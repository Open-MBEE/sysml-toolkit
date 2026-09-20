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

/// The session fingerprint, the package, and the actions planned for it.
type SplitCache = (Vec<(String, i32)>, ElementRef, Vec<(String, WorkspaceEdit)>);

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
    /// path — computed once per Nav from the library *texts* (a
    /// syntax-tier parse; no model build), since structure is syntactic.
    /// Feeds both the flat completion list (packages + direct members)
    /// and the qualifier-filtered import/member completions.
    library_symbols: Option<Vec<QualifiedSymbol>>,
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
    /// Qualified symbols of the seeded workspace units, parsed once per
    /// seed (the [`Self::library_symbols`] pattern) — import fixes and
    /// completions must see the whole workspace, not just what happens
    /// to be open, without a per-keystroke full-workspace parse. Units
    /// shadowed by an open document are filtered at query time.
    workspace_seed_symbols: Option<Vec<QualifiedSymbol>>,
    session: Option<Session>,
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
            root: None,
            workspace: None,
            workspace_seed_symbols: None,
            session: None,
            fingerprint: Vec::new(),
            verify: None,
            lint: None,
            split_cache: None,
            hide_redundant_value_hints: true,
            snippet_completions: false,
            infer_unit_types: true,
            completion_session: None,
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
    pub fn set_workspace_sources(&mut self, units: Arc<Vec<(String, String)>>) {
        self.workspace = Some(units);
        self.workspace_seed_symbols = None;
        self.invalidate();
    }

    /// Drop the cached session (after a rename commit mutated it, the
    /// client must re-sync before answers are trustworthy again).
    pub fn invalidate(&mut self) {
        self.session = None;
        self.fingerprint.clear();
        self.verify = None;
        self.lint = None;
        self.split_cache = None;
        self.completion_session = None;
    }

    /// Completions for a feature-chain step (`tank.|`, `tank.liq|`,
    /// `a.b.|`): the members the step could reach. The chain resolves
    /// the way the evaluator resolves chains — the head from the
    /// innermost enclosing declaration outward (inherited members
    /// included, via [`ResolvedModel::member_of`]), later segments as
    /// members of the segment before them — and enumeration walks the
    /// reached feature's own body, its declared types, and their
    /// explicit specialization closure, nearest declaration winning a
    /// name. `None` when the prefix does not resolve or reaches
    /// something memberless: the caller falls back to the
    /// position-blind list.
    ///
    /// [`ResolvedModel::member_of`]: sysmlv2_parser::json::ResolvedModel::member_of
    fn chain_member_completions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        enc: Encoding,
        snippets: bool,
    ) -> Option<Vec<lsp_types::CompletionItem>> {
        // The statement being typed, cut for the session build (its
        // parse error would refuse the whole session): statement start
        // to the end of the cursor's line.
        let text = &docs.get(uri)?.text;
        let line_end = text[(cx.offset as usize).min(text.len())..]
            .find('\n')
            .map(|i| cx.offset + offset32(i))
            .unwrap_or(offset32(text.len()));
        let session = self.completion_session(docs, uri, Span::new(cx.stmt_start, line_end))?;
        let unit = Self::unit_of_static(uri, session)?;
        let resolved = session.resolved();
        // The declarations enclosing the statement, innermost first:
        // the scopes the chain head resolves from. Queried at the
        // statement's start — the same scopes as the cursor, at an
        // offset the cut cannot have shifted.
        let at = cx.stmt_start;
        let mut enclosing: Vec<(ElementRef, u32)> = resolved
            .user_elements()
            .filter_map(|e| {
                let (u, span) = resolved.member_extent(e)?;
                (u == unit && span.start <= at && at <= span.end).then(|| (e, span.len()))
            })
            .collect();
        enclosing.sort_by_key(|&(_, len)| len);
        let qn = |name: &str| sysmlv2_parser::ast::QualifiedName {
            is_global: false,
            segments: vec![sysmlv2_parser::ast::Name {
                value: name.to_string(),
                span: Span::new(0, 0),
            }],
            span: Span::new(0, 0),
        };
        let root = resolved.root_scope();
        let head = qn(&cx.dot_chain[0]);
        let mut cur = enclosing
            .iter()
            .find_map(|&(e, _)| resolved.member_of(e, &head).map(|(hit, _)| hit))
            .or_else(|| resolved.resolve_in(root, &head))?;
        for seg in &cx.dot_chain[1..] {
            cur = resolved.member_of(cur, &qn(seg))?.0;
        }
        // Enumerate: own body first, then declared types and their
        // specialization closure (breadth-first, so the nearest
        // declaration of a name shadows farther ones).
        let mut members: Vec<(String, ElementRef)> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut visited = std::collections::HashSet::new();
        let mut frontier = std::collections::VecDeque::from([cur]);
        while let Some(scope_el) = frontier.pop_front() {
            if !visited.insert(scope_el) {
                continue;
            }
            for m in resolved.owned_features(scope_el) {
                if let Some(n) = resolved.element_name(m) {
                    if seen.insert(n.to_string()) {
                        members.push((n.to_string(), m));
                    }
                }
            }
            for t in resolved.typings(scope_el) {
                frontier.push_back(t);
            }
            for s in resolved.explicit_supertypes(scope_el) {
                frontier.push_back(s);
            }
        }
        if members.is_empty() {
            return None;
        }
        // Kind + detail while the session borrow lasts; items after.
        let details: Vec<(String, lsp_types::CompletionItemKind, Option<String>)> = members
            .into_iter()
            .map(|(n, m)| {
                let kind = member_kind(resolved.element_type(m));
                let detail = resolved.element_qualified_name(m);
                (n, kind, detail)
            })
            .collect();
        let d = docs.get(uri)?;
        let mapper = Mapper::new(&d.text, enc);
        Some(
            details
                .into_iter()
                .map(|(name, kind, detail)| {
                    let (text_edit, repair, insert_text_format) = item_edits(
                        &d.text,
                        &mapper,
                        cx,
                        crate::dialect_of(uri),
                        &name,
                        snippets,
                    );
                    lsp_types::CompletionItem {
                        label: crate::outline::spell_name(&name),
                        kind: Some(kind),
                        detail,
                        text_edit,
                        additional_text_edits: repair.map(|e| vec![e]),
                        insert_text_format,
                        ..Default::default()
                    }
                })
                .collect(),
        )
    }

    /// The session over the current open documents, rebuilding if any
    /// version moved. `None` when a document fails to build a session
    /// (never expected — sessions tolerate parse errors — but a broken
    /// library directory reports here).
    fn session(&mut self, docs: &BTreeMap<Uri, Document>) -> Option<&mut Session> {
        let mut fp: Vec<(String, i32)> = docs
            .iter()
            .map(|(u, d)| (u.to_string(), d.version))
            .collect();
        fp.sort();
        if self.session.is_none() || fp != self.fingerprint {
            let sources = self.assemble_sources(docs, &fp);
            let session = self.build_session(sources)?;
            self.session = Some(session);
            self.fingerprint = fp;
            self.verify = None;
            self.lint = None;
            self.split_cache = None;
        }
        self.session.as_mut()
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
    /// already shows those errors. A library that cannot be read is not
    /// ordinary and is recorded for the client: without it every
    /// model-backed answer here is silently empty.
    fn build_session(&mut self, sources: Vec<(String, String)>) -> Option<Session> {
        let mut session = match Session::from_sources(sources) {
            Ok(session) => session,
            Err(e) => {
                self.note_failure(&e, false);
                return None;
            }
        };
        if let Some(lib) = &self.library {
            if let Err(e) = session.load_library_from(lib.clone()) {
                self.note_failure(&e, true);
                return None;
            }
        }
        Some(session)
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

    /// The completion tier's session: [`Self::assemble_sources`] with
    /// `cut` (the statement being typed, in `uri`) removed outright —
    /// a mid-statement cursor nearly always means a parse error, which
    /// sessions refuse, and the statement itself contributes nothing a
    /// member listing needs. The reduced text is identical for every
    /// keystroke inside the statement, so the cache (keyed by a hash
    /// of the reduced sources) rebuilds only when something *outside*
    /// the statement changes. Position queries against this session
    /// must use offsets at or before `cut.start` — later spans shifted.
    /// `None` when the rest of the workspace does not parse either.
    fn completion_session(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cut: Span,
    ) -> Option<&mut Session> {
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
        let key = hasher.finish();
        if self.completion_session.as_ref().map(|(k, _)| *k) != Some(key) {
            let session = self.build_session(sources)?;
            self.completion_session = Some((key, session));
        }
        self.completion_session.as_mut().map(|(_, s)| s)
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
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let (target, _) = Self::element_at(session, unit, offset)?;
        let (dunit, dspan) = session.resolved().declaration_site(target)?;
        Self::location_static(session, dunit, dspan, enc)
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
        let session = self.session(docs)?;
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
        // `→`. Types render exactly as the declaration spells them
        // (`:>` subsetting included), so the reader sees the author's
        // qualification. The fence is tagged `sysml-signature` — the
        // notation is not SysML source, so clients colorize it with a
        // dedicated signature grammar (plain monospace where none is
        // registered).
        let parts = def_signature(resolved, target, metaclass);
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
        let (_, _, src) = session.units().find(|(i, _, _)| *i == unit)?;
        let mapper = Mapper::new(src, enc);
        Some((text, mapper.range(span)))
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

    /// The standard library's qualified symbol table, built once per Nav
    /// from a syntax-tier parse of the library texts. Model-free by
    /// design: structure is syntactic, and this must not add a
    /// per-keystroke model build.
    fn library_symbols(&mut self) -> &[QualifiedSymbol] {
        if self.library_symbols.is_none() {
            let mut symbols: Vec<QualifiedSymbol> = Vec::new();
            if let Some(lib) = &self.library {
                for (name, text) in Self::library_sources(lib) {
                    let parse = if crate::is_kerml(name.as_str()) {
                        sysmlv2_parser::parser::parse_kerml_source(&text)
                    } else {
                        sysmlv2_parser::parser::parse_source(&text)
                    };
                    let mapper = Mapper::new(&text, Encoding::Utf8);
                    let roots = crate::document_symbols(&parse.unit, &text, &mapper);
                    let bodies = crate::outline::doc_bodies(&parse.unit, &mapper);
                    let shorts = crate::outline::short_names(&parse.unit, &mapper);
                    collect_qualified(&roots, "", 0, true, None, &bodies, &shorts, &mut symbols);
                }
            }
            self.library_symbols = Some(symbols);
        }
        self.library_symbols.as_deref().unwrap_or(&[])
    }

    /// Workspace symbols across BOTH tiers: fresh parses of the open
    /// documents, plus the cached seed scan for every seeded unit that
    /// is not open (an open document's live text shadows its seed
    /// copy). Everything that offers or auto-inserts an import must use
    /// this — the open-documents map alone hides most of the workspace.
    fn all_workspace_symbols(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        enc: Encoding,
    ) -> Vec<QualifiedSymbol> {
        let mut out = workspace_symbols(docs, enc);
        if self.workspace_seed_symbols.is_none() {
            if let Some(units) = &self.workspace {
                let mut symbols: Vec<QualifiedSymbol> = Vec::new();
                for (name, text) in units.iter() {
                    let parse = if crate::is_kerml(name) {
                        sysmlv2_parser::parser::parse_kerml_source(text)
                    } else {
                        sysmlv2_parser::parser::parse_source(text)
                    };
                    let mapper = Mapper::new(text, enc);
                    let roots = crate::document_symbols(&parse.unit, text, &mapper);
                    let bodies = crate::outline::doc_bodies(&parse.unit, &mapper);
                    let shorts = crate::outline::short_names(&parse.unit, &mapper);
                    collect_qualified(
                        &roots,
                        "",
                        0,
                        true,
                        Some(name.as_str()),
                        &bodies,
                        &shorts,
                        &mut symbols,
                    );
                }
                self.workspace_seed_symbols = Some(symbols);
            }
        }
        if let Some(seed) = &self.workspace_seed_symbols {
            let open: std::collections::HashSet<String> =
                docs.keys().map(|u| u.to_string()).collect();
            out.extend(
                seed.iter()
                    .filter(|s| s.site.as_ref().is_none_or(|(u, _)| !open.contains(u)))
                    .cloned(),
            );
        }
        out
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
        let auto = crate::autoimport::AutoImport::new(
            text,
            &parse.unit,
            offset,
            Span::new(offset, offset + token_len),
        );
        let mapper = Mapper::new(text, enc);
        let ws = self.all_workspace_symbols(docs, enc);
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        for s in ws.iter().chain(self.library_symbols()) {
            if out.len() >= 5 {
                break;
            }
            if s.name != name || s.depth == 0 || !s.importable || !seen.insert(s.qualified.clone())
            {
                continue;
            }
            let Some((at, new_text)) = auto.import_edit(&s.name, &s.qualified) else {
                continue;
            };
            out.push((
                format!(
                    "Add import {}",
                    crate::autoimport::escape_qualified(crate::dialect_of(uri), &s.qualified)
                ),
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
    /// `meta` pairs each item index with the symbol's (name,
    /// qualified) it was built from.
    fn append_unit_type_edits(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
        (cx, tcx): (&CompletionCx, &UnitTypeCx),
        meta: &[(usize, String, String)],
        out: &mut [lsp_types::CompletionItem],
    ) {
        let Some(doc) = docs.get(uri) else { return };
        let text = &doc.text;
        let at_cursor = (cx.offset as usize).min(text.len());
        let line_end = text[at_cursor..]
            .find('\n')
            .map(|i| at_cursor + i)
            .unwrap_or(text.len());
        // Anything after the cursor other than the closing bracket
        // means the accepted name is only a factor of a larger unit
        // expression — its type says nothing about the whole.
        let rest = text[at_cursor..line_end].trim_start();
        if !(rest.is_empty() || rest.starts_with(']')) {
            return;
        }
        let mapper = Mapper::new(text, enc);
        let insert_at = mapper.range(Span::new(tcx.name_end, tcx.name_end));
        let Some(session) =
            self.completion_session(docs, uri, Span::new(cx.stmt_start, offset32(line_end)))
        else {
            return;
        };
        let Some(unit) = Self::unit_of_static(uri, session) else {
            return;
        };
        let resolved = session.resolved();
        // The declaration's resolution scope: the innermost enclosing
        // declaration's body, the root namespace as the fallback.
        let at = cx.stmt_start;
        let mut enclosing: Vec<(ElementRef, u32)> = resolved
            .user_elements()
            .filter_map(|e| {
                let (u, span) = resolved.member_extent(e)?;
                (u == unit && span.start <= at && at <= span.end).then(|| (e, span.len()))
            })
            .collect();
        enclosing.sort_by_key(|&(_, len)| len);
        let scope = enclosing
            .iter()
            .find_map(|&(e, _)| resolved.element_scope(e))
            .unwrap_or_else(|| resolved.root_scope());
        for (idx, name, qualified) in meta {
            let range =
                crate::autoimport::replace_range_for(text, cx.partial_start, cx.offset, name);
            let interior = text
                .get(tcx.bracket_open as usize + 1..range.start as usize)
                .map(str::trim);
            if interior != Some("") {
                continue;
            }
            let Some(elem) = resolved.resolve_qualified(qualified) else {
                continue;
            };
            let mut types: Vec<ElementRef> = Vec::new();
            for def in resolved.typings(elem) {
                for t in resolved.quantity_types_for_unit_def(def) {
                    if !types.contains(&t) {
                        types.push(t);
                    }
                }
            }
            let [target] = types[..] else { continue };
            let dialect = Some(crate::dialect_of(uri));
            let Some(spelling) = resolved.type_spelling_at(dialect, scope, target) else {
                continue;
            };
            out[*idx]
                .additional_text_edits
                .get_or_insert_with(Vec::new)
                .push(TextEdit {
                    range: insert_at,
                    new_text: format!(" : {spelling}"),
                });
        }
    }

    /// Completion. Position-aware where it matters:
    /// - after a qualifier (`Foo::`), only the members of `Foo`
    ///   (workspace and library), matched by qualified-path suffix;
    /// - inside an `import` statement's path, symbols at any depth are
    ///   offered by simple name and accepting one inserts its full
    ///   qualified path over the typed partial word (a `textEdit`), so
    ///   the import actually resolves;
    /// - everywhere else, the position-blind list: keyword
    ///   vocabulary + workspace names + library packages and their
    ///   direct members.
    pub fn completions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: Option<u32>,
        enc: Encoding,
    ) -> Vec<lsp_types::CompletionItem> {
        use lsp_types::{CompletionItem, CompletionItemKind};
        // Copied out: the symbol iterators below hold `self` borrows.
        let snippets = self.snippet_completions;
        let cx = offset.and_then(|o| docs.get(uri).map(|d| completion_context(&d.text, o)));
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

        // Feature-chain context (`tank.` / `tank.liq`): the members the
        // chain step could actually reach, from the semantic session. A
        // prefix the session cannot resolve falls through to the
        // position-blind list below.
        if let Some(cx) = cx.as_ref().filter(|cx| !cx.dot_chain.is_empty()) {
            if let Some(items) = self.chain_member_completions(docs, uri, cx, enc, snippets) {
                return items;
            }
        }

        // Qualifier context: members of the qualified namespace only.
        if let Some(cx) = cx.as_ref().filter(|cx| !cx.qualifier.is_empty()) {
            let path = cx.qualifier.join("::");
            let quoting = docs.get(uri).map(|d| (Mapper::new(&d.text, enc), &d.text));
            let mut out: Vec<CompletionItem> = Vec::new();
            let mut meta: Vec<(usize, String, String)> = Vec::new();
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            let ws = self.all_workspace_symbols(docs, enc);
            for s in ws.iter().chain(self.library_symbols()) {
                if is_phantom(s) {
                    continue;
                }
                if s.is_member_of(&path) && seen.insert(s.name.clone()) {
                    let (text_edit, repair, insert_text_format) = match &quoting {
                        Some((mapper, text)) => {
                            item_edits(text, mapper, cx, crate::dialect_of(uri), &s.name, snippets)
                        }
                        None => (None, None, None),
                    };
                    meta.push((out.len(), s.name.clone(), s.qualified.clone()));
                    out.push(CompletionItem {
                        label: crate::outline::spell_name(&s.name),
                        kind: Some(s.kind),
                        detail: Some(s.qualified.clone()),
                        documentation: s.documentation(),
                        text_edit,
                        additional_text_edits: repair.map(|e| vec![e]),
                        insert_text_format,
                        ..Default::default()
                    });
                }
            }
            if let Some(tcx) = unit_type_cx.as_ref() {
                self.append_unit_type_edits(docs, uri, enc, (cx, tcx), &meta, &mut out);
            }
            return out;
        }

        // Import context: everything importable, inserted as its full
        // qualified path so the reference resolves from the root.
        if let (Some(cx), Some(doc)) = (cx.as_ref().filter(|cx| cx.import), docs.get(uri)) {
            let mapper = Mapper::new(&doc.text, enc);
            let replace = mapper.range(Span::new(cx.partial_start, cx.offset));
            // Statement repairs (the import statement's own `;`) —
            // identical for every item: the replace range is the
            // partial word regardless of candidate.
            let repairs = crate::autofix::statement_repairs(
                &doc.text,
                cx.stmt_start,
                cx.partial_start,
                cx.offset,
            );
            let (suffix, repair) = match repairs {
                Some(r) => (
                    r.suffix,
                    r.insert.map(|(at, fix)| TextEdit {
                        range: mapper.range(Span::new(at, at)),
                        new_text: fix,
                    }),
                ),
                None => (String::new(), None),
            };
            // The repair suffix rides every item's main edit the same
            // way — snippet-stop the cursor ahead of it where the
            // client allows (see `item_edits`).
            let snippet = snippets && !suffix.is_empty();
            let mut out: Vec<CompletionItem> = Vec::new();
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            let ws = self.all_workspace_symbols(docs, enc);
            for s in ws.iter().chain(self.library_symbols()) {
                // Depth cap: packages, their members, and one level
                // below — deeper targets are reached by typing the
                // qualifier (the branch above). Keeps the unfiltered
                // import list from carrying the whole stdlib tree.
                if is_phantom(s) || s.depth > 2 || !seen.insert(s.qualified.clone()) {
                    continue;
                }
                let qualified =
                    crate::autoimport::escape_qualified(crate::dialect_of(uri), &s.qualified);
                out.push(CompletionItem {
                    label: crate::outline::spell_name(&s.name),
                    kind: Some(s.kind),
                    detail: Some(if s.depth == 0 {
                        "standard library".to_string()
                    } else {
                        s.qualified.clone()
                    }),
                    documentation: s.documentation(),
                    text_edit: Some(lsp_types::CompletionTextEdit::Edit(TextEdit {
                        range: replace,
                        new_text: if snippet {
                            format!("{}$0{suffix}", snippet_escape(&qualified))
                        } else {
                            format!("{qualified}{suffix}")
                        },
                    })),
                    additional_text_edits: repair.clone().map(|e| vec![e]),
                    insert_text_format: snippet.then_some(lsp_types::InsertTextFormat::SNIPPET),
                    ..Default::default()
                });
            }
            return out;
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
        let auto = match (cx.as_ref(), parsed.as_ref().zip(doc)) {
            (Some(cx), Some((p, d))) => Some(crate::autoimport::AutoImport::new(
                &d.text,
                &p.unit,
                cx.offset,
                Span::new(cx.partial_start, cx.offset),
            )),
            _ => None,
        };
        let mapper = doc.map(|d| Mapper::new(&d.text, enc));
        // The import edit + source annotation for a symbol offered by
        // simple name, `None` when accepting it needs no import.
        let import_extras = |s: &QualifiedSymbol| {
            let (auto, mapper) = auto.as_ref().zip(mapper.as_ref())?;
            if s.depth == 0 || !s.importable {
                return None;
            }
            let (at, new_text) = auto.import_edit(&s.name, &s.qualified)?;
            let parent = s
                .qualified
                .strip_suffix(s.name.as_str())?
                .strip_suffix("::")?;
            Some((
                vec![TextEdit {
                    range: mapper.range(Span::new(at, at)),
                    new_text,
                }],
                lsp_types::CompletionItemLabelDetails {
                    detail: None,
                    description: Some(format!("import {parent}")),
                },
            ))
        };
        // Restricted names insert quoted, replacing the typed spelling.
        // The main edit (quoting + repair suffix) and the repair
        // insertion, per item; merged with the import edit below.
        let edits_for = |s: &QualifiedSymbol| match cx.as_ref().zip(mapper.as_ref().zip(doc)) {
            Some((cx, (mapper, d))) => item_edits(
                &d.text,
                mapper,
                cx,
                crate::dialect_of(uri),
                &s.name,
                snippets,
            ),
            None => (None, None, None),
        };
        let assemble = |s: &QualifiedSymbol| {
            let (text_edit, repair, insert_text_format) = edits_for(s);
            let (import_edits, label_details) = match import_extras(s) {
                Some((e, d)) => (Some(e), Some(d)),
                None => (None, None),
            };
            let additional: Vec<TextEdit> =
                import_edits.into_iter().flatten().chain(repair).collect();
            (
                text_edit,
                (!additional.is_empty()).then_some(additional),
                label_details,
                insert_text_format,
            )
        };
        let mut out: Vec<CompletionItem> = crate::tokens::VOCABULARY
            .iter()
            .map(|kw| CompletionItem {
                label: kw.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                ..Default::default()
            })
            .collect();
        let mut meta: Vec<(usize, String, String)> = Vec::new();
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        for s in &self.all_workspace_symbols(docs, enc) {
            if seen.insert(s.name.clone()) {
                let (text_edit, additional_text_edits, label_details, insert_text_format) =
                    assemble(s);
                meta.push((out.len(), s.name.clone(), s.qualified.clone()));
                out.push(CompletionItem {
                    label: crate::outline::spell_name(&s.name),
                    kind: Some(s.kind),
                    detail: (!s.qualified.eq(&s.name)).then(|| s.qualified.clone()),
                    documentation: s.documentation(),
                    text_edit,
                    additional_text_edits,
                    label_details,
                    insert_text_format,
                    ..Default::default()
                });
            }
        }
        // Standard-library names last: workspace names shadow them. Kept
        // to packages + direct members — the full table would flood the
        // unfiltered list.
        for s in self.library_symbols() {
            if s.depth > 1 || !seen.insert(s.name.clone()) {
                continue;
            }
            let (text_edit, additional_text_edits, label_details, insert_text_format) = assemble(s);
            meta.push((out.len(), s.name.clone(), s.qualified.clone()));
            out.push(CompletionItem {
                label: crate::outline::spell_name(&s.name),
                kind: Some(s.kind),
                detail: Some(if s.depth == 0 {
                    "standard library".to_string()
                } else {
                    s.qualified.clone()
                }),
                documentation: s.documentation(),
                text_edit,
                additional_text_edits,
                label_details,
                insert_text_format,
                ..Default::default()
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
/// `workspace/symbol`.
pub fn flatten_symbols(
    symbols: &[lsp_types::DocumentSymbol],
    uri: &Uri,
    query: &str,
    out: &mut Vec<lsp_types::SymbolInformation>,
) {
    for s in symbols {
        if query.is_empty() || s.name.to_lowercase().contains(&query.to_lowercase()) {
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
            flatten_symbols(children, uri, query, out);
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

/// A named symbol with its `::`-qualified path, flattened from an
/// outline tree. `depth` counts nesting from the unit root (0 = a
/// top-level package). Workspace symbols carry their declaration site
/// (`uri` + name span) so completion can drop the phantom symbol the
/// half-typed statement itself declares — `private import Real` parses
/// as a member named `Real`, and offering it back (qualified into its
/// accidental owner) would outrank the real target.
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
}

impl QualifiedSymbol {
    /// The symbol's doc body as completion-item documentation.
    fn documentation(&self) -> Option<lsp_types::Documentation> {
        self.doc.as_ref().map(|d| {
            lsp_types::Documentation::MarkupContent(lsp_types::MarkupContent {
                kind: lsp_types::MarkupKind::Markdown,
                value: d.clone(),
            })
        })
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
        parent == path || parent.ends_with(&format!("::{path}"))
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
        SymbolKind::KEY => CompletionItemKind::KEYWORD,
        SymbolKind::OBJECT | SymbolKind::STRING => CompletionItemKind::VALUE,
        _ => CompletionItemKind::VARIABLE,
    }
}

/// Flatten an outline tree into qualified symbols. Anonymous
/// (`«keyword»`) members have no referenceable name — their subtrees
/// are skipped, since a qualified path through them would not resolve.
#[allow(clippy::too_many_arguments)] // one recursive walk, one context set
fn collect_qualified(
    nodes: &[lsp_types::DocumentSymbol],
    prefix: &str,
    depth: usize,
    in_packages: bool,
    uri: Option<&str>,
    docs: &HashMap<lsp_types::Position, String>,
    shorts: &HashMap<lsp_types::Position, String>,
    out: &mut Vec<QualifiedSymbol>,
) {
    for s in nodes {
        if s.name.starts_with('«') {
            continue;
        }
        let qualified = if prefix.is_empty() {
            s.name.clone()
        } else {
            format!("{prefix}::{}", s.name)
        };
        out.push(QualifiedSymbol {
            name: s.name.clone(),
            qualified: qualified.clone(),
            kind: completion_kind(s.kind),
            depth,
            importable: in_packages,
            site: uri.map(|u| (u.to_string(), s.selection_range)),
            doc: docs.get(&s.selection_range.start).cloned(),
        });
        // A short symbol (`<'m/s²'>`) alongside the regular name is its
        // own referenceable spelling — its own entry, same everything
        // else. Nothing nests under it: children path through the
        // regular name.
        if let Some(short) = shorts.get(&s.selection_range.start) {
            out.push(QualifiedSymbol {
                name: short.clone(),
                qualified: if prefix.is_empty() {
                    short.clone()
                } else {
                    format!("{prefix}::{short}")
                },
                kind: completion_kind(s.kind),
                depth,
                importable: in_packages,
                site: uri.map(|u| (u.to_string(), s.selection_range)),
                doc: docs.get(&s.selection_range.start).cloned(),
            });
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
                out,
            );
        }
    }
}

/// Every open document's outline, flattened to qualified symbols.
fn workspace_symbols(docs: &BTreeMap<Uri, Document>, enc: Encoding) -> Vec<QualifiedSymbol> {
    let mut out = Vec::new();
    for (uri, doc) in docs {
        let parse = if crate::is_kerml(uri.path().as_str()) {
            sysmlv2_parser::parser::parse_kerml_source(&doc.text)
        } else {
            sysmlv2_parser::parser::parse_source(&doc.text)
        };
        let mapper = Mapper::new(&doc.text, enc);
        let roots = crate::document_symbols(&parse.unit, &doc.text, &mapper);
        let bodies = crate::outline::doc_bodies(&parse.unit, &mapper);
        let shorts = crate::outline::short_names(&parse.unit, &mapper);
        collect_qualified(
            &roots,
            "",
            0,
            true,
            Some(uri.to_string().as_str()),
            &bodies,
            &shorts,
            &mut out,
        );
    }
    out
}

/// What the cursor is completing: the partial word being typed, the
/// `::`-chained qualifier before it, and whether the enclosing
/// statement (back to the previous `;`/`{`/`}`) is an `import`.
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
    pub import: bool,
    /// Statement start (after the previous `;`/`{`/`}`) — the autofix
    /// tier's scan anchor.
    pub stmt_start: u32,
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

/// Detect [`UnitTypeCx`] textually on the live document — the
/// statement being typed rarely parses, so the model cannot answer.
/// Conservative: any `:` between the name and the `=` (typing,
/// subsetting, redefinition) bails, as does a cursor not inside an
/// open `[`.
pub(crate) fn untyped_attribute_unit_context(text: &str, cx: &CompletionCx) -> Option<UnitTypeCx> {
    let seg = text.get(cx.stmt_start as usize..cx.partial_start as usize)?;
    let bytes = seg.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    // `attribute` as its own word.
    let kw = "attribute";
    let mut from = 0;
    let kw_end = loop {
        let at = from + seg[from..].find(kw)?;
        let end = at + kw.len();
        let before_ok = at == 0 || !is_word(bytes[at - 1]);
        let after_ok = end >= seg.len() || !is_word(bytes[end]);
        if before_ok && after_ok {
            break end;
        }
        from = end;
    };
    let skip_ws = |mut p: usize| {
        while p < bytes.len() && bytes[p].is_ascii_whitespace() {
            p += 1;
        }
        p
    };
    let mut p = skip_ws(kw_end);
    // Optional short-name group `<...>`.
    if bytes.get(p) == Some(&b'<') {
        p = p + seg[p..].find('>')? + 1;
        p = skip_ws(p);
    }
    // The declared name: an identifier or a quoted name.
    let name_start = p;
    if bytes.get(p) == Some(&b'\'') {
        p = p + 1 + seg[p + 1..].find('\'')? + 2;
    } else {
        while p < bytes.len() && is_word(bytes[p]) {
            p += 1;
        }
    }
    if p == name_start {
        return None;
    }
    let name_end = p;
    // Between the name and the `=`: whitespace and at most a
    // multiplicity group — any `:` means the declaration is typed.
    let eq = name_end + seg[name_end..].find('=')?;
    if seg[name_end..eq].contains(':') {
        return None;
    }
    // The cursor must sit inside an open quantity bracket of the value.
    let mut open: Option<usize> = None;
    let mut depth = 0i32;
    for (j, b) in seg.bytes().enumerate().skip(eq) {
        match b {
            b'[' => {
                depth += 1;
                open = Some(j);
            }
            b']' => {
                depth -= 1;
                if depth <= 0 {
                    open = None;
                }
            }
            _ => {}
        }
    }
    let bracket_open = open?;
    Some(UnitTypeCx {
        name_end: cx.stmt_start + offset32(name_end),
        bracket_open: cx.stmt_start + offset32(bracket_open),
    })
}

/// A doc/comment body as hover Markdown — the model's shared
/// normalization (gutters stripped, blank edges trimmed).
pub(crate) fn doc_markdown(body: &str) -> String {
    sysmlv2_parser::json::doc_display_text(body)
}

/// A parameter's (or return's) type references: the written
/// specialization clauses of its declaration (typing, subsetting,
/// redefinition — the qualified name spans as the author spelled
/// them), plus resolved simple names as the fallback for declarations
/// with nothing spelled (interchange-lifted units).
struct SigTypes {
    refs: Vec<(usize, Span)>,
    fallback: Vec<String>,
}

/// One rendered-signature parameter: direction prefix (`in` is implied
/// and empty), name, types.
struct SigParam {
    prefix: String,
    name: String,
    types: SigTypes,
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

/// The type references of a feature's declaration, spelled clauses
/// first (see [`SigTypes`]).
fn spelled_types(resolved: &mut sysmlv2_parser::json::ResolvedModel, e: ElementRef) -> SigTypes {
    let refs = resolved.specialization_spans(e);
    let fallback = if refs.is_empty() {
        let mut targets = resolved.typings(e);
        if targets.is_empty() {
            targets = resolved.explicit_supertypes(e);
        }
        targets
            .into_iter()
            .filter_map(|t| resolved.element_name(t).map(str::to_string))
            .collect()
    } else {
        Vec::new()
    };
    SigTypes { refs, fallback }
}

/// Assemble the signature line, slicing each type's written spelling
/// out of its unit's source.
fn render_signature(parts: SigParts, session: &Session) -> String {
    let types = |t: &SigTypes| -> Vec<String> {
        let spelled: Vec<String> = t
            .refs
            .iter()
            .filter_map(|(unit, span)| {
                let (_, _, src) = session.units().find(|(i, _, _)| i == unit)?;
                src.get(span.start as usize..span.end as usize)
                    .map(|s| s.trim().to_string())
            })
            .filter(|s| !s.is_empty())
            .collect();
        if spelled.is_empty() {
            t.fallback.clone()
        } else {
            spelled
        }
    };
    let params: Vec<String> = parts
        .params
        .iter()
        .map(|p| {
            let ts = types(&p.types);
            if ts.is_empty() {
                format!("{}{}", p.prefix, p.name)
            } else {
                format!("{}{}: {}", p.prefix, p.name, ts.join(", "))
            }
        })
        .collect();
    let ret = parts
        .ret
        .as_ref()
        .map(&types)
        .filter(|ts| !ts.is_empty())
        .map(|ts| ts.join(", "))
        .or(parts.ret_name);
    let ret = ret.map(|r| format!(" → {r}")).unwrap_or_default();
    format!("{}({}){ret}", parts.name, params.join(", "))
}

/// A callable's function signature —
/// `calculateDeltaV(isp: specificImpulse, g0: ISQ::acceleration) →
/// ISQ::speed` — from its directed parameters and return parameter,
/// for every metaclass an invocation expression can call: the SysML
/// calc/constraint/action definitions AND usages (a package-level
/// `calc <ln> naturalLogarithm { … }` is a CalculationUsage), and the
/// KerML behavioral classifiers (`function`, `predicate`, `behavior`).
/// `in` is the implied direction and stays silent; `out`/`inout` are
/// spelled. `None` for other metaclasses and for callables declaring
/// no parameters (the bare card already says everything).
fn def_signature(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    target: ElementRef,
    metaclass: &str,
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
    let ret = resolved.calc_return_param(target);
    let params: Vec<ElementRef> = resolved
        .owned_features(target)
        .into_iter()
        .filter(|p| Some(*p) != ret && resolved.declared_direction(*p).is_some())
        .collect();
    if params.is_empty() && ret.is_none() {
        return None;
    }
    let name = resolved
        .element_name(target)
        .unwrap_or("<anonymous>")
        .to_string();
    let params: Vec<SigParam> = params
        .into_iter()
        .map(|p| SigParam {
            prefix: match resolved.declared_direction(p) {
                Some("in") | None => String::new(),
                Some(dir) => format!("{dir} "),
            },
            name: resolved.element_name(p).unwrap_or("_").to_string(),
            types: spelled_types(resolved, p),
        })
        .collect();
    Some(SigParts {
        name,
        ret: ret.map(|r| spelled_types(resolved, r)),
        ret_name: ret.and_then(|r| resolved.element_name(r).map(str::to_string)),
        params,
    })
}

/// The edits accepting `name` should perform, beyond inserting the
/// label: restricted names insert quoted (`'m/s²'` — the raw label
/// would parse as an expression) over the typed spelling (see
/// [`crate::autoimport::replace_range_for`]), and the autofix tier's
/// statement repairs ride along — the suffix on the main edit, the
/// rest as a separate insertion past the cursor. When a repair suffix
/// rides the main edit and the client takes snippets, the edit
/// carries a `$0` stop between name and suffix: the cursor belongs
/// where typing continues, before the auto-inserted `];`, not after
/// it. `(None, None, None)` for a basic name needing no repairs:
/// plain label insertion is right and keeps the item light.
fn item_edits(
    text: &str,
    mapper: &Mapper<'_>,
    cx: &CompletionCx,
    dialect: sysmlv2_parser::ast::Dialect,
    name: &str,
    snippets: bool,
) -> (
    Option<lsp_types::CompletionTextEdit>,
    Option<TextEdit>,
    Option<lsp_types::InsertTextFormat>,
) {
    // Insert text is source for this document: a name the dialect
    // reserves (`'view'`) and a non-basic name are quoted, a word the
    // dialect does not reserve stays bare — the label keeps the raw name.
    let escaped = sysmlv2_parser::name::spell_name_in(Some(dialect), name);
    let range = crate::autoimport::replace_range_for(text, cx.partial_start, cx.offset, name);
    let repairs = crate::autofix::statement_repairs(text, cx.stmt_start, range.start, cx.offset);
    let (suffix, insert) = match repairs {
        Some(r) => (r.suffix, r.insert),
        None => (String::new(), None),
    };
    let snippet = snippets && !suffix.is_empty();
    let text_edit = (escaped != name || !suffix.is_empty()).then(|| {
        lsp_types::CompletionTextEdit::Edit(TextEdit {
            range: mapper.range(range),
            new_text: if snippet {
                format!("{}$0{suffix}", snippet_escape(&escaped))
            } else {
                format!("{escaped}{suffix}")
            },
        })
    });
    let extra = insert.map(|(at, fix)| TextEdit {
        range: mapper.range(Span::new(at, at)),
        new_text: fix,
    });
    (
        text_edit,
        extra,
        snippet.then_some(lsp_types::InsertTextFormat::SNIPPET),
    )
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

/// A completion's literal text made safe for snippet-format delivery:
/// `$`, `}`, and `\` are snippet syntax and must arrive escaped.
fn snippet_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if matches!(c, '$' | '}' | '\\') {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

pub(crate) fn completion_context(text: &str, offset: u32) -> CompletionCx {
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
    let stmt_start = text[..j].rfind([';', '{', '}']).map(|k| k + 1).unwrap_or(0);
    let import = text[stmt_start..j]
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .any(|w| w == "import");
    CompletionCx {
        qualifier,
        dot_chain,
        partial_start: offset32(partial_start),
        offset: offset32(offset),
        import,
        stmt_start: offset32(stmt_start),
    }
}

#[cfg(test)]
mod context_tests {
    use super::completion_context;

    #[test]
    fn qualifier_and_import_detection() {
        let text = "package P { private import ScalarFunctions:: }";
        let cx = completion_context(text, 44);
        assert_eq!(cx.qualifier, vec!["ScalarFunctions"]);
        assert!(cx.import);

        let text = "package P { private import Real }";
        let cx = completion_context(text, 31);
        assert!(cx.qualifier.is_empty());
        assert!(cx.import);
        assert_eq!(&text[cx.partial_start as usize..cx.offset as usize], "Real");

        let text = "package P { part x : ISQ::Torque }";
        let cx = completion_context(text, 32);
        assert_eq!(cx.qualifier, vec!["ISQ"]);
        assert!(!cx.import);

        let text = "package P { import A::B:: }";
        let cx = completion_context(text, 25);
        assert_eq!(cx.qualifier, vec!["A", "B"]);
        assert!(cx.import);

        let text = "part w : ";
        let cx = completion_context(text, 9);
        assert!(cx.qualifier.is_empty());
        assert!(!cx.import);
    }

    #[test]
    fn dot_chain_detection() {
        // Bare dot, and a partial after it.
        let text = "package P { attribute t = fuelTank. }";
        let cx = completion_context(text, 35);
        assert_eq!(cx.dot_chain, vec!["fuelTank"]);
        let text = "package P { attribute t = fuelTank.vol }";
        let cx = completion_context(text, 38);
        assert_eq!(cx.dot_chain, vec!["fuelTank"]);
        assert_eq!(&text[cx.partial_start as usize..cx.offset as usize], "vol");

        // Multi-hop chains keep every segment, in order.
        let text = "package P { attribute t = sys.tank.liq }";
        let cx = completion_context(text, 38);
        assert_eq!(cx.dot_chain, vec!["sys", "tank"]);

        // A literal's decimal point is no chain step.
        let text = "package P { attribute t = 9.8 }";
        let cx = completion_context(text, 29);
        assert!(cx.dot_chain.is_empty());

        // `::` qualifiers keep their own context.
        let text = "package P { part x : ISQ::Torque }";
        let cx = completion_context(text, 32);
        assert!(cx.dot_chain.is_empty());
    }
}
