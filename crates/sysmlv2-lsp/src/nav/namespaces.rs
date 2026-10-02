//! The completion tier's symbol tables and what their namespaces make
//! visible. A table holds the qualified symbols of a set of units,
//! flattened from their outlines, and the `import` statements their
//! namespaces declare; it answers which members a namespace makes
//! visible beyond the ones it owns — what its public imports bring in,
//! directly or through the imported namespaces' own public imports —
//! without a model build.
//!
//! Targets resolve the way the notation reads them, as far as a syntax
//! tier can: the first segment among the owned members of the
//! namespace the import sits in, then of each enclosing namespace out
//! to the root; each later segment among the visible members of the
//! namespace before it. Tables layer: the document being completed
//! over the rest of the workspace over the library, lookups falling
//! through, each layer's imports naming namespaces of its own or of the
//! layers below. A layer keeps what it works out for as long as it
//! lives, so the library's answers last the session and the rest of
//! the workspace's last while no other document changes.
//!
//! What a namespace makes visible is decided once per namespace — for
//! its clients, and for a name written inside it
//! ([`SymbolTable::names`]) — and serves every question asked of it —
//! what a qualifier lists, whether an existing import provides a name,
//! which package an inserted import may run through — so the answers
//! cannot disagree: an owned member hides an imported one of the same
//! name from whoever sees it at every step of a re-export chain, and a
//! name two imports bring in for different elements denotes neither.

use super::QualifiedSymbol;
use crate::autoimport::Brought;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

#[cfg(test)]
thread_local! {
    /// The tables' work on this thread, so a test can pin what a
    /// completion request costs: symbols indexed into a table,
    /// namespaces whose visible names were worked out, and namespaces
    /// whose routes were walked.
    pub(crate) static WORK: std::cell::Cell<[usize; 3]> = const { std::cell::Cell::new([0; 3]) };
}

thread_local! {
    /// The views being worked out on this thread (see
    /// [`SymbolTable::guarded`]).
    static WORKING: std::cell::RefCell<Working> = std::cell::RefCell::default();
}

/// The views being worked out on a thread: a view asked for again while
/// it is worked out — through a name looked up on the way, say — is a
/// cycle, cut there, and every view begun since works with an answer
/// short of what that one comes to: those are not kept.
#[derive(Default)]
struct Working {
    /// Each view being worked out, by table and view, at its depth.
    open: HashMap<(usize, String), usize>,
    /// The shallowest depth a cut leaves short, if any.
    short: Option<usize>,
}

/// A view being worked out (see [`SymbolTable::guarded`]), left once
/// done — or when the work unwinds, so a view a request gave up on is
/// not taken for one under way by the next.
struct Open {
    id: (usize, String),
    depth: usize,
    left: bool,
}

impl Open {
    /// Leave the view, done: whether its answer is whole, no cut on the
    /// way having left it short.
    fn leave(mut self) -> bool {
        self.left = true;
        WORKING.with(|w| {
            let mut w = w.borrow_mut();
            w.open.remove(&self.id);
            let short = w.short.is_some_and(|d| d <= self.depth);
            if w.short.is_some_and(|d| d >= self.depth) {
                w.short = None;
            }
            !short
        })
    }
}

impl Drop for Open {
    fn drop(&mut self) {
        if !self.left {
            WORKING.with(|w| {
                let mut w = w.borrow_mut();
                w.open.remove(&self.id);
                if w.short.is_some_and(|d| d >= self.depth) {
                    w.short = None;
                }
            });
        }
    }
}

/// Count `n` units of the work at `slot` of [`WORK`].
#[cfg(test)]
fn work(slot: usize, n: usize) {
    WORK.with(|w| {
        let mut counts = w.get();
        counts[slot] += n;
        w.set(counts);
    });
}

/// What an import brings into its namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Reach {
    /// `import T;` — the one member `T` names.
    Member,
    /// `import T::*;` — the members of `T`.
    Members,
    /// `import T::*::**;` — the members of `T` and, recursively, of the
    /// namespaces among them. `import T::**;` is recorded as a `Member`
    /// and a `Recursive`.
    Recursive,
}

/// Whose view of a namespace's names is asked for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Access {
    /// A client outside the namespace: its public members, and what its
    /// public imports bring in.
    Clients,
    /// A name written inside the namespace, or an `import all` of it:
    /// every member, and what every import brings in.
    Inside,
}

/// One import statement, as a table records it.
#[derive(Clone, Debug)]
pub(super) struct ImportRecord {
    /// The importing namespace's qualified path (`""`: the root).
    pub owner: String,
    /// The target as written: one raw name per segment.
    pub target: Vec<String>,
    /// `$::`-rooted: resolved from the root, not from the owner.
    pub global: bool,
    pub reach: Reach,
    /// Re-exported to the namespace's clients: `public`, or no
    /// visibility keyword at all.
    pub public: bool,
    /// `import all`: brings in what a name written inside the target
    /// finds there, whatever its visibility.
    pub all: bool,
    /// Conditioned by a filter: brings in only the members the
    /// condition admits, which the syntax tier cannot tell.
    pub filtered: bool,
    /// The declaring unit of a workspace import (the key of
    /// [`QualifiedSymbol`]'s site), so a seeded unit's imports are
    /// shadowed with its symbols while the unit is open.
    pub unit: Option<String>,
    /// The target's qualified path, once the table resolved it.
    resolved: Option<String>,
}

impl ImportRecord {
    /// Does the import make what it brings in visible to the
    /// namespace's clients, as far as the syntax tier can tell? A
    /// filtered one counts as bringing in nothing.
    fn reexports(&self) -> bool {
        self.public && !self.filtered
    }

    pub(super) fn new(
        owner: &str,
        form: &crate::outline::ImportForm,
        reach: Reach,
        unit: Option<&str>,
    ) -> ImportRecord {
        ImportRecord {
            owner: owner.to_string(),
            target: form.target.clone(),
            global: form.global,
            reach,
            public: form.public,
            all: form.all,
            filtered: form.filtered,
            unit: unit.map(str::to_string),
            resolved: None,
        }
    }
}

/// What a walk over the units records besides their symbols.
#[derive(Clone, Default)]
pub(super) struct Links {
    pub imports: Vec<ImportRecord>,
    /// What each declaration specializes, as written (see
    /// [`crate::outline::Base`]), by its qualified path.
    pub bases: Vec<(String, Vec<crate::outline::Base>)>,
}

impl Links {
    /// Record the import at an outline node inside `owner`: one record,
    /// or two for `import T::**;`.
    pub(super) fn import(
        &mut self,
        owner: &str,
        form: &crate::outline::ImportForm,
        unit: Option<&str>,
    ) {
        let reaches: &[Reach] = match (form.namespace, form.recursive) {
            (false, false) => &[Reach::Member],
            (true, false) => &[Reach::Members],
            (true, true) => &[Reach::Recursive],
            (false, true) => &[Reach::Member, Reach::Recursive],
        };
        for &reach in reaches {
            self.imports
                .push(ImportRecord::new(owner, form, reach, unit));
        }
    }
}

/// What a namespace makes visible, by name, in the order the names come
/// in: the qualified path of the one element each denotes there, or
/// none when two of the namespace's imports bring in different elements
/// under it — an ambiguous reference. A name comes in at a tier — the
/// namespace's own members, what its imports of one member bring in,
/// what its imports of a namespace's members do — and one that came in
/// at an earlier tier hides it at a later one.
#[derive(Default)]
pub(super) struct Names {
    entries: Vec<(String, Option<String>, u8)>,
    index: HashMap<String, usize>,
}

impl Names {
    /// What `name` denotes: `None` when nothing is visible under it,
    /// `Some(None)` when it is ambiguous.
    fn get(&self, name: &str) -> Option<Option<&str>> {
        self.index.get(name).map(|&i| self.entries[i].1.as_deref())
    }

    /// Record that `name` denotes the element at `path` (`None`: an
    /// ambiguous name brought in whole), coming in at `tier`: a
    /// different element at the same tier makes it ambiguous, one at an
    /// earlier tier replaces it, one at a later tier is hidden.
    fn add(&mut self, tier: u8, name: &str, path: Option<&str>) {
        match self.index.get(name) {
            None => {
                self.index.insert(name.to_string(), self.entries.len());
                self.entries
                    .push((name.to_string(), path.map(str::to_string), tier));
            }
            Some(&i) => {
                let (_, known, at) = &mut self.entries[i];
                if tier < *at {
                    *known = path.map(str::to_string);
                    *at = tier;
                } else if tier == *at && known.as_deref() != path {
                    *known = None;
                }
            }
        }
    }

    /// Every name with what it denotes, in order.
    fn iter(&self) -> impl Iterator<Item = (&str, Option<&str>)> {
        self.entries
            .iter()
            .map(|(name, path, _)| (name.as_str(), path.as_deref()))
    }
}

/// The tiers names come in at (see [`Names`]).
const OWNED: u8 = 0;
const IMPORTED_MEMBER: u8 = 1;
const IMPORTED_MEMBERS: u8 = 2;

/// The qualified symbols and imports of a set of units, indexed.
#[derive(Default)]
pub(crate) struct SymbolTable {
    symbols: Vec<QualifiedSymbol>,
    imports: Vec<ImportRecord>,
    /// Qualified path → the first symbol declaring it.
    by_path: HashMap<String, usize>,
    /// Namespace path (`""`: the root) → its members, in order.
    by_parent: HashMap<String, Vec<usize>>,
    /// Namespace path → the imports it declares, in order.
    by_owner: HashMap<String, Vec<usize>>,
    /// Resolved target path → the re-exporting imports naming it.
    by_target: HashMap<String, Vec<usize>>,
    /// The namespace owning a re-exporting single-member import's target
    /// → those imports.
    singles: HashMap<String, Vec<usize>>,
    /// The table lookups fall through to (the library's, for a
    /// workspace table).
    base: Option<Arc<SymbolTable>>,
    /// [`Self::names`], by view and namespace, as they are asked for.
    visible: Mutex<[HashMap<String, Arc<Names>>; 2]>,
    /// [`Self::recursive_in`], by view and namespace, as they are asked
    /// for.
    recursive: Mutex<[HashMap<String, Arc<Names>>; 2]>,
    /// What each declaration this table holds specializes, as written,
    /// by its qualified path (see [`Links::bases`]).
    written: HashMap<String, Vec<crate::outline::Base>>,
    /// [`Self::bases_of`], by element, as they are asked for.
    bases: Mutex<HashMap<String, Arc<[String]>>>,
    /// [`Self::inherited`], by element, as they are asked for.
    inheritance: Mutex<HashMap<String, Arc<Names>>>,
    /// [`Self::heritage`], by element, as they are asked for.
    heritage: Mutex<HashMap<String, Arc<Names>>>,
    /// [`Self::routes_of`], by namespace, as they are asked for.
    routes: Mutex<HashMap<String, Arc<Routes>>>,
}

/// The routes to a namespace's members: those that see all of them,
/// and, for a member a single-member import names, those that see it
/// alone too — each list best first.
#[derive(Default)]
struct Routes {
    /// The segments of the namespace's own path.
    segments: usize,
    members: Vec<Route>,
    singles: Vec<(String, Vec<Route>)>,
}

impl Routes {
    /// The routes to the member named `name`.
    fn to(&self, name: &str) -> &[Route] {
        self.singles
            .iter()
            .find(|(n, _)| n == name)
            .map_or(&self.members, |(_, routes)| routes)
    }
}

/// A top-level package that sees a namespace's members under their
/// own names: how well it names them (see [`SymbolTable::import_path`])
/// and the number of imports on the way. What the package makes
/// visible is asked of the table choosing the path, never kept here:
/// the layers above the one that worked the routes out share them, and
/// a layer above can declare in the package itself.
#[derive(Clone)]
struct Route {
    rank: u8,
    hops: usize,
    package: String,
}

impl Route {
    fn key(&self) -> (u8, usize, &str) {
        (self.rank, self.hops, &self.package)
    }
}

impl SymbolTable {
    /// The table's symbols: its own, then those of the workspace layers
    /// below it — never the library's, which a library table alone
    /// yields.
    pub(super) fn iter(&self) -> impl Iterator<Item = &QualifiedSymbol> {
        std::iter::successors(Some(self), |t| {
            t.base.as_deref().filter(|b| b.base.is_some())
        })
        .flat_map(|t| t.symbols.iter())
    }

    /// The table's own symbols, not those of the layers below.
    pub(super) fn symbols(&self) -> &[QualifiedSymbol] {
        &self.symbols
    }

    /// This table and the ones below it, topmost first.
    fn layers(&self) -> impl Iterator<Item = &SymbolTable> {
        std::iter::successors(Some(self), |t| t.base.as_deref())
    }

    /// Would a re-exporting import the table could not resolve on its
    /// own resolve over `top`, a layer above it? Only those change what
    /// a namespace makes visible: a private import's target decides
    /// nothing a client sees.
    pub(super) fn resolves_above(&self, top: &SymbolTable) -> bool {
        self.imports
            .iter()
            .filter(|imp| imp.resolved.is_none() && imp.reexports())
            .any(|imp| top.resolve(&imp.owner, &imp.target, imp.global).is_some())
    }

    /// The table's own symbols and imports, for a table built anew.
    pub(super) fn parts(&self) -> (Vec<QualifiedSymbol>, Links) {
        let mut imports = self.imports.clone();
        for imp in &mut imports {
            imp.resolved = None;
        }
        let bases = self
            .written
            .iter()
            .map(|(path, bases)| (path.clone(), bases.clone()))
            .collect();
        (self.symbols.clone(), Links { imports, bases })
    }

    /// Index `symbols` and `links` over `base` and resolve the import
    /// targets.
    pub(super) fn new(
        symbols: Vec<QualifiedSymbol>,
        links: Links,
        base: Option<Arc<SymbolTable>>,
    ) -> SymbolTable {
        #[cfg(test)]
        work(0, symbols.len());
        let mut table = SymbolTable {
            symbols,
            imports: links.imports,
            base,
            ..SymbolTable::default()
        };
        for (path, bases) in links.bases {
            table.written.entry(path).or_insert(bases);
        }
        for (i, s) in table.symbols.iter().enumerate() {
            table.by_path.entry(s.qualified.clone()).or_insert(i);
            if let Some(parent) = parent_of(s) {
                table
                    .by_parent
                    .entry(parent.to_string())
                    .or_default()
                    .push(i);
            }
        }
        for (i, imp) in table.imports.iter().enumerate() {
            table.by_owner.entry(imp.owner.clone()).or_default().push(i);
        }
        // A target reached through another namespace's public import
        // needs that import resolved first: each round picks up what the
        // previous one made reachable, until one resolves nothing new.
        loop {
            let resolved: Vec<(usize, String)> = table
                .imports
                .iter()
                .enumerate()
                .filter(|(_, imp)| imp.resolved.is_none())
                .filter_map(|(i, imp)| {
                    table
                        .resolve(&imp.owner, &imp.target, imp.global)
                        .map(|path| (i, path))
                })
                .collect();
            if resolved.is_empty() {
                break;
            }
            for (i, path) in resolved {
                table.imports[i].resolved = Some(path);
            }
        }
        for (i, imp) in table.imports.iter().enumerate() {
            if let Some(target) = imp.resolved.as_ref().filter(|_| imp.reexports()) {
                table.by_target.entry(target.clone()).or_default().push(i);
                if imp.reach == Reach::Member {
                    let parent = enclosing(target).unwrap_or_default();
                    table.singles.entry(parent.to_string()).or_default().push(i);
                }
            }
        }
        table.resolve_aliases();
        table
    }

    /// Take each alias as what it names (see [`Self::alias_target`]):
    /// its target's kind, declaration, and types — completion shows,
    /// admits, and ranks it so — and whether an operator names a
    /// function by it. One whose target does not resolve keeps what it
    /// was collected with.
    fn resolve_aliases(&mut self) {
        let named: Vec<_> = (0..self.symbols.len())
            .filter(|&i| self.symbols[i].alias.is_some())
            .filter_map(|i| {
                let t = self.alias_target(i)?;
                Some((i, t.kind, t.decl, t.types.clone()))
            })
            .collect();
        for (i, kind, decl, types) in named {
            let s = &mut self.symbols[i];
            s.operator = super::is_operator_spelling(&s.name)
                && matches!(
                    kind,
                    lsp_types::CompletionItemKind::FUNCTION
                        | lsp_types::CompletionItemKind::OPERATOR
                );
            (s.kind, s.decl, s.types) = (kind, decl, types);
        }
    }

    /// The symbol the alias at `i` names: its target read as a name
    /// written where the alias is ([`Self::resolve_written`]), through
    /// further aliases of this table — one of a table below is already
    /// what it names. `None` when a target does not resolve, or the
    /// aliases lead back to one on the way.
    fn alias_target(&self, i: usize) -> Option<&QualifiedSymbol> {
        let mut s = &self.symbols[i];
        let mut seen = HashSet::new();
        while let Some(alias) = &s.alias {
            if !seen.insert(s.qualified.as_str()) {
                return None;
            }
            let path = self.resolve_written(parent_of(s)?, &alias.target, alias.global)?;
            s = match self.by_path.get(&path) {
                Some(&j) => &self.symbols[j],
                None => return self.symbol_at(&path),
            };
        }
        Some(s)
    }

    /// Resolve a qualified name written inside the namespace at `owner`
    /// as the notation reads it: the first segment among what each
    /// namespace from `owner` out to the root finds under it — its
    /// members, and what its imports bring in, private ones included —
    /// or from the root alone when `global`; each later segment among
    /// what the namespace before makes visible to `owner`: every member
    /// when `owner` is inside it, the public ones otherwise. `None` when
    /// a segment does not resolve, or names two elements.
    fn resolve_written(&self, owner: &str, target: &[String], global: bool) -> Option<String> {
        let (first, rest) = target.split_first()?;
        let mut scope = Some(if global { "" } else { owner });
        let mut path = None;
        while let Some(s) = scope {
            if let Some(found) = self.name_in(s, Access::Inside, first, &mut HashSet::new()) {
                path = Some(found?);
                break;
            }
            scope = enclosing(s);
        }
        let mut path = path?;
        for segment in rest {
            let access = if within(owner, &path) {
                Access::Inside
            } else {
                Access::Clients
            };
            path = self.name_in(&path, access, segment, &mut HashSet::new())??;
        }
        Some(path)
    }

    /// What [`Self::names`] holds under `name` for the namespace at
    /// `ns`, worked out for that one name unless the whole answer is
    /// known already: a namespace this table declares in is answered
    /// anew for every table built, and one name rarely needs all it
    /// makes visible.
    fn name_in(
        &self,
        ns: &str,
        access: Access,
        name: &str,
        active: &mut HashSet<(String, Access)>,
    ) -> Option<Option<String>> {
        if let Some(base) = &self.base {
            if !self.by_parent.contains_key(ns) && !self.by_owner.contains_key(ns) {
                return base.name_in(ns, access, name, active);
            }
        }
        if let Some(known) = self.visible.lock().expect("visible names")[access as usize].get(ns) {
            return known.get(name).map(|path| path.map(str::to_string));
        }
        let key = (ns.to_string(), access);
        if !active.insert(key.clone()) {
            return None;
        }
        let found = self.compute_name(ns, access, name, active);
        active.remove(&key);
        found
    }

    /// [`Self::compute_names`] for the one name `name`.
    fn compute_name(
        &self,
        ns: &str,
        access: Access,
        name: &str,
        active: &mut HashSet<(String, Access)>,
    ) -> Option<Option<String>> {
        let own = join(ns, name);
        if self
            .symbol_at(&own)
            .is_some_and(|s| access == Access::Inside || s.public)
        {
            return Some(Some(own));
        }
        // The imports' answers, the earliest tier deciding.
        let mut found: Option<(u8, Option<String>)> = None;
        for imp in self.imports_of(ns) {
            let admitted = match access {
                Access::Clients => imp.reexports(),
                Access::Inside => !imp.filtered,
            };
            let Some(target) = imp.resolved.as_deref().filter(|_| admitted) else {
                continue;
            };
            let inner = if imp.all {
                Access::Inside
            } else {
                Access::Clients
            };
            let (tier, brought) = match imp.reach {
                Reach::Member => (
                    IMPORTED_MEMBER,
                    (imp.target.last().map(String::as_str) == Some(name)
                        && self.symbol_at(target).is_some_and(|s| imp.all || s.public))
                    .then(|| Some(target.to_string())),
                ),
                Reach::Members => (IMPORTED_MEMBERS, self.name_in(target, inner, name, active)),
                Reach::Recursive => (
                    IMPORTED_MEMBERS,
                    self.recursive_in(target, inner, active)
                        .get(name)
                        .map(|path| path.map(str::to_string)),
                ),
            };
            let Some(brought) = brought else {
                continue;
            };
            found = match found {
                None => Some((tier, brought)),
                Some((at, _)) if tier < at => Some((tier, brought)),
                Some((at, known)) if tier == at && known != brought => Some((at, None)),
                kept => kept,
            };
        }
        found.map(|(_, path)| path)
    }

    /// The symbol declaring `path`, here or in the base table.
    pub(super) fn symbol_at(&self, path: &str) -> Option<&QualifiedSymbol> {
        match self.by_path.get(path) {
            Some(&i) => Some(&self.symbols[i]),
            None => self.base.as_ref().and_then(|b| b.symbol_at(path)),
        }
    }

    /// The owned members of the namespace at `path`, here and in the
    /// base table.
    fn members_of<'s>(&'s self, path: &str, out: &mut Vec<&'s QualifiedSymbol>) {
        if let Some(members) = self.by_parent.get(path) {
            out.extend(members.iter().map(|&i| &self.symbols[i]));
        }
        if let Some(base) = &self.base {
            base.members_of(path, out);
        }
    }

    /// The imports the namespace at `path` declares, here and in the
    /// base table.
    fn imports_of(&self, path: &str) -> Vec<&ImportRecord> {
        let mut out: Vec<&ImportRecord> = self
            .by_owner
            .get(path)
            .into_iter()
            .flatten()
            .map(|&i| &self.imports[i])
            .collect();
        if let Some(base) = &self.base {
            out.extend(base.imports_of(path));
        }
        out
    }

    /// The re-exporting imports whose target resolved to `path`, here
    /// and in the layers below.
    fn importers_of<'s>(&'s self, path: &'s str) -> impl Iterator<Item = &'s ImportRecord> {
        self.layers().flat_map(move |t| {
            t.by_target
                .get(path)
                .into_iter()
                .flatten()
                .map(move |&i| &t.imports[i])
        })
    }

    /// Every import, here then in the base table.
    fn all_imports(&self) -> impl Iterator<Item = &ImportRecord> {
        let base = self
            .base
            .iter()
            .flat_map(|b| b.all_imports().collect::<Vec<_>>());
        self.imports.iter().chain(base)
    }

    /// Resolve a qualified name written inside the namespace at
    /// `owner`: the first segment among the owned members of `owner`,
    /// then of each enclosing namespace out to the root (from the root
    /// alone when `global`), each later segment among what the namespace
    /// before shows `owner` — every member when `owner` is inside it,
    /// the public ones otherwise.
    fn resolve(&self, owner: &str, target: &[String], global: bool) -> Option<String> {
        let (first, rest) = target.split_first()?;
        let mut scope = Some(if global { "" } else { owner });
        let mut path = None;
        while let Some(s) = scope {
            let candidate = join(s, first);
            if self.symbol_at(&candidate).is_some() {
                path = Some(candidate);
                break;
            }
            scope = enclosing(s);
        }
        let mut path = path?;
        for segment in rest {
            let inside = within(owner, &path);
            path = self.member_path(&path, segment, inside, &mut HashSet::new())?;
        }
        Some(path)
    }

    /// The qualified path of the member the namespace at `ns` shows
    /// under `name` — to a name written inside it (`inside`) every
    /// member, to a client the public ones: its own, else the first its
    /// imports bring in — every one of them inside it, the public ones
    /// to a client.
    fn member_path(
        &self,
        ns: &str,
        name: &str,
        inside: bool,
        seen: &mut HashSet<String>,
    ) -> Option<String> {
        let own = join(ns, name);
        if self.symbol_at(&own).is_some_and(|s| inside || s.public) {
            return Some(own);
        }
        if !seen.insert(ns.to_string()) {
            return None;
        }
        for imp in self.imports_of(ns) {
            let admitted = if inside {
                !imp.filtered
            } else {
                imp.reexports()
            };
            let Some(target) = imp.resolved.as_deref().filter(|_| admitted) else {
                continue;
            };
            let found = match imp.reach {
                Reach::Member => (imp.target.last().map(String::as_str) == Some(name)
                    && self.symbol_at(target).is_some_and(|s| imp.all || s.public))
                .then(|| target.to_string()),
                Reach::Members | Reach::Recursive => self.member_path(target, name, imp.all, seen),
            };
            if found.is_some() {
                return found;
            }
        }
        None
    }

    /// The members the namespaces a qualifier names make visible
    /// through their imports — the public ones to a client, every one
    /// to a name written inside them (`access`) — directly or through
    /// the imported namespaces' own, in import order, not counting the
    /// members they own, nor a name that denotes no one element. The
    /// qualifier matches as [`QualifiedSymbol`] parents do: the path
    /// itself or any path ending in it.
    pub(super) fn reexported_members(
        &self,
        qualifier: &str,
        access: Access,
    ) -> Vec<&QualifiedSymbol> {
        let suffix = format!("::{qualifier}");
        let mut owners: Vec<&str> = Vec::new();
        for imp in self.all_imports() {
            let owner = imp.owner.as_str();
            if (owner == qualifier || owner.ends_with(&suffix)) && !owners.contains(&owner) {
                owners.push(owner);
            }
        }
        let mut out = Vec::new();
        for owner in owners {
            let names = self.names(owner, access);
            for (_, path) in names.iter() {
                let Some(path) = path.filter(|p| enclosing(p) != Some(owner)) else {
                    continue;
                };
                out.extend(self.symbol_at(path));
            }
        }
        out
    }

    /// What the namespace at `ns` makes visible, by name, to `access`:
    /// its own members — the public ones to a client — then what its
    /// imports bring in — the public ones' to a client — one member,
    /// the members of a namespace (with what that namespace makes
    /// visible in turn), or a namespace's contents recursively; an
    /// `import all` brings in what a name written inside its target
    /// finds there. An owned member hides an imported one of the same
    /// name from whoever sees it; a name two imports bring in for
    /// different elements denotes neither. Decided once per namespace
    /// and view: a namespace the table declares nothing in is answered
    /// by the base table, which keeps its answers.
    pub(super) fn names(&self, ns: &str, access: Access) -> Arc<Names> {
        self.names_in(ns, access, &mut HashSet::new())
    }

    /// [`Self::names`], with the namespaces whose answer is being worked
    /// out further up: an import cycle adds nothing more.
    fn names_in(
        &self,
        ns: &str,
        access: Access,
        active: &mut HashSet<(String, Access)>,
    ) -> Arc<Names> {
        if let Some(base) = &self.base {
            if !self.by_parent.contains_key(ns) && !self.by_owner.contains_key(ns) {
                return base.names_in(ns, access, active);
            }
        }
        if let Some(known) = self.visible.lock().expect("visible names")[access as usize].get(ns) {
            return Arc::clone(known);
        }
        let key = (ns.to_string(), access);
        if !active.insert(key.clone()) {
            return Arc::default();
        }
        let view = format!("n{} {ns}", access as usize);
        let worked = self.guarded(view, || self.compute_names(ns, access, active));
        active.remove(&key);
        let Some((names, keep)) = worked else {
            return Arc::default();
        };
        let names = Arc::new(names);
        if keep {
            self.visible.lock().expect("visible names")[access as usize]
                .insert(key.0, Arc::clone(&names));
        }
        names
    }

    fn compute_names(
        &self,
        ns: &str,
        access: Access,
        active: &mut HashSet<(String, Access)>,
    ) -> Names {
        #[cfg(test)]
        work(1, 1);
        let mut names = Names::default();
        let mut own = Vec::new();
        self.members_of(ns, &mut own);
        // An owned member hides an imported one of the same name from
        // whoever sees it: a private or protected one is visible to no
        // client, so it hides nothing from one.
        for s in own
            .into_iter()
            .filter(|s| access == Access::Inside || s.public)
        {
            names.add(OWNED, &s.name, Some(&s.qualified));
        }
        // What the imports bring in, as whoever they name them for finds
        // them — a client of the target, or with `all` a name written
        // inside it: an import of one member ahead of an import of a
        // namespace's members.
        for imp in self.imports_of(ns) {
            let admitted = match access {
                Access::Clients => imp.reexports(),
                Access::Inside => !imp.filtered,
            };
            let Some(target) = imp.resolved.as_deref().filter(|_| admitted) else {
                continue;
            };
            let inner = if imp.all {
                Access::Inside
            } else {
                Access::Clients
            };
            match imp.reach {
                Reach::Member => {
                    if let Some(s) = self.symbol_at(target).filter(|s| imp.all || s.public) {
                        names.add(IMPORTED_MEMBER, &s.name, Some(&s.qualified));
                    }
                }
                Reach::Members => {
                    for (name, path) in self.names_in(target, inner, active).iter() {
                        names.add(IMPORTED_MEMBERS, name, path);
                    }
                }
                Reach::Recursive => {
                    for (name, path) in self.recursive_in(target, inner, active).iter() {
                        names.add(IMPORTED_MEMBERS, name, path);
                    }
                }
            }
        }
        names
    }

    /// What an import of the contents of the namespace at `ns`,
    /// recursively, brings in, as `access` finds them: the members of
    /// the namespaces it owns, at any depth — a client sees none inside
    /// a private or protected one, and nobody inside a usage found by
    /// the name of what it redefines or references — what it makes
    /// visible itself, and what the elements it reaches inherit (see
    /// [`Self::compute_recursive`]). Decided once per namespace and
    /// view, like [`Self::names`].
    fn recursive_in(
        &self,
        ns: &str,
        access: Access,
        active: &mut HashSet<(String, Access)>,
    ) -> Arc<Names> {
        if let Some(base) = &self.base {
            if !self.by_parent.contains_key(ns) && !self.by_owner.contains_key(ns) {
                return base.recursive_in(ns, access, active);
            }
        }
        if let Some(known) =
            self.recursive.lock().expect("recursive names")[access as usize].get(ns)
        {
            return Arc::clone(known);
        }
        let key = format!("r{} {ns}", access as usize);
        let Some((names, keep)) = self.guarded(key, || self.compute_recursive(ns, access, active))
        else {
            return Arc::default();
        };
        let names = Arc::new(names);
        if keep {
            self.recursive.lock().expect("recursive names")[access as usize]
                .insert(ns.to_string(), Arc::clone(&names));
        }
        names
    }

    /// [`Self::recursive_in`], worked out.
    fn compute_recursive(
        &self,
        ns: &str,
        access: Access,
        active: &mut HashSet<(String, Access)>,
    ) -> Names {
        let mut below: Vec<&QualifiedSymbol> = Vec::new();
        let mut stack = vec![ns.to_string()];
        let mut walked = HashSet::new();
        while let Some(path) = stack.pop() {
            if !walked.insert(path.clone()) {
                continue;
            }
            let mut members = Vec::new();
            self.members_of(&path, &mut members);
            members.retain(|s| access == Access::Inside || s.public);
            stack.extend(
                members
                    .iter()
                    .filter(|s| !s.effective)
                    .map(|s| s.qualified.clone()),
            );
            below.extend(members);
        }
        let mut names = Names::default();
        for s in below {
            names.add(OWNED, &s.name, Some(&s.qualified));
        }
        for (name, path) in self.names_in(ns, access, active).iter() {
            names.add(OWNED, name, path);
        }
        // What each element the walk reaches inherits is found in it
        // too, unless the element declares that name itself. What a
        // library type passes on also comes to elements no written
        // specialization shows, through the library base every element
        // of a kind specializes: a name it passes on denotes no one
        // element here.
        for path in &walked {
            for (name, found) in self.inherited(path).iter() {
                if self.symbol_at(&join(path, name)).is_some() {
                    continue;
                }
                let library = found
                    .and_then(|f| self.symbol_at(f))
                    .is_some_and(|s| s.site.is_none());
                names.add(OWNED, name, found.filter(|_| !library));
            }
        }
        names
    }

    /// Does this table declare the element at `path`, or anything in it?
    /// Else a table below answers for it.
    fn holds(&self, path: &str) -> bool {
        self.by_path.contains_key(path) || self.by_parent.contains_key(path)
    }

    /// Work out the view `key` of this table with `work`, unless it is
    /// being worked out already further up: `None` then (see
    /// [`Working`]). With the answer, whether to keep it: not when a
    /// cut on the way left it short.
    fn guarded<T>(&self, key: String, work: impl FnOnce() -> T) -> Option<(T, bool)> {
        let id = (std::ptr::from_ref(self) as usize, key);
        let depth = WORKING.with(|w| {
            let mut w = w.borrow_mut();
            if let Some(&at) = w.open.get(&id) {
                w.short = Some(w.short.map_or(at + 1, |d| d.min(at + 1)));
                return None;
            }
            let depth = w.open.len();
            w.open.insert(id.clone(), depth);
            Some(depth)
        })?;
        let open = Open {
            id,
            depth,
            left: false,
        };
        let out = work();
        Some((out, open.leave()))
    }

    /// What the element at `path` specializes, resolved: the types it is
    /// typed by, the features it subsets, redefines, or references, the
    /// definitions it specializes — each reference read from where the
    /// declaration is written, a redefined feature among what that
    /// owner inherits, the element itself never. Worked out once per
    /// element.
    fn bases_of(&self, path: &str) -> Arc<[String]> {
        if let Some(base) = &self.base {
            if !self.holds(path) {
                return base.bases_of(path);
            }
        }
        if let Some(known) = self.bases.lock().expect("bases").get(path) {
            return Arc::clone(known);
        }
        let Some((declared, owner)) = self
            .layers()
            .find_map(|t| t.written.get(path))
            .zip(self.symbol_at(path).and_then(parent_of))
        else {
            return Arc::default();
        };
        let work = || {
            let mut out: Vec<String> = Vec::new();
            for b in declared {
                let written = &b.written;
                let inherited = match written.target.as_slice() {
                    [name] if b.redefines && !written.global => self
                        .inherited(owner)
                        .get(name)
                        .flatten()
                        .map(str::to_string),
                    _ => None,
                };
                let found = inherited
                    .or_else(|| self.resolve_written(owner, &written.target, written.global));
                if let Some(found) = found.filter(|f| f != path && !out.contains(f)) {
                    out.push(found);
                }
            }
            out
        };
        let Some((bases, keep)) = self.guarded(format!("b {path}"), work) else {
            return Arc::default();
        };
        let bases: Arc<[String]> = bases.into();
        if keep {
            self.bases
                .lock()
                .expect("bases")
                .insert(path.to_string(), Arc::clone(&bases));
        }
        bases
    }

    /// What the element at `path` inherits, by name: what each element
    /// it specializes passes on ([`Self::heritage`]), a name two of them
    /// pass on for different elements denoting neither. Worked out once
    /// per element.
    fn inherited(&self, path: &str) -> Arc<Names> {
        if let Some(base) = &self.base {
            if !self.holds(path) {
                return base.inherited(path);
            }
        }
        if let Some(known) = self.inheritance.lock().expect("inheritance").get(path) {
            return Arc::clone(known);
        }
        let work = || {
            let mut names = Names::default();
            for b in self.bases_of(path).iter() {
                for (name, found) in self.heritage(b).iter() {
                    names.add(OWNED, name, found);
                }
            }
            names
        };
        let Some((names, keep)) = self.guarded(format!("i {path}"), work) else {
            return Arc::default();
        };
        let names = Arc::new(names);
        if keep {
            self.inheritance
                .lock()
                .expect("inheritance")
                .insert(path.to_string(), Arc::clone(&names));
        }
        names
    }

    /// What the element at `path` passes on to what specializes it, by
    /// name: its public members, then what it inherits, a member hiding
    /// an inherited one of its name. Worked out once per element.
    fn heritage(&self, path: &str) -> Arc<Names> {
        if let Some(base) = &self.base {
            if !self.holds(path) {
                return base.heritage(path);
            }
        }
        if let Some(known) = self.heritage.lock().expect("heritage").get(path) {
            return Arc::clone(known);
        }
        let work = || {
            let mut names = Names::default();
            let mut own = Vec::new();
            self.members_of(path, &mut own);
            for s in own.into_iter().filter(|s| s.public) {
                names.add(OWNED, &s.name, Some(&s.qualified));
            }
            for (name, found) in self.inherited(path).iter() {
                names.add(IMPORTED_MEMBER, name, found);
            }
            names
        };
        let Some((names, keep)) = self.guarded(format!("h {path}"), work) else {
            return Arc::default();
        };
        let names = Arc::new(names);
        if keep {
            self.heritage
                .lock()
                .expect("heritage")
                .insert(path.to_string(), Arc::clone(&names));
        }
        names
    }

    /// Does `name` denote exactly the element at `qualified` for the
    /// clients of the namespace at `ns`?
    fn denotes(&self, ns: &str, name: &str, qualified: &str) -> bool {
        self.names(ns, Access::Clients).get(name) == Some(Some(qualified))
    }
}

impl SymbolTable {
    /// The path an import of the symbol at `qualified` (named `name`)
    /// should name. Besides its own path, every top-level package that
    /// makes the symbol visible — through its public imports, and
    /// theirs in turn — offers one of two segments. The shortest wins;
    /// between equally short ones the package of the symbol's family
    /// comes first (a package whose name its defining package's name
    /// extends: `ISQ` for `ISQBase::MassValue`), then the symbol's own
    /// path or its own top-level package, then the fewest imports on
    /// the way, then the spelling. A package where the name denotes
    /// anything else — a member of its own, or two imports' elements —
    /// offers nothing.
    pub(super) fn import_path(&self, name: &str, qualified: &str) -> String {
        self.import_route(name, qualified)
            .unwrap_or_else(|| qualified.to_string())
    }

    /// [`Self::import_path`] when it runs through a re-exporting package,
    /// `None` when it is the symbol's own path.
    fn import_route(&self, name: &str, qualified: &str) -> Option<String> {
        let parent = qualified
            .strip_suffix(name)
            .and_then(|p| p.strip_suffix("::"))?;
        let routes = self.routes_of(parent);
        let own = (routes.segments + 1, 1, 0);
        routes
            .to(name)
            .iter()
            .take_while(|r| (2, r.rank, r.hops) < own)
            .find(|r| self.denotes(&r.package, name, qualified))
            .map(|r| join(&r.package, name))
    }

    /// The top-level packages other than `ns` itself that see the
    /// members of the namespace at `ns` under their own names, and those
    /// that see a member alone through an import of it, best first.
    /// Worked out once per namespace; a table whose units re-export
    /// nothing answers from the layer below, which keeps its answers.
    fn routes_of(&self, ns: &str) -> Arc<Routes> {
        if self.by_target.is_empty() {
            if let Some(base) = &self.base {
                return base.routes_of(ns);
            }
        }
        if let Some(known) = self.routes.lock().expect("routes").get(ns) {
            return Arc::clone(known);
        }
        #[cfg(test)]
        work(2, 1);
        let top = ns.split("::").next().unwrap_or(ns);
        let mut members = self.walk_routes(std::iter::once((ns.to_string(), 0)), ns, top);
        members.sort_by(|a, b| a.key().cmp(&b.key()));
        // An import of one member sees it too, and so does whoever
        // imports that importer's members.
        let mut singles: Vec<(String, Vec<Route>)> = Vec::new();
        for t in self.layers() {
            for imp in t
                .singles
                .get(ns)
                .into_iter()
                .flatten()
                .map(|&i| &t.imports[i])
            {
                let Some(name) = imp.resolved.as_deref().and_then(|p| p.rsplit("::").next()) else {
                    continue;
                };
                let start = std::iter::once((imp.owner.clone(), 1));
                let found = self.walk_routes(start, ns, top);
                match singles.iter_mut().find(|(n, _)| n == name) {
                    Some((_, routes)) => routes.extend(found),
                    None => singles.push((name.to_string(), found)),
                }
            }
        }
        for (_, routes) in &mut singles {
            routes.extend(members.iter().cloned());
            routes.sort_by(|a, b| a.key().cmp(&b.key()));
        }
        let segments = ns.matches("::").count() + 1;
        let routes = Arc::new(Routes {
            segments,
            members,
            singles,
        });
        self.routes
            .lock()
            .expect("routes")
            .insert(ns.to_string(), Arc::clone(&routes));
        routes
    }

    /// Walk the public imports outward from `starts` (namespace, imports
    /// on the way): whoever imports a namespace's members, or those of a
    /// namespace around it recursively, sees them too. Every top-level
    /// package reached other than `parent` is a route, ranked against
    /// `top`, the members' own top-level package.
    fn walk_routes(
        &self,
        starts: impl Iterator<Item = (String, usize)>,
        parent: &str,
        top: &str,
    ) -> Vec<Route> {
        let mut routes = Vec::new();
        let mut queue: std::collections::VecDeque<(String, usize)> = starts.collect();
        let mut seen = HashSet::new();
        while let Some((ns, hops)) = queue.pop_front() {
            if !seen.insert(ns.clone()) {
                continue;
            }
            if !ns.is_empty() && !ns.contains("::") && ns != parent {
                let rank = if family(&ns, top) {
                    0
                } else if ns == top {
                    1
                } else {
                    2
                };
                routes.push(Route {
                    rank,
                    hops,
                    package: ns.clone(),
                });
            }
            let mut around = Some(ns.as_str());
            while let Some(a) = around.filter(|a| !a.is_empty()) {
                for imp in self.importers_of(a) {
                    let reaches = match imp.reach {
                        Reach::Members => a == ns,
                        Reach::Recursive => true,
                        Reach::Member => false,
                    };
                    if reaches {
                        queue.push_back((imp.owner.clone(), hops + 1));
                    }
                }
                around = enclosing(a);
            }
        }
        routes
    }
}

impl crate::autoimport::Reexports for SymbolTable {
    fn namespace(&self, owner: &str, target: &[String], global: bool) -> Option<String> {
        self.resolve(owner, target, global)
    }

    fn inherits(&self, ns: &str, name: &str, qualified: &str) -> Brought {
        match self.inherited(ns).get(name) {
            None => Brought::Nothing,
            Some(Some(path)) if path == qualified => Brought::It,
            Some(Some(path)) => Brought::other(path),
            Some(None) => Brought::Several,
        }
    }

    fn inherited_paths(&self, ns: &str) -> Vec<String> {
        self.inherited(ns)
            .iter()
            .filter_map(|(_, path)| path.map(str::to_string))
            .collect()
    }

    fn brought(
        &self,
        ns: &str,
        name: &str,
        qualified: &str,
        recursive: bool,
        all: bool,
    ) -> Brought {
        let access = if all { Access::Inside } else { Access::Clients };
        let names = if recursive {
            self.recursive_in(ns, access, &mut HashSet::new())
        } else {
            self.names(ns, access)
        };
        match names.get(name) {
            None => Brought::Nothing,
            Some(Some(path)) if path == qualified => Brought::It,
            Some(Some(path)) => Brought::other(path),
            Some(None) => Brought::Several,
        }
    }

    fn import_route(&self, name: &str, qualified: &str) -> Option<String> {
        SymbolTable::import_route(self, name, qualified)
    }
}

/// Is the top-level package `ns` the facade of the family `top`
/// belongs to — does `top`'s name extend `ns`'s (`ISQ` for `ISQBase`,
/// `SI` for `SIPrefixes`) at a word boundary?
fn family(ns: &str, top: &str) -> bool {
    top.len() > ns.len()
        && top.starts_with(ns)
        && !top[ns.len()..].starts_with(|c: char| c.is_lowercase())
}

/// The qualified path of the namespace owning `s` (`""`: the root).
fn parent_of(s: &QualifiedSymbol) -> Option<&str> {
    if s.qualified == s.name {
        return Some("");
    }
    s.qualified
        .strip_suffix(s.name.as_str())
        .and_then(|p| p.strip_suffix("::"))
}

/// Is the namespace at `path` the one at `ns`, or nested in it?
fn within(path: &str, ns: &str) -> bool {
    path.strip_prefix(ns)
        .is_some_and(|rest| rest.is_empty() || rest.starts_with("::"))
}

/// `name` as a member of the namespace at `ns` (`""`: the root).
fn join(ns: &str, name: &str) -> String {
    if ns.is_empty() {
        return name.to_string();
    }
    let mut path = String::with_capacity(ns.len() + 2 + name.len());
    path.push_str(ns);
    path.push_str("::");
    path.push_str(name);
    path
}

/// The namespace enclosing the one at `ns`: `None` past the root.
fn enclosing(ns: &str) -> Option<&str> {
    if ns.is_empty() {
        None
    } else {
        Some(ns.rfind("::").map_or("", |i| &ns[..i]))
    }
}
