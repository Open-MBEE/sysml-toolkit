//! Auto-import support for completion: when a completion offers
//! a symbol by simple name that would not resolve at the cursor — a
//! library unit like `SI::volt`, a package member declared elsewhere in
//! the workspace — accepting the item should also insert the `import`
//! that makes the name resolve, the way code editors update imports on
//! accepting an out-of-scope completion.
//!
//! Everything here is syntax-tier over the current document, matching
//! the completion path's cost model (no per-keystroke model build).
//! The cursor's scope chain is read as the notation resolves a name,
//! innermost first: the first scope that declares the name or whose
//! imports bring it in decides what it finds. The analysis cannot see
//! inheritance — a name visible only through a specialization still
//! gets an import offered, redundant but harmless: the qualified target
//! resolves from the root namespace regardless. What an imported
//! namespace makes visible is the one fact from beyond the document:
//! the symbol tables supply it ([`Reexports`]), so an existing
//! `import ISQ::*;` admits `MassValue`, which `ISQ` re-exports from
//! `ISQBase` — but not a name two of a scope's imports bring in for
//! different elements, which finds neither: an import of the one
//! member, found ahead of them, settles it.

use crate::position::offset32;
use std::collections::HashMap;
use sysmlv2_parser::ast::{Dialect, Import, Member, MemberKind, Name, SourceUnit, Visibility};
use sysmlv2_parser::span::Span;

/// One namespace body on the cursor's ancestor chain.
struct Scope<'a> {
    members: &'a [Member],
    /// A package/namespace body (or the unit root) — somewhere an
    /// import statement conventionally belongs.
    package: bool,
    /// The namespace's qualified path (`""`: the unit root) — where an
    /// import in it resolves from. A usage without a name of its own
    /// has its effective name's; another anonymous member's body keeps
    /// the path of the namespace around it.
    path: String,
    /// The names its members declare — by name, short name, or the
    /// name a usage without one is found by — but the phantom the
    /// half-typed statement introduces, sorted for a binary search.
    declared: Vec<&'a str>,
}

/// What the symbol tables know about namespaces beyond the document.
pub(crate) trait Reexports {
    /// The qualified path of the namespace an import names: the import
    /// sits in the namespace at `owner` (`""` for the root) and names
    /// `target` as written.
    fn namespace(&self, owner: &str, target: &[String], global: bool) -> Option<String>;
    /// What `name` denotes, measured against the symbol at `qualified`,
    /// among what an import of the namespace at `ns` brings in — its
    /// members, and with `recursive` those of the namespaces below it —
    /// as a client of `ns` finds them (owned there, or brought in by its
    /// public imports), or with `all` as a name written inside it does.
    fn brought(&self, ns: &str, name: &str, qualified: &str, recursive: bool, all: bool)
    -> Brought;
    /// What `name` denotes, measured against the symbol at `qualified`,
    /// among what the element at `ns` inherits from what it specializes.
    fn inherits(&self, ns: &str, name: &str, qualified: &str) -> Brought;
    /// The paths of the elements the element at `ns` inherits from what
    /// it specializes, each found there by its name alone.
    fn inherited_paths(&self, ns: &str) -> Vec<String>;
    /// The path an import of the symbol at `qualified` (named `name`)
    /// should name when it runs through a package that re-exports it
    /// (`ISQ::MassValue` for `ISQBase::MassValue`), `None` when it is
    /// the symbol's own.
    fn import_route(&self, name: &str, qualified: &str) -> Option<String>;
}

/// What a name finds, measured against the symbol asked about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Brought {
    Nothing,
    /// That symbol, and nothing else.
    It,
    /// One other element, told apart by its path (hashed): a reference
    /// to the name finds it.
    Else(u64),
    /// Several elements: a reference to the name is ambiguous.
    Several,
}

impl Brought {
    /// The one other element at `path`.
    pub(crate) fn other(path: &str) -> Brought {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        path.hash(&mut hasher);
        Brought::Else(hasher.finish())
    }

    /// Take in `other`, brought in beside this.
    fn add(&mut self, other: Brought) {
        *self = match (*self, other) {
            (Brought::Nothing, other) | (other, Brought::Nothing) => other,
            (Brought::It, Brought::It) => Brought::It,
            (Brought::Else(a), Brought::Else(b)) if a == b => Brought::Else(a),
            _ => Brought::Several,
        };
    }
}

/// What accepting a name by itself at the cursor takes to resolve to
/// the symbol offered.
pub(crate) enum Needs {
    /// Nothing: the name finds it as it stands.
    Nothing,
    /// This import.
    Import(ImportEdit),
    /// More than an import should give: the name finds another element
    /// at the cursor — which an inserted import would take it from, for
    /// every reference in the package — or two, decided nearer the
    /// cursor than the import can go.
    Qualifier,
}

/// Which imports admission takes at their word for a symbol (see
/// [`AutoImport::finds`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Admit {
    /// Any: an import whose target the symbol tables do not resolve
    /// admits a name its target spells the symbol with, as a guess.
    Any,
    /// Those the tables resolve, and such a guess only for an
    /// `import all`: for a member its namespace holds private or
    /// protected, which no other import brings in.
    All,
    /// Those the tables resolve alone: for a symbol an ancestor's
    /// visibility keeps inside a namespace, which a guess from its path
    /// cannot see.
    Resolved,
}

/// What a name finds at the cursor (see [`AutoImport::finds`]).
enum Found {
    /// The symbol asked about.
    It,
    /// Nothing.
    Nowhere,
    /// Something else, or two elements (`several`), in the scope at
    /// this index of the chain — decided there by a declaration or an
    /// import of the one name (`fixed`), which an inserted import beside
    /// them cannot outrank, or by the namespace imports, which it can.
    Other {
        scope: usize,
        fixed: bool,
        several: bool,
    },
}

/// An import statement to insert: the byte offset, the text, the
/// root-qualified path it names when that is not the symbol's own, and
/// whether it writes that path from the global scope (`$::`).
pub(crate) struct ImportEdit {
    pub at: u32,
    pub text: String,
    pub route: Option<String>,
    pub global: bool,
}

impl ImportEdit {
    /// The path the statement names, the symbol's own being `qualified`.
    pub fn path<'a>(&'a self, qualified: &'a str) -> &'a str {
        self.route.as_deref().unwrap_or(qualified)
    }

    /// That path as the statement spells it in `dialect`.
    pub fn spelled(&self, dialect: Dialect, qualified: &str) -> String {
        let path = escape_qualified(dialect, self.path(qualified));
        if self.global {
            format!("$::{path}")
        } else {
            path
        }
    }
}

/// The cursor's syntactic surroundings: the ancestor scope chain
/// (outermost first; the unit root is always present) and the partial
/// word being completed (the phantom declaration guard).
pub(crate) struct AutoImport<'a> {
    text: &'a str,
    /// The unit's dialect: the reserved-word table an inserted import
    /// path must respect.
    dialect: Dialect,
    scopes: Vec<Scope<'a>>,
    partial: Span,
    /// What the scope chain's imports name, as the symbol tables resolve
    /// their targets, by import member start.
    targets: HashMap<u32, String>,
    /// The symbol tables, when known: they choose the imported path.
    tables: Option<&'a dyn Reexports>,
    /// Whether an inserted import starts at the global scope, by the
    /// path's first segment, once asked (see [`Self::needs`]).
    rooted: std::cell::RefCell<HashMap<String, bool>>,
    /// The paths of what the scopes around the cursor inherit, once
    /// asked (see [`Self::may_find`]).
    inherited: std::cell::OnceCell<std::collections::HashSet<String>>,
}

impl<'a> AutoImport<'a> {
    pub fn new(text: &'a str, unit: &'a SourceUnit, offset: u32, partial: Span) -> AutoImport<'a> {
        let mut scopes = vec![Scope {
            members: &unit.members,
            package: true,
            path: String::new(),
            declared: declared_in(&unit.members, partial),
        }];
        loop {
            let cur = scopes.last().unwrap();
            let next = cur.members.iter().find_map(|m| {
                if m.span.start <= offset && offset <= m.span.end {
                    let name = declared_names(&m.kind)
                        .last()
                        .copied()
                        .or_else(|| crate::outline::effective_name_of(m));
                    body_of(&m.kind).map(|b| {
                        let mut declared = declared_in(b, partial);
                        // A connection's named ends are its features too.
                        if let MemberKind::Usage(u) = &m.kind {
                            declared.extend(end_names(&u.detail));
                            declared.sort_unstable();
                            declared.dedup();
                        }
                        Scope {
                            members: b,
                            package: matches!(m.kind, MemberKind::Package(_)),
                            path: match name {
                                Some(n) if cur.path.is_empty() => n.value.clone(),
                                Some(n) => format!("{}::{}", cur.path, n.value),
                                None => cur.path.clone(),
                            },
                            declared,
                        }
                    })
                } else {
                    None
                }
            });
            match next {
                Some(s) => scopes.push(s),
                None => break,
            }
        }
        AutoImport {
            text,
            dialect: unit.dialect,
            scopes,
            partial,
            targets: HashMap::new(),
            tables: None,
            rooted: std::cell::RefCell::default(),
            inherited: std::cell::OnceCell::new(),
        }
    }

    /// Let existing imports admit what they bring in as the symbol
    /// tables know it — what an imported namespace re-exports too — and
    /// let the tables choose the path an inserted import names.
    pub fn with_reexports(mut self, tables: &'a dyn Reexports) -> Self {
        self.tables = Some(tables);
        for scope in &self.scopes {
            for m in scope.members {
                let MemberKind::Import(imp) = &m.kind else {
                    continue;
                };
                let target: Vec<String> = imp
                    .target
                    .segments
                    .iter()
                    .map(|s| s.value.clone())
                    .collect();
                if let Some(path) = tables.namespace(&scope.path, &target, imp.target.is_global) {
                    self.targets.insert(m.span.start, path);
                }
            }
        }
        self
    }

    /// What `name` (fully `qualified` from the root) needs to resolve to
    /// that symbol at the cursor: nothing when the name finds it already
    /// ([`Self::finds`]); an import when the name finds nothing, or two
    /// elements where nothing nearer the cursor than the import can go
    /// decides it — the import goes into the nearest enclosing package,
    /// where an import of the one member is found ahead of what
    /// namespace imports beside it bring in; a qualifier otherwise: an
    /// import of this symbol would take the name from every reference
    /// in that package that finds the other element by it now. The
    /// import names the symbol tables' choice of path when known — a
    /// re-exporting package's path can be the conventional one — else
    /// `qualified`.
    pub fn needs(&self, name: &str, qualified: &str) -> Needs {
        let Some(parent) = qualified
            .strip_suffix(name)
            .and_then(|p| p.strip_suffix("::"))
        else {
            return Needs::Nothing;
        };
        let at = self
            .scopes
            .iter()
            .rposition(|s| s.package)
            .expect("the unit root is always a package scope");
        match self.finds(name, parent, qualified, Admit::Any) {
            Found::It => Needs::Nothing,
            Found::Other { scope, fixed, .. } if scope > at || (scope == at && fixed) => {
                Needs::Qualifier
            }
            // The one element the name finds keeps it; a name two
            // elements make ambiguous finds nothing yet, so an import
            // only settles it.
            Found::Other { several: false, .. } => Needs::Qualifier,
            Found::Nowhere | Found::Other { .. } => {
                let route = self
                    .tables
                    .and_then(|tables| tables.import_route(name, qualified));
                let path = route.as_deref().unwrap_or(qualified);
                // An import resolves its path from where it sits: a first
                // segment a name there takes from the top-level element is
                // written from the global scope.
                let first = path.split("::").next().unwrap_or(path);
                let known = self.rooted.borrow().get(first).copied();
                let global = known.unwrap_or_else(|| {
                    let taken = matches!(
                        self.finds_from(at, first, "", first, Admit::Any),
                        Found::Other { .. }
                    );
                    self.rooted.borrow_mut().insert(first.to_string(), taken);
                    taken
                });
                let (at, text) = self.insertion(path, global);
                Needs::Import(ImportEdit {
                    at,
                    text,
                    route,
                    global,
                })
            }
        }
    }

    /// Is the cursor inside the namespace at the qualified path `ns` —
    /// in its body, or in one nested in it?
    pub fn inside(&self, ns: &str) -> bool {
        self.scopes.iter().any(|scope| {
            scope
                .path
                .strip_prefix(ns)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with("::"))
        })
    }

    /// Can `name`, fully `qualified`, which its namespace holds private
    /// or protected, be named bare at the cursor? Inside the namespace
    /// it can; elsewhere only through an `import all`, of its namespace
    /// or of one that brings it in so, as no other import brings in a
    /// member that is not public.
    pub fn sees_hidden(&self, name: &str, qualified: &str) -> bool {
        let Some(parent) = qualified
            .strip_suffix(name)
            .and_then(|p| p.strip_suffix("::"))
        else {
            return true;
        };
        matches!(self.finds(name, parent, qualified, Admit::All), Found::It)
    }

    /// Can `name`, fully `qualified`, which an ancestor's visibility
    /// keeps inside a namespace the cursor is outside of, be named bare
    /// here? Only through an import the symbol tables follow to a
    /// namespace that brings it in: its own path does not resolve here.
    pub fn sees_enclosed(&self, name: &str, qualified: &str) -> bool {
        let Some(parent) = qualified
            .strip_suffix(name)
            .and_then(|p| p.strip_suffix("::"))
        else {
            return true;
        };
        matches!(
            self.finds(name, parent, qualified, Admit::Resolved),
            Found::It
        )
    }

    /// Does `name` at the cursor find the element at `qualified`? The
    /// scope chain is read innermost first, and the first scope where
    /// the name is found decides: one declaring it (the phantom the
    /// half-typed statement introduces aside), else one whose imports
    /// bring it in, taken together ([`Self::imported`]) — the element
    /// found must be the one at `qualified`, and a name they bring in
    /// for different elements is ambiguous, finding neither. `admit`
    /// tells which imports are taken at their word.
    fn finds(&self, name: &str, parent: &str, qualified: &str, admit: Admit) -> Found {
        self.finds_from(self.scopes.len() - 1, name, parent, qualified, admit)
    }

    /// [`Self::finds`], for `name` written in the scope at index `from`
    /// of the chain.
    fn finds_from(
        &self,
        from: usize,
        name: &str,
        parent: &str,
        qualified: &str,
        admit: Admit,
    ) -> Found {
        for (i, scope) in self.scopes[..=from].iter().enumerate().rev() {
            let (found, fixed) = if scope.declared.binary_search(&name).is_ok() {
                // The member the scope declares: the symbol, if its path
                // is the scope's and the name's.
                let own = if scope.path.is_empty() {
                    parent.is_empty()
                } else {
                    parent == scope.path
                };
                let declared = if scope.path.is_empty() {
                    name.to_string()
                } else {
                    format!("{}::{name}", scope.path)
                };
                (
                    if own {
                        Brought::It
                    } else {
                        Brought::other(&declared)
                    },
                    true,
                )
            } else {
                self.imported(scope, name, parent, qualified, admit)
            };
            match found {
                Brought::Nothing => {}
                Brought::It => return Found::It,
                Brought::Else(_) | Brought::Several => {
                    return Found::Other {
                        scope: i,
                        fixed,
                        several: found == Brought::Several,
                    };
                }
            }
        }
        Found::Nowhere
    }

    /// What the imports of `scope` bring in under `name`, and whether
    /// imports naming one member (`import T::m;`, and the `T` of
    /// `import T::**;`) did: those come ahead of imports naming a
    /// namespace's members, whose names they hide. The symbol tables
    /// tell what an import whose target they resolve brings in; any
    /// other admits a name its target spells the symbol at `qualified`
    /// with, as a guess, where `admit` allows it. A filtered import — a
    /// `[…]` condition of its own, or a `filter` member beside it —
    /// admits no re-export, only its target's own members: its
    /// condition is not known here.
    fn imported(
        &self,
        scope: &Scope<'_>,
        name: &str,
        parent: &str,
        qualified: &str,
        admit: Admit,
    ) -> (Brought, bool) {
        let conditioned = scope
            .members
            .iter()
            .any(|m| matches!(m.kind, MemberKind::Filter(_)));
        let (mut one, mut members) = (Brought::Nothing, Brought::Nothing);
        for m in scope.members {
            let MemberKind::Import(imp) = &m.kind else {
                continue;
            };
            // Read off the target's spelling only when asked.
            let admits = || {
                let taken = match admit {
                    Admit::Any => true,
                    Admit::All => imp.is_import_all,
                    Admit::Resolved => false,
                };
                taken && import_admits(imp, name, parent, qualified)
            };
            let target = self.targets.get(&m.span.start).zip(self.tables);
            let filtered = !imp.filters.is_empty() || conditioned;
            if !imp.is_namespace && imp.target.segments.last().is_some_and(|s| s.value == name) {
                one.add(match target {
                    Some((path, _)) if path != qualified => Brought::other(path),
                    // A plain import of the one member brings in no
                    // private or protected member.
                    Some(_) if admit != Admit::All || imp.is_import_all => Brought::It,
                    None if admits() => Brought::It,
                    _ => Brought::Nothing,
                });
            }
            if imp.is_namespace || imp.is_recursive {
                members.add(match target {
                    Some((ns, tables)) if !filtered => {
                        tables.brought(ns, name, qualified, imp.is_recursive, imp.is_import_all)
                    }
                    _ if admits() => Brought::It,
                    _ => Brought::Nothing,
                });
            }
        }
        if one != Brought::Nothing {
            return (one, true);
        }
        // An element's own scope finds what it inherits next, ahead of
        // what namespace imports bring in.
        let inherited = match self.tables {
            Some(tables) if !scope.package && !scope.path.is_empty() => {
                tables.inherits(&scope.path, name, qualified)
            }
            _ => Brought::Nothing,
        };
        if inherited != Brought::Nothing {
            (inherited, true)
        } else {
            (members, false)
        }
    }

    /// Might `name`, of the symbol at `qualified`, a member of the type
    /// or usage at `owner`, find it at the cursor at all — declared in a
    /// scope around the cursor, inherited by one, or brought in by an
    /// import in one naming its owner, the member itself, or everything
    /// below a namespace holding it, or by one of a namespace whose
    /// imports bring it in, as the symbol tables follow them? A cheap
    /// test ahead of [`Self::needs`], which tells.
    pub fn may_find(&self, name: &str, qualified: &str, owner: &str) -> bool {
        if self.scopes.iter().any(|scope| scope.path == owner) {
            return true;
        }
        let below = |ns: &str| {
            owner
                .strip_prefix(ns)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with("::"))
        };
        let imported = self.scopes.iter().flat_map(|scope| scope.members).any(|m| {
            let (MemberKind::Import(imp), Some(target)) =
                (&m.kind, self.targets.get(&m.span.start))
            else {
                return false;
            };
            // What the target's imports bring in — through a package
            // re-exporting the member — or, recursively, what the
            // elements below it inherit.
            let brings = || {
                self.tables.is_some_and(|tables| {
                    tables.brought(target, name, qualified, imp.is_recursive, imp.is_import_all)
                        == Brought::It
                })
            };
            (imp.is_recursive && below(target))
                || (imp.is_namespace && owner == target)
                || (!imp.is_namespace && qualified == target)
                || ((imp.is_namespace || imp.is_recursive) && brings())
        });
        imported
            || self
                .inherited
                .get_or_init(|| {
                    let Some(tables) = self.tables else {
                        return std::collections::HashSet::new();
                    };
                    self.scopes
                        .iter()
                        .filter(|scope| !scope.package && !scope.path.is_empty())
                        .flat_map(|scope| tables.inherited_paths(&scope.path))
                        .collect()
                })
                .contains(qualified)
    }

    /// Where and what to insert: after the last import of the nearest
    /// enclosing package body (or the unit root), matching its
    /// indentation and visibility spelling; with no imports yet,
    /// before the first substantive member as a `private import` (the
    /// non-re-exporting default). `global` writes the path from the
    /// global scope.
    fn insertion(&self, qualified: &str, global: bool) -> (u32, String) {
        let path = escape_qualified(self.dialect, qualified);
        let path = if global { format!("$::{path}") } else { path };
        let scope = self
            .scopes
            .iter()
            .rev()
            .find(|s| s.package)
            .expect("the unit root is always a package scope");
        let last_import = scope
            .members
            .iter()
            .rfind(|m| matches!(m.kind, MemberKind::Import(_)));
        if let Some(last) = last_import {
            let vis = match last.visibility {
                Some(Visibility::Public) => "public ",
                Some(Visibility::Protected) => "protected ",
                Some(Visibility::Private) => "private ",
                None => "",
            };
            return match self.line_indent(last.span.start) {
                Some(indent) => (last.span.end, format!("\n{indent}{vis}import {path};")),
                // Import mid-line (`package P { private import A; …`):
                // stay inline.
                None => (last.span.end, format!(" {vis}import {path};")),
            };
        }
        // Leading documentation stays leading; the phantom member the
        // partial word parses as is as good an anchor as any.
        let first = scope.members.iter().find(|m| {
            !matches!(
                m.kind,
                MemberKind::Doc(_) | MemberKind::Comment(_) | MemberKind::TextualRep(_)
            )
        });
        if let Some(first) = first {
            return match self.line_indent(first.span.start) {
                Some(indent) => (
                    first.span.start,
                    format!("private import {path};\n{indent}"),
                ),
                None => (first.span.start, format!("private import {path}; ")),
            };
        }
        // Empty scope: the line holding the partial word.
        let line_start = self.text[..self.partial.start as usize]
            .rfind('\n')
            .map(|i| i + 1)
            .unwrap_or(0);
        let indent: String = self.text[line_start..]
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t')
            .collect();
        (
            offset32(line_start),
            format!("{indent}private import {path};\n"),
        )
    }

    /// The pure-whitespace line prefix before `offset`, or `None` when
    /// something substantive precedes it on its line.
    fn line_indent(&self, offset: u32) -> Option<&str> {
        let line_start = self.text[..offset as usize]
            .rfind('\n')
            .map(|i| i + 1)
            .unwrap_or(0);
        let prefix = &self.text[line_start..offset as usize];
        prefix
            .chars()
            .all(|c| c == ' ' || c == '\t')
            .then_some(prefix)
    }
}

fn overlaps(a: Span, b: Span) -> bool {
    a.start < b.end && b.start < a.end
}

/// The members list a member's body owns, through the membership
/// wrappers that carry a usage.
fn body_of(kind: &MemberKind) -> Option<&[Member]> {
    match kind {
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
        | MemberKind::RequirementConstraint { usage: u, .. } => u.body.as_deref(),
        MemberKind::StateSubaction {
            action: Some(u), ..
        } => u.body.as_deref(),
        _ => None,
    }
}

/// Is `offset` inside an import statement (at any nesting depth)? An
/// unresolved name there is already an import path — the target is
/// missing from the model, and inserting another import statement for
/// a same-named symbol elsewhere cannot make this one resolve.
pub(crate) fn within_import(members: &[Member], offset: u32) -> bool {
    members.iter().any(|m| {
        m.span.start <= offset
            && offset <= m.span.end
            && (matches!(m.kind, MemberKind::Import(_))
                || body_of(&m.kind).is_some_and(|b| within_import(b, offset)))
    })
}

/// The names `members` declare — by name, short name, or the name a
/// usage without one is found by — but where one overlaps `partial`, the
/// phantom the half-typed statement introduces.
fn declared_in(members: &[Member], partial: Span) -> Vec<&str> {
    let mut out = Vec::new();
    for m in members {
        let names = declared_names(&m.kind)
            .into_iter()
            .chain(crate::outline::effective_name_of(m));
        for n in names.filter(|n| !overlaps(n.span, partial)) {
            out.push(n.value.as_str());
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// The names of the ends a connection declares as it connects them
/// (`connect lugNut ::> wheel.lugNut to shank ::> hub.shank`).
fn end_names(detail: &sysmlv2_parser::ast::UsageDetail) -> Vec<&str> {
    use sysmlv2_parser::ast::UsageDetail as D;
    let ends: Vec<&sysmlv2_parser::ast::ConnectorEnd> = match detail {
        D::Connector { ends } | D::Binding { ends } => ends.iter().collect(),
        D::Succession { source, target } => {
            source.as_deref().into_iter().chain([&**target]).collect()
        }
        _ => Vec::new(),
    };
    ends.into_iter()
        .filter_map(|e| e.name.as_ref().map(|n| n.value.as_str()))
        .collect()
}

/// The names a member declares in its owning scope.
fn declared_names(kind: &MemberKind) -> Vec<&Name> {
    let id = match kind {
        MemberKind::Package(p) => Some(&p.id),
        MemberKind::Definition(d) => Some(&d.id),
        MemberKind::Alias(a) => Some(&a.id),
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u)
        | MemberKind::RequirementConstraint { usage: u, .. } => Some(&u.declaration.id),
        MemberKind::StateSubaction {
            action: Some(u), ..
        } => Some(&u.declaration.id),
        _ => None,
    };
    id.map(|id| id.short_name.iter().chain(id.name.iter()).collect())
        .unwrap_or_default()
}

/// Does an existing import bring `name` in? Paths compare by
/// `::`-boundary suffix in both directions — resolution is relative,
/// so the import target may be spelled more or less qualified than the
/// symbol table's root-based path. Filtered imports count as admitting
/// (a second import would duplicate, and the filter usually passes).
fn import_admits(imp: &Import, name: &str, parent: &str, qualified: &str) -> bool {
    let t = imp.target.to_display_string();
    let t = t.strip_prefix("$::").unwrap_or(&t);
    if imp.is_recursive {
        // `import T::**`: every member at any depth below T.
        return qualified
            .match_indices("::")
            .any(|(i, _)| path_matches(&qualified[..i], t));
    }
    if imp.is_namespace {
        // `import T::*`: T's direct members.
        return path_matches(parent, t);
    }
    // `import T`: the one membership named by T's last segment.
    imp.target.segments.last().is_some_and(|s| s.value == name)
}

fn path_matches(p: &str, t: &str) -> bool {
    p == t || p.ends_with(&format!("::{t}")) || t.ends_with(&format!("::{p}"))
}

/// A root-qualified path in the textual notation of `dialect`:
/// restricted names and the dialect's reserved words quoted, so the
/// import statement parses and the formatter keeps it.
pub(crate) fn escape_qualified(dialect: Dialect, qualified: &str) -> String {
    sysmlv2_parser::name::spell_path(Some(dialect), qualified.split("::"))
}

#[cfg(test)]
mod tests {
    use super::{AutoImport, offset32};
    use sysmlv2_parser::span::Span;

    /// Cursor at the end of `cursor`'s first occurrence; the partial
    /// word is its trailing identifier run.
    fn edit(text: &str, cursor: &str, name: &str, qualified: &str) -> Option<(u32, String)> {
        let at = text.find(cursor).expect("cursor needle") + cursor.len();
        let word_start = text[..at]
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map(|i| i + 1)
            .unwrap_or(0);
        let parse = sysmlv2_parser::parser::parse_source(text);
        let auto = AutoImport::new(
            text,
            &parse.unit,
            offset32(at),
            Span::new(offset32(word_start), offset32(at)),
        );
        match auto.needs(name, qualified) {
            super::Needs::Import(e) => Some((e.at, e.text)),
            super::Needs::Nothing | super::Needs::Qualifier => None,
        }
    }

    #[test]
    fn inserts_after_last_import_matching_style() {
        let text = "package P {\n    private import ISQ::*;\n    attribute v = 3 [volt];\n}\n";
        let (at, ins) = edit(text, "[volt", "volt", "SI::volt").expect("edit");
        assert_eq!(at as usize, text.find(";").unwrap() + 1);
        assert_eq!(ins, "\n    private import SI::volt;");
    }

    #[test]
    fn no_edit_when_admitted_by_existing_imports() {
        for import in [
            "import SI::*;",
            "import SI::volt;",
            "import SI::**;",
            "private import SI::*;",
        ] {
            let text = format!("package P {{\n    {import}\n    attribute v = 3 [volt];\n}}\n");
            assert_eq!(edit(&text, "[volt", "volt", "SI::volt"), None, "{import}");
        }
    }

    #[test]
    fn no_edit_when_declared_on_the_scope_chain() {
        let text = "package P {\n    attribute volt;\n    attribute v = 3 [volt];\n}\n";
        assert_eq!(edit(text, "3 [volt", "volt", "SI::volt"), None);
    }

    #[test]
    fn phantom_declaration_does_not_suppress() {
        // The fully-typed partial word parses as a declaration of the
        // very name being completed — it must not read as visible.
        let text = "package P {\n    part def X;\n    volt\n}\n";
        assert!(edit(text, "\n    volt", "volt", "SI::volt").is_some());
    }

    #[test]
    fn defaults_to_private_before_first_member() {
        let text = "package P {\n    doc /* d */\n    attribute v = 3 [volt];\n}\n";
        let (at, ins) = edit(text, "[volt", "volt", "SI::volt").expect("edit");
        assert_eq!(at as usize, text.find("attribute").unwrap());
        assert_eq!(ins, "private import SI::volt;\n    ");
    }

    #[test]
    fn import_lands_in_nearest_package_not_def_body() {
        let text = "package P {\n    private import ISQ::*;\n    part def X {\n        attribute v = 3 [volt];\n    }\n}\n";
        let (at, ins) = edit(text, "[volt", "volt", "SI::volt").expect("edit");
        assert_eq!(at as usize, text.find(";").unwrap() + 1);
        assert_eq!(ins, "\n    private import SI::volt;");
    }

    #[test]
    fn quotes_restricted_names() {
        let text = "package P {\n    attribute v = 3 [x];\n}\n";
        let (_, ins) = edit(text, "[x", "m/s", "U::m/s").expect("edit");
        assert!(ins.contains("import U::'m/s';"), "{ins}");
    }

    #[test]
    fn relative_import_spellings_admit() {
        // Import target spelled deeper than the symbol's parent.
        let text = "package P {\n    import Units::SI::*;\n    attribute v = 3 [volt];\n}\n";
        assert_eq!(edit(text, "[volt", "volt", "SI::volt"), None);
    }
}
