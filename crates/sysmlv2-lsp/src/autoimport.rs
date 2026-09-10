//! Auto-import support for completion: when a completion offers
//! a symbol by simple name that would not resolve at the cursor — a
//! library unit like `SI::volt`, a package member declared elsewhere in
//! the workspace — accepting the item should also insert the `import`
//! that makes the name resolve, the way code editors update imports on
//! accepting an out-of-scope completion.
//!
//! Everything here is syntax-tier over the current document, matching
//! the completion path's cost model (no per-keystroke model build).
//! Visibility is therefore approximate in a deliberate direction:
//! only *provably present* names (a declaration or an admitting import
//! in the cursor's scope chain) suppress the edit, and the analysis
//! cannot see inheritance — a name visible only through a
//! specialization still gets an import offered. That import is
//! redundant, never wrong: the qualified target resolves from the root
//! namespace regardless.

use sysmlv2_parser::ast::{Import, Member, MemberKind, Name, SourceUnit, Visibility, escape_name};
use sysmlv2_parser::span::Span;

/// One namespace body on the cursor's ancestor chain.
struct Scope<'a> {
    members: &'a [Member],
    /// A package/namespace body (or the unit root) — somewhere an
    /// import statement conventionally belongs.
    package: bool,
}

/// The cursor's syntactic surroundings: the ancestor scope chain
/// (outermost first; the unit root is always present) and the partial
/// word being completed (the phantom declaration guard).
pub(crate) struct AutoImport<'a> {
    text: &'a str,
    scopes: Vec<Scope<'a>>,
    partial: Span,
}

impl<'a> AutoImport<'a> {
    pub fn new(text: &'a str, unit: &'a SourceUnit, offset: u32, partial: Span) -> AutoImport<'a> {
        let mut scopes = vec![Scope {
            members: &unit.members,
            package: true,
        }];
        loop {
            let cur = scopes.last().unwrap().members;
            let next = cur.iter().find_map(|m| {
                if m.span.start <= offset && offset <= m.span.end {
                    body_of(&m.kind).map(|b| Scope {
                        members: b,
                        package: matches!(m.kind, MemberKind::Package(_)),
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
            scopes,
            partial,
        }
    }

    /// The import edit that makes `name` (fully `qualified` from the
    /// root) resolve at the cursor: `None` when the name is already
    /// visible — declared on the scope chain or admitted by an
    /// existing import — otherwise the byte offset and text of the
    /// statement to insert.
    pub fn import_edit(&self, name: &str, qualified: &str) -> Option<(u32, String)> {
        let parent = qualified
            .strip_suffix(name)
            .and_then(|p| p.strip_suffix("::"))?;
        if self.visible(name, parent, qualified) {
            return None;
        }
        Some(self.insertion(qualified))
    }

    /// Is `name` provably visible at the cursor? Declarations exactly
    /// at the partial word are the phantom the half-typed statement
    /// itself introduces and do not count.
    fn visible(&self, name: &str, parent: &str, qualified: &str) -> bool {
        for scope in &self.scopes {
            for m in scope.members {
                if declared_names(&m.kind)
                    .iter()
                    .any(|n| n.value == name && !overlaps(n.span, self.partial))
                {
                    return true;
                }
                if let MemberKind::Import(imp) = &m.kind {
                    if import_admits(imp, name, parent, qualified) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Where and what to insert: after the last import of the nearest
    /// enclosing package body (or the unit root), matching its
    /// indentation and visibility spelling; with no imports yet,
    /// before the first substantive member as a `private import` (the
    /// non-re-exporting default).
    fn insertion(&self, qualified: &str) -> (u32, String) {
        let path = escape_qualified(qualified);
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
            line_start as u32,
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

/// A root-qualified path in textual notation, restricted names quoted.
pub(crate) fn escape_qualified(qualified: &str) -> String {
    qualified
        .split("::")
        .map(escape_name)
        .collect::<Vec<_>>()
        .join("::")
}

/// The byte range a completion for `name` should replace. The partial
/// word is the trailing identifier run, but a restricted name like
/// `m/s²` spans word-breaking characters — a typed `m/s` must be
/// replaced whole, so the range extends backward over characters that
/// belong to the candidate's own spelling (self-limiting: `3*m` stops
/// at the `*` no unit name contains). A typed opening quote joins the
/// range so accepting `'m/s²'` never doubles it.
pub(crate) fn replace_range_for(text: &str, partial_start: u32, offset: u32, name: &str) -> Span {
    let mut start = partial_start as usize;
    while let Some(prev) = text[..start].chars().next_back() {
        if prev.is_whitespace() || prev == '\'' || !name.contains(prev) {
            break;
        }
        start -= prev.len_utf8();
    }
    if text[..start].ends_with('\'') {
        start -= 1;
    }
    Span::new(start as u32, offset)
}

#[cfg(test)]
mod tests {
    use super::AutoImport;
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
            at as u32,
            Span::new(word_start as u32, at as u32),
        );
        auto.import_edit(name, qualified)
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
