//! Semantic tokens: exact, dialect-aware highlighting.
//!
//! Keywords are not lexed in this language — `part` is a keyword in
//! SysML and a legal name in KerML — so no lexer or TextMate grammar can
//! classify them. The parser is the authority, and its verdict is fully
//! recoverable from what it already returns: the AST records the span of
//! **every name** (declared identifications and every qualified-name
//! segment, including inside expressions). An `Ident` token therefore
//! classifies by subtraction: inside a recorded name span it is that
//! name's role; outside every name span, a word from the keyword
//! vocabulary was consumed as a keyword. The vocabulary is generated
//! from the vendored normative grammars (`spec-refs/*.xtext`), and two
//! gates keep the scheme honest: a test regenerates the vocabulary from
//! the grammars, and the corpus sweep asserts every `Ident` in every
//! clean-parsing file classifies (a vocabulary gap cannot hide).

use crate::position::Mapper;
use lsp_types::{SemanticToken, SemanticTokenModifier, SemanticTokenType};
use std::collections::HashMap;
use sysmlv2_parser::ast::{
    DefKind, FeatureSpecialization, Identification, Member, MemberKind, QualifiedName, SourceUnit,
    TargetRef, UsageKind,
};
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};
use sysmlv2_parser::visit::{self, Visit};

/// Keyword vocabulary: every word-shaped terminal of the normative
/// grammars, both dialects (generated from `spec-refs/*.xtext`; the
/// `vocabulary_matches_the_grammars` gate regenerates and compares).
pub const VOCABULARY: &[&str] = &[
    "about",
    "abstract",
    "accept",
    "action",
    "actor",
    "after",
    "alias",
    "all",
    "allocate",
    "allocation",
    "analysis",
    "and",
    "as",
    "assert",
    "assign",
    "assoc",
    "assume",
    "at",
    "attribute",
    "behavior",
    "bind",
    "binding",
    "bool",
    "by",
    "calc",
    "case",
    "chains",
    "class",
    "classifier",
    "comment",
    "composite",
    "concern",
    "conjugate",
    "conjugates",
    "conjugation",
    "connect",
    "connection",
    "connector",
    "const",
    "constant",
    "constraint",
    "crosses",
    "datatype",
    "decide",
    "def",
    "default",
    "defined",
    "dependency",
    "derived",
    "differences",
    "disjoining",
    "disjoint",
    "do",
    "doc",
    "else",
    "end",
    "entry",
    "enum",
    "event",
    "exhibit",
    "exit",
    "expose",
    "expr",
    "false",
    "feature",
    "featured",
    "featuring",
    "filter",
    "first",
    "flow",
    "for",
    "fork",
    "frame",
    "from",
    "function",
    "hastype",
    "if",
    "implies",
    "import",
    "in",
    "include",
    "individual",
    "inout",
    "interaction",
    "interface",
    "intersects",
    "inv",
    "inverse",
    "inverting",
    "istype",
    "item",
    "join",
    "language",
    "library",
    "locale",
    "loop",
    "member",
    "merge",
    "message",
    "meta",
    "metaclass",
    "metadata",
    "multiplicity",
    "namespace",
    "new",
    "nonunique",
    "not",
    "null",
    "objective",
    "occurrence",
    "of",
    "or",
    "ordered",
    "out",
    "package",
    "parallel",
    "part",
    "perform",
    "port",
    "portion",
    "predicate",
    "private",
    "protected",
    "public",
    "redefines",
    "redefinition",
    "ref",
    "references",
    "render",
    "rendering",
    "rep",
    "require",
    "requirement",
    "return",
    "satisfy",
    "send",
    "snapshot",
    "specialization",
    "specializes",
    "stakeholder",
    "standard",
    "state",
    "step",
    "struct",
    "subclassifier",
    "subject",
    "subset",
    "subsets",
    "subtype",
    "succession",
    "terminate",
    "then",
    "timeslice",
    "to",
    "transition",
    "true",
    "type",
    "typed",
    "typing",
    "unions",
    "until",
    "use",
    "var",
    "variant",
    "variation",
    "verification",
    "verify",
    "via",
    "view",
    "viewpoint",
    "when",
    "while",
    "xor",
];

/// Legend indices — the order is the wire protocol; append only.
pub fn legend_types() -> Vec<SemanticTokenType> {
    vec![
        SemanticTokenType::NAMESPACE,   // 0
        SemanticTokenType::TYPE,        // 1
        SemanticTokenType::PROPERTY,    // 2
        SemanticTokenType::VARIABLE,    // 3
        SemanticTokenType::ENUM_MEMBER, // 4
        SemanticTokenType::KEYWORD,     // 5
        SemanticTokenType::COMMENT,     // 6
        SemanticTokenType::STRING,      // 7
        SemanticTokenType::NUMBER,      // 8
    ]
}

pub fn legend_modifiers() -> Vec<SemanticTokenModifier> {
    vec![SemanticTokenModifier::DECLARATION] // bit 0
}

const NAMESPACE: u32 = 0;
const TYPE: u32 = 1;
const PROPERTY: u32 = 2;
const VARIABLE: u32 = 3;
const ENUM_MEMBER: u32 = 4;
const KEYWORD: u32 = 5;
const COMMENT: u32 = 6;
const STRING: u32 = 7;
const NUMBER: u32 = 8;
const DECL: u32 = 1; // modifier bit

/// One classified token, pre-encoding: absolute byte span + legend index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Classified {
    pub span: Span,
    pub token_type: u32,
    pub modifiers: u32,
}

/// Classify one parsed unit's tokens. `tokens` must be the unfiltered
/// lexer output for `src` (trivia included — notes classify as comments).
pub fn classify(unit: &SourceUnit, src: &str, tokens: &[Token]) -> Vec<Classified> {
    let names = collect_name_roles(unit);
    let mut out = Vec::new();
    for t in tokens {
        let role = match t.kind {
            TokenKind::Ident | TokenKind::UnrestrictedName => {
                match names.get(&(t.span.start, t.span.end)) {
                    Some(&(ty, mods)) => Some((ty, mods)),
                    None if t.kind == TokenKind::Ident
                        && VOCABULARY.binary_search(&t.text(src)).is_ok() =>
                    {
                        Some((KEYWORD, 0))
                    }
                    // Unrecorded and not a keyword: leave uncolored (a
                    // mid-edit fragment, or recovery debris).
                    None => None,
                }
            }
            TokenKind::Decimal | TokenKind::Exp => Some((NUMBER, 0)),
            TokenKind::String => Some((STRING, 0)),
            TokenKind::RegularComment | TokenKind::LineNote | TokenKind::BlockNote => {
                Some((COMMENT, 0))
            }
            _ => None, // punctuation, whitespace, errors
        };
        if let Some((token_type, modifiers)) = role {
            out.push(Classified {
                span: t.span,
                token_type,
                modifiers,
            });
        }
    }
    out
}

/// Every recorded name span in the unit, keyed by exact span, with its
/// role. One visitor does both jobs: declaration hooks insert the
/// specific roles first (declared names with the `declaration` modifier,
/// typing/specialization targets as types, import targets as
/// namespaces), then delegate to the default walk, whose generic
/// `visit_qualified_name` fills every remaining segment as a plain
/// variable reference via `or_insert` — specific wins, and the walk's
/// totality (expressions and their lambda-parameter declarations
/// included) is what the corpus completeness gate leans on.
fn collect_name_roles(unit: &SourceUnit) -> HashMap<(u32, u32), (u32, u32)> {
    let mut v = Names {
        map: HashMap::new(),
        in_enum: false,
    };
    v.visit_unit(unit);
    v.map
}

struct Names {
    map: HashMap<(u32, u32), (u32, u32)>,
    /// Directly inside an `enum def` body (its bare literals are
    /// enum members, not features).
    in_enum: bool,
}

impl<'a> Visit<'a> for Names {
    fn visit_qualified_name(&mut self, qn: &'a QualifiedName) {
        for seg in &qn.segments {
            self.map
                .entry((seg.span.start, seg.span.end))
                .or_insert((VARIABLE, 0));
        }
    }

    fn visit_member(&mut self, m: &'a Member) {
        match &m.kind {
            MemberKind::Alias(a) => record_id(&mut self.map, &a.id, VARIABLE),
            MemberKind::Dependency(d) => record_id(&mut self.map, &d.id, VARIABLE),
            // Annotating elements: the default walk skips them (no
            // expression surface), but their ids and `about` targets are
            // names all the same.
            MemberKind::Comment(c) => {
                record_id(&mut self.map, &c.id, VARIABLE);
                for qn in &c.about {
                    self.visit_qualified_name(qn);
                }
            }
            MemberKind::Doc(d) => record_id(&mut self.map, &d.id, VARIABLE),
            MemberKind::TextualRep(r) => record_id(&mut self.map, &r.id, VARIABLE),
            // KerML standalone declarations: names outside Identification
            // reach of the other hooks.
            MemberKind::MultiplicityDecl(md) => record_id(&mut self.map, &md.id, VARIABLE),
            MemberKind::Relationship(r) => record_id(&mut self.map, &r.id, VARIABLE),
            _ => {}
        }
        visit::walk_member(self, m);
    }

    fn visit_package(&mut self, p: &'a sysmlv2_parser::ast::Package) {
        record_id(&mut self.map, &p.id, NAMESPACE);
        let prev = std::mem::replace(&mut self.in_enum, false);
        visit::walk_package(self, p);
        self.in_enum = prev;
    }

    fn visit_import(&mut self, i: &'a sysmlv2_parser::ast::Import) {
        record_qn(&mut self.map, &i.target, NAMESPACE);
        visit::walk_import(self, i);
    }

    fn visit_definition(&mut self, d: &'a sysmlv2_parser::ast::Definition) {
        record_id(&mut self.map, &d.id, TYPE);
        for t in d.specializes.iter().chain(&d.conjugates) {
            record_target(&mut self.map, t, TYPE);
        }
        let prev = std::mem::replace(&mut self.in_enum, d.kind == DefKind::Enum);
        visit::walk_definition(self, d);
        self.in_enum = prev;
    }

    /// Every feature declaration declares a name — this covers shapes no
    /// other hook sees (`end inCart[0..1] item cart : C` puts the end
    /// name in a second declaration under `prefix.end_cross`). The main
    /// usage declaration was already recorded with its specific role by
    /// `visit_usage`, so this uses or-insert semantics.
    fn visit_feature_declaration(&mut self, d: &'a sysmlv2_parser::ast::FeatureDeclaration) {
        for n in d.id.short_name.iter().chain(d.id.name.iter()) {
            self.map
                .entry((n.span.start, n.span.end))
                .or_insert((VARIABLE, DECL));
        }
        for s in &d.specializations {
            if let FeatureSpecialization::TypedBy(types) = s {
                for t in types {
                    record_target(&mut self.map, &t.target, TYPE);
                }
            }
        }
        visit::walk_feature_declaration(self, d);
    }

    fn visit_connector_end(&mut self, e: &'a sysmlv2_parser::ast::ConnectorEnd) {
        if let Some(n) = &e.name {
            self.map
                .insert((n.span.start, n.span.end), (VARIABLE, DECL));
        }
        visit::walk_connector_end(self, e);
    }

    fn visit_payload(&mut self, p: &'a sysmlv2_parser::ast::PayloadPart) {
        record_id(&mut self.map, &p.id, VARIABLE);
        for s in &p.specializations {
            if let FeatureSpecialization::TypedBy(types) = s {
                for t in types {
                    record_target(&mut self.map, &t.target, TYPE);
                }
            }
        }
        visit::walk_payload(self, p);
    }

    fn visit_usage(&mut self, u: &'a sysmlv2_parser::ast::Usage) {
        let ty = if self.in_enum && matches!(u.kind, UsageKind::Default | UsageKind::Enum) {
            ENUM_MEMBER
        } else {
            match u.kind {
                UsageKind::Attribute => PROPERTY,
                UsageKind::Enum => ENUM_MEMBER,
                _ => VARIABLE,
            }
        };
        record_id(&mut self.map, &u.declaration.id, ty);
        for s in &u.declaration.specializations {
            if let FeatureSpecialization::TypedBy(types) = s {
                for t in types {
                    record_target(&mut self.map, &t.target, TYPE);
                }
            }
        }
        let prev = std::mem::replace(&mut self.in_enum, false);
        visit::walk_usage(self, u);
        self.in_enum = prev;
    }
}

fn record_id(map: &mut HashMap<(u32, u32), (u32, u32)>, id: &Identification, ty: u32) {
    for n in id.short_name.iter().chain(id.name.iter()) {
        map.insert((n.span.start, n.span.end), (ty, DECL));
    }
}

fn record_target(map: &mut HashMap<(u32, u32), (u32, u32)>, t: &TargetRef, ty: u32) {
    if let TargetRef::Name(qn) = t {
        for seg in &qn.segments {
            map.insert((seg.span.start, seg.span.end), (ty, 0));
        }
    }
    // Chains stay generic: `a.b.c` links are features, not types.
}

fn record_qn(map: &mut HashMap<(u32, u32), (u32, u32)>, qn: &QualifiedName, ty: u32) {
    for seg in &qn.segments {
        map.insert((seg.span.start, seg.span.end), (ty, 0));
    }
}

/// Encode classified tokens as the LSP wire format: sorted, multi-line
/// comments split per line (multiline tokens need a client capability we
/// don't assume), lengths in the negotiated encoding's units.
pub fn encode(mut toks: Vec<Classified>, src: &str, mapper: &Mapper<'_>) -> Vec<SemanticToken> {
    toks.sort_by_key(|t| t.span.start);
    let mut out = Vec::with_capacity(toks.len());
    let (mut prev_line, mut prev_char) = (0u32, 0u32);
    let mut push = |span: Span, token_type: u32, modifiers: u32| {
        let start = mapper.position(span.start);
        let end = mapper.position(span.end);
        debug_assert_eq!(start.line, end.line, "encode() takes single-line spans");
        let delta_line = start.line - prev_line;
        let delta_start = if delta_line == 0 {
            start.character - prev_char
        } else {
            start.character
        };
        out.push(SemanticToken {
            delta_line,
            delta_start,
            length: end.character - start.character,
            token_type,
            token_modifiers_bitset: modifiers,
        });
        (prev_line, prev_char) = (start.line, start.character);
    };
    for t in toks {
        let text = t.span.slice(src);
        if text.contains('\n') {
            let mut line_start = t.span.start;
            for line in text.split('\n') {
                let line_end = line_start + line.len() as u32;
                if line_start < line_end {
                    push(Span::new(line_start, line_end), t.token_type, t.modifiers);
                }
                line_start = line_end + 1; // past the '\n'
            }
        } else {
            push(t.span, t.token_type, t.modifiers);
        }
    }
    out
}

/// Convenience: how many `Ident` tokens failed to classify (the corpus
/// completeness gate — 0 on clean-parsing files).
pub fn unclassified_idents(unit: &SourceUnit, src: &str, tokens: &[Token]) -> Vec<Span> {
    let names = collect_name_roles(unit);
    tokens
        .iter()
        .filter(|t| {
            t.kind == TokenKind::Ident
                && !names.contains_key(&(t.span.start, t.span.end))
                && VOCABULARY.binary_search(&t.text(src)).is_err()
        })
        .map(|t| t.span)
        .collect()
}

/// The unfiltered token stream for one text (lexer output, trivia kept).
pub fn lex(src: &str) -> Vec<Token> {
    sysmlv2_parser::lexer::tokenize(src).0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vocabulary_is_sorted_for_binary_search() {
        assert!(VOCABULARY.windows(2).all(|w| w[0] < w[1]));
    }
}
