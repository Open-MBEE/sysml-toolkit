//! Textual-notation printer and formatter.
//!
//! [`print_source`] renders an AST back to canonical `.sysml` / `.kerml`
//! text. [`format_source`] is the formatter: parse, then print with *layout
//! preservation* — notes (`// …`, `//* … */`) are re-attached from the
//! original token stream and single blank lines between members survive.
//!
//! Canonical style: four-space indentation, one member per line, `{` on the
//! declaration line, multiplicities after the typing clause, symbolic
//! specialization operators (`:>`, `:>>`, `::>`), `/* … */` bodies kept
//! verbatim.
//!
//! Guarantees (enforced by `tests/format.rs` over the whole corpus):
//! * semantic preservation — `parse(format(x))` equals `parse(x)` as ASTs
//!   (modulo spans);
//! * idempotency — `format(format(x)) == format(x)`.

use crate::ast::*;
use crate::diag::Diagnostics;
use crate::parser::parse_expression;
use crate::span::{LineIndex, Span};

/// Indentation style for printed text. The canonical style (and the
/// default everywhere) is four spaces; hosts whose files are
/// tab-indented can ask for tabs instead — the choice is presentation
/// only and never affects parsing or identity.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Indent {
    Spaces(u8),
    Tabs,
}

impl Default for Indent {
    fn default() -> Self {
        Indent::Spaces(4)
    }
}

impl Indent {
    fn unit(self) -> String {
        match self {
            Indent::Spaces(n) => " ".repeat(n as usize),
            Indent::Tabs => "\t".to_string(),
        }
    }
}

/// Printing knobs beyond the canonical defaults.
#[derive(Clone, Copy, Default)]
pub struct PrintOptions {
    pub indent: Indent,
    /// Re-lay multi-line `doc`/`comment` bodies as a `*`-guttered block
    /// at the printed depth. For bodies that arrive *dedented* — lifted
    /// from interchange, where `processCommentBody` already stripped
    /// the original margins — the layout inverts back to the same body
    /// on re-emission. Never set for parsed sources: their bodies are
    /// verbatim and must stay so.
    pub reflow_doc_bodies: bool,
    /// Break a body result expression whose logical chain (`and`,
    /// `or`, `xor`, `implies`, `&`, `|`) has at least this many
    /// operands onto one condition per line, continuation lines led
    /// by the operator. `None` keeps chains inline (the canonical
    /// serialization default); the formatter turns this on.
    pub multiline_chains: Option<u8>,
}

/// The formatter's default chain threshold: a two-operand chain stays
/// inline, three or more break one condition per line.
pub const FORMAT_CHAIN_MIN: u8 = 3;

/// Print an AST as canonical textual notation (no source layout available:
/// notes are gone — they are trivia — and members are single-spaced).
#[must_use]
pub fn print_source(unit: &SourceUnit) -> String {
    print_source_with(unit, Indent::default())
}

/// [`print_source`] with an explicit indentation style.
#[must_use]
pub fn print_source_with(unit: &SourceUnit, indent: Indent) -> String {
    print_source_opts(
        unit,
        PrintOptions {
            indent,
            ..PrintOptions::default()
        },
    )
}

/// [`print_source`] with explicit [`PrintOptions`].
#[must_use]
pub fn print_source_opts(unit: &SourceUnit, opts: PrintOptions) -> String {
    let mut p = Printer::new_opts(unit.dialect, None, opts);
    p.print_unit(unit);
    p.finish()
}

/// The query formatter's default line width: past this, an expression's
/// `->` chain steps and invocation arguments break one per line.
pub const FORMAT_QUERY_WIDTH: usize = 80;

/// Format one standalone expression — a query document's statement,
/// which is an expression rather than a model unit, so [`format_source`]
/// (which parses a whole namespace) does not apply. Parses, then prints
/// with `->` chain steps, invocation arguments, and lambda-body results
/// broken one per line wherever the flat form would run past `width`;
/// anything that fits stays on one line. Fails on input that is not a
/// single well-formed expression — a formatter must not guess at broken
/// input.
pub fn format_expression(
    src: &str,
    dialect: Dialect,
    indent: Indent,
    width: usize,
) -> Result<String, Diagnostics> {
    let parse = parse_expression(src);
    if !parse.diagnostics.is_empty() {
        return Err(parse.diagnostics.into());
    }
    let Some(e) = parse.expr else {
        return Err(Diagnostics::default());
    };
    let mut p = Printer::new_opts(
        dialect,
        None,
        PrintOptions {
            indent,
            ..PrintOptions::default()
        },
    );
    p.print_expr_wrapped(&e, width);
    let mut out = p.finish();
    while out.ends_with('\n') {
        out.pop();
    }
    Ok(out)
}

/// Print one expression as canonical textual notation — diagram labels,
/// diagnostics. Bodied expressions may span lines; callers that need a
/// single line collapse the whitespace themselves.
#[must_use]
pub fn print_expr_source(e: &Expr, dialect: Dialect) -> String {
    let mut p = Printer::new(dialect, None);
    p.print_expr(e, 0);
    let mut out = p.out;
    while out.ends_with('\n') {
        out.pop();
    }
    out
}

/// Format source text: parse (with the dialect's grammar), then re-print
/// preserving notes and single blank lines. Fails if the source has parse
/// diagnostics — a formatter must not guess at broken input.
pub fn format_source(src: &str, dialect: Dialect) -> Result<String, Diagnostics> {
    format_source_with(src, dialect, Indent::default())
}

/// [`format_source`] with an explicit indentation style.
pub fn format_source_with(
    src: &str,
    dialect: Dialect,
    indent: Indent,
) -> Result<String, Diagnostics> {
    // The formatter (unlike the canonical serializer) breaks long
    // logical chains one condition per line by default.
    format_source_opts(
        src,
        dialect,
        PrintOptions {
            indent,
            multiline_chains: Some(FORMAT_CHAIN_MIN),
            ..PrintOptions::default()
        },
    )
}

/// [`format_source`] with explicit [`PrintOptions`] — hosts that read
/// project style configuration (the `multiline-conditions` lint
/// rule's `min` option) pass their chain threshold here.
pub fn format_source_opts(
    src: &str,
    dialect: Dialect,
    opts: PrintOptions,
) -> Result<String, Diagnostics> {
    let (parse, notes) = crate::parser::parse_with_notes(src, dialect);
    if !parse.diagnostics.is_empty() {
        return Err(parse.diagnostics.into());
    }
    let layout = Layout::with_notes(src, notes);
    let mut p = Printer::new_opts(dialect, Some(layout), opts);
    p.print_unit(&parse.unit);
    Ok(p.finish())
}

/// Source-layout info used by the formatter: note tokens and line numbers.
struct Layout {
    lines: LineIndex,
    /// Note tokens (span, raw text), in source order.
    notes: Vec<(Span, String)>,
}

impl Layout {
    /// The notes come from the parse: they are the trivia the parser has
    /// already seen, so the formatter never lexes the file a second time.
    fn with_notes(src: &str, notes: Vec<(Span, String)>) -> Self {
        Layout {
            lines: LineIndex::new(src),
            notes,
        }
    }

    fn line(&self, offset: u32) -> u32 {
        self.lines.line_col(offset).line
    }
}

struct Printer {
    out: String,
    depth: usize,
    dialect: Dialect,
    layout: Option<Layout>,
    /// One level of indentation, per the requested [`Indent`] style.
    indent: String,
    /// Re-lay dedented multi-line doc/comment bodies (lift printing).
    reflow_doc_bodies: bool,
    /// Break long logical chains in result position (formatter style).
    multiline_chains: Option<u8>,
    /// Next unemitted note index.
    note_pos: usize,
    /// Source line of the last emitted member/note (blank-line preservation).
    prev_line: Option<u32>,
}

impl Printer {
    fn new(dialect: Dialect, layout: Option<Layout>) -> Self {
        Self::new_opts(dialect, layout, PrintOptions::default())
    }

    fn new_opts(dialect: Dialect, layout: Option<Layout>, opts: PrintOptions) -> Self {
        Printer {
            out: String::new(),
            depth: 0,
            dialect,
            layout,
            indent: opts.indent.unit(),
            reflow_doc_bodies: opts.reflow_doc_bodies,
            multiline_chains: opts.multiline_chains,
            note_pos: 0,
            prev_line: None,
        }
    }

    fn finish(mut self) -> String {
        self.flush_notes(u32::MAX);
        // Exactly one trailing newline.
        while self.out.ends_with('\n') {
            self.out.pop();
        }
        if !self.out.is_empty() {
            self.out.push('\n');
        }
        self.out
    }

    fn kerml(&self) -> bool {
        self.dialect == Dialect::Kerml
    }

    fn push_indent(&mut self) {
        for _ in 0..self.depth {
            self.out.push_str(&self.indent);
        }
    }

    fn w(&mut self, s: &str) {
        self.out.push_str(s);
    }

    // ---- layout: notes and blank lines ----

    /// Emit a blank line if the original had one before source line `line`.
    fn blank_before(&mut self, line: u32) {
        if let Some(prev) = self.prev_line {
            if line > prev + 1 {
                self.out.push('\n');
            }
        }
        self.prev_line = Some(line);
    }

    /// Emit every note that starts before `before` on its own line.
    fn flush_notes(&mut self, before: u32) {
        loop {
            let Some(layout) = &self.layout else { return };
            if self.note_pos >= layout.notes.len() || layout.notes[self.note_pos].0.start >= before
            {
                return;
            }
            let (span, text) = layout.notes[self.note_pos].clone();
            let line = layout.line(span.start);
            let end_line = layout.line(span.end.saturating_sub(1));
            self.note_pos += 1;
            self.blank_before(line);
            self.push_indent();
            self.w(&text);
            self.out.push('\n');
            self.prev_line = Some(end_line);
        }
    }

    /// After a member ends at source offset `end`: emit a same-line trailing
    /// note if the next note starts on the same source line.
    fn trailing_note(&mut self, end: u32) {
        let Some(layout) = &self.layout else { return };
        if self.note_pos >= layout.notes.len() {
            return;
        }
        let (span, _) = layout.notes[self.note_pos];
        if span.start >= end && layout.line(span.start) == layout.line(end.saturating_sub(1)) {
            let text = layout.notes[self.note_pos].1.clone();
            self.note_pos += 1;
            // Replace the trailing newline with " <note>\n".
            if self.out.ends_with('\n') {
                self.out.pop();
            }
            self.w(" ");
            self.w(&text);
            self.out.push('\n');
        }
    }

    // ---- structure ----

    fn print_unit(&mut self, unit: &SourceUnit) {
        for member in &unit.members {
            self.print_member(member);
        }
    }

    fn print_member(&mut self, m: &Member) {
        self.flush_notes(m.span.start);
        if let Some(layout) = &self.layout {
            let line = layout.line(m.span.start);
            let end_line = layout.line(m.span.end.saturating_sub(1));
            self.blank_before(line);
            self.prev_line = Some(end_line);
        }
        self.push_indent();
        if let Some(v) = m.visibility {
            self.w(match v {
                Visibility::Public => "public ",
                Visibility::Private => "private ",
                Visibility::Protected => "protected ",
            });
        }
        if m.leading_then {
            self.w("then ");
            if let Some(mult) = &m.leading_then_multiplicity {
                self.print_multiplicity(mult);
                self.w(" ");
            }
        }
        self.print_member_kind(&m.kind, m.span);
        self.trailing_note(m.span.end);
    }

    fn print_member_kind(&mut self, kind: &MemberKind, span: Span) {
        match kind {
            MemberKind::Package(p) => self.print_package(p, span),
            MemberKind::Import(imp) => self.print_import("import", imp),
            MemberKind::Expose(imp) => self.print_import("expose", imp),
            MemberKind::Alias(a) => {
                self.w("alias ");
                self.print_identification(&a.id);
                self.w("for ");
                self.print_qn(&a.target);
                self.line_end();
            }
            MemberKind::Filter(e) => {
                self.w("filter ");
                self.print_expr(e, 0);
                self.line_end();
            }
            MemberKind::Comment(c) => {
                if !c.id.is_empty() || !c.about.is_empty() {
                    self.w("comment ");
                    self.print_identification(&c.id);
                    if !c.about.is_empty() {
                        self.w("about ");
                        for (i, qn) in c.about.iter().enumerate() {
                            if i > 0 {
                                self.w(", ");
                            }
                            self.print_qn(qn);
                        }
                        self.w(" ");
                    }
                }
                if let Some(locale) = &c.locale {
                    self.w("locale ");
                    self.print_string(locale);
                    self.w(" ");
                }
                self.print_comment_body(&c.body, true);
            }
            MemberKind::Doc(d) => {
                self.w("doc ");
                self.print_identification(&d.id);
                if let Some(locale) = &d.locale {
                    self.w("locale ");
                    self.print_string(locale);
                    self.w(" ");
                }
                self.print_comment_body(&d.body, true);
            }
            MemberKind::TextualRep(r) => {
                if !r.id.is_empty() {
                    self.w("rep ");
                    self.print_identification(&r.id);
                }
                self.w("language ");
                self.print_string(&r.language);
                self.w(" ");
                self.print_comment_body(&r.body, false);
            }
            MemberKind::Dependency(d) => {
                self.print_metadata_prefixes(&d.metadata);
                self.w("dependency ");
                if !d.id.is_empty() {
                    self.print_identification(&d.id);
                    self.w("from ");
                }
                for (i, c) in d.clients.iter().enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    self.print_qn(c);
                }
                self.w(" to ");
                for (i, s) in d.suppliers.iter().enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    self.print_qn(s);
                }
                self.line_end();
            }
            MemberKind::Definition(d) => self.print_definition(d, span),
            MemberKind::Usage(u) => self.print_usage(u, span),
            MemberKind::InitialNode(qn) => {
                self.w("first ");
                self.print_qn(qn);
                self.line_end();
            }
            MemberKind::Subject(u) => self.print_wrapped_usage("subject", u, span),
            MemberKind::Actor(u) => self.print_wrapped_usage("actor", u, span),
            MemberKind::Stakeholder(u) => self.print_wrapped_usage("stakeholder", u, span),
            MemberKind::Objective(u) => self.print_wrapped_usage("objective", u, span),
            MemberKind::RequirementConstraint { kind, usage } => {
                self.w(match kind {
                    RequirementConstraintKind::Assumption => "assume",
                    RequirementConstraintKind::Requirement => "require",
                });
                self.print_ref_or_kind_tail(usage, "constraint", span);
            }
            MemberKind::FramedConcern(u) => {
                self.w("frame");
                self.print_ref_or_kind_tail(u, "concern", span);
            }
            MemberKind::RequirementVerification(u) => {
                self.w("verify");
                self.print_ref_or_kind_tail(u, "requirement", span);
            }
            MemberKind::Render(u) => {
                self.w("render");
                self.print_ref_or_kind_tail(u, "rendering", span);
            }
            MemberKind::StateSubaction { kind, action } => {
                self.w(match kind {
                    StateSubactionKind::Entry => "entry",
                    StateSubactionKind::Do => "do",
                    StateSubactionKind::Exit => "exit",
                });
                match action {
                    None => self.line_end(),
                    Some(u) => {
                        self.w(" ");
                        self.print_performed_action(u, span, true);
                    }
                }
            }
            MemberKind::Return(u) => {
                self.w("return ");
                self.print_usage(u, span);
            }
            MemberKind::Result(e) => {
                if !self.try_print_multiline_chain(e) {
                    self.print_expr(e, 0);
                }
                self.out.push('\n');
            }
            MemberKind::Relationship(r) => self.print_relationship(r),
            MemberKind::MultiplicityDecl(m) => {
                self.w("multiplicity ");
                self.print_identification(&m.id);
                if let Some(subsets) = &m.subsets {
                    self.w("subsets ");
                    self.print_target(subsets);
                } else if let Some(range) = &m.range {
                    self.print_multiplicity(range);
                }
                self.print_body(&m.body, span);
            }
        }
    }

    fn line_end(&mut self) {
        self.w(";");
        self.out.push('\n');
    }

    fn print_package(&mut self, p: &Package, span: Span) {
        if p.is_standard {
            self.w("standard ");
        }
        if p.is_library {
            self.w("library ");
        }
        self.print_metadata_prefixes(&p.metadata);
        self.w(if p.is_namespace {
            "namespace "
        } else {
            "package "
        });
        self.print_identification(&p.id);
        self.trim_trailing_space();
        self.print_body(&p.body, span);
    }

    fn print_import(&mut self, kw: &str, imp: &Import) {
        self.w(kw);
        self.w(" ");
        if imp.is_import_all {
            self.w("all ");
        }
        self.print_qn(&imp.target);
        if imp.is_namespace {
            self.w("::*");
        }
        if imp.is_recursive {
            self.w("::**");
        }
        for f in &imp.filters {
            self.w("[");
            self.print_expr(f, 0);
            self.w("]");
        }
        self.line_end();
    }

    /// `reflow` marks bodies the emit-side normalization processes
    /// (`doc`/`comment`); `rep` bodies emit raw into interchange, so
    /// reflowing them would not invert — they stay verbatim always.
    fn print_comment_body(&mut self, body: &str, reflow: bool) {
        // Only indentation so far on this line (an anonymous `/* … */`
        // member): keep it. Trimming here used to eat the pushed indent
        // and flush such comments to column 0.
        let line_start = self.out.rfind('\n').map_or(0, |i| i + 1);
        if !self.out[line_start..].trim().is_empty() {
            self.trim_trailing_space();
            // `comment <id>` etc. already emitted: keep the body on the line.
            self.w(" ");
        }
        if reflow && self.reflow_doc_bodies && body.contains('\n') {
            self.print_reflowed_body(body);
            return;
        }
        self.w("/*");
        self.w(body);
        self.w("*/");
        self.out.push('\n');
    }

    /// A dedented multi-line body as a `*`-guttered block at the current
    /// depth. The shape is chosen so the emit-side body normalization
    /// (leading whitespace + `* ` margin stripped per line, to a
    /// fixpoint) recovers the input exactly — including the presence or
    /// absence of a trailing newline.
    fn print_reflowed_body(&mut self, body: &str) {
        let ends_nl = body.ends_with('\n');
        let content = if ends_nl {
            &body[..body.len() - 1]
        } else {
            body
        };
        self.w("/*\n");
        let lines: Vec<&str> = content.split('\n').collect();
        for (i, line) in lines.iter().enumerate() {
            self.push_indent();
            if line.is_empty() {
                self.w(" *");
            } else {
                self.w(" * ");
                self.w(line);
            }
            if i + 1 < lines.len() {
                self.w("\n");
            } else if ends_nl {
                self.w("\n");
                self.push_indent();
                self.w(" */");
            } else {
                // No trailing newline in the body: `*/` closes on the
                // content line, so no empty last line is invented.
                self.w("*/");
            }
        }
        self.out.push('\n');
    }

    /// Drop the spaces a member left at the end of the line — but never
    /// the indentation it opened the line with, so a member that spells
    /// little or nothing still sits where it belongs.
    fn trim_trailing_space(&mut self) {
        let line = self.out.rfind('\n').map_or(0, |i| i + 1);
        let floor = self.out.len() - self.out[line..].trim_start_matches(' ').len();
        while self.out.len() > floor && self.out.ends_with(' ') {
            self.out.pop();
        }
    }

    // ---- names ----

    fn print_name(&mut self, name: &Name) {
        // Reserved words print as quoted restricted names even though
        // they are lexically basic (`<in>` inch, `'frame'`, …); the
        // spelling is the canonical one `name::canonical_name` answers.
        let spelling = crate::name::spell_name(self.dialect, &name.value);
        self.w(&spelling);
    }

    fn print_identification(&mut self, id: &Identification) {
        if let Some(short) = &id.short_name {
            self.w("<");
            self.print_name(short);
            self.w("> ");
        }
        if let Some(name) = &id.name {
            self.print_name(name);
            self.w(" ");
        }
    }

    fn print_qn(&mut self, qn: &QualifiedName) {
        if qn.is_global {
            self.w("$::");
        }
        for (i, seg) in qn.segments.iter().enumerate() {
            if i > 0 {
                self.w("::");
            }
            self.print_name(seg);
        }
    }

    fn print_target(&mut self, t: &TargetRef) {
        match t {
            TargetRef::Name(qn) => self.print_qn(qn),
            TargetRef::Chain(links) => {
                for (i, link) in links.iter().enumerate() {
                    if i > 0 {
                        self.w(".");
                    }
                    self.print_qn(link);
                }
            }
        }
    }

    fn print_string(&mut self, s: &str) {
        self.w("\"");
        for c in s.chars() {
            match c {
                '\u{0008}' => self.w("\\b"),
                '\t' => self.w("\\t"),
                '\n' => self.w("\\n"),
                '\u{000C}' => self.w("\\f"),
                '\r' => self.w("\\r"),
                '"' => self.w("\\\""),
                '\\' => self.w("\\\\"),
                c => self.out.push(c),
            }
        }
        self.w("\"");
    }

    fn print_metadata_prefixes(&mut self, metadata: &[QualifiedName]) {
        for m in metadata {
            self.w("#");
            self.print_qn(m);
            self.w(" ");
        }
    }

    // ---- definitions ----

    fn def_keyword(kind: DefKind) -> &'static str {
        match kind {
            DefKind::Attribute => "attribute def",
            DefKind::Enum => "enum def",
            DefKind::Occurrence => "occurrence def",
            DefKind::Individual => "individual def",
            DefKind::Item => "item def",
            DefKind::Metadata => "metadata def",
            DefKind::Part => "part def",
            DefKind::Port => "port def",
            DefKind::Connection => "connection def",
            DefKind::Interface => "interface def",
            DefKind::Allocation => "allocation def",
            DefKind::Flow => "flow def",
            DefKind::Action => "action def",
            DefKind::State => "state def",
            DefKind::Calc => "calc def",
            DefKind::Constraint => "constraint def",
            DefKind::Requirement => "requirement def",
            DefKind::Concern => "concern def",
            DefKind::Case => "case def",
            DefKind::Analysis => "analysis def",
            DefKind::Verification => "verification def",
            DefKind::UseCase => "use case def",
            DefKind::View => "view def",
            DefKind::Viewpoint => "viewpoint def",
            DefKind::Rendering => "rendering def",
            DefKind::Extended => "def",
            DefKind::Type => "type",
            DefKind::Classifier => "classifier",
            DefKind::Class => "class",
            DefKind::Struct => "struct",
            DefKind::DataType => "datatype",
            DefKind::Assoc => "assoc",
            DefKind::AssocStruct => "assoc struct",
            DefKind::Behavior => "behavior",
            DefKind::Interaction => "interaction",
            DefKind::Function => "function",
            DefKind::Predicate => "predicate",
            DefKind::Metaclass => "metaclass",
        }
    }

    fn print_definition(&mut self, d: &Definition, span: Span) {
        if d.prefix.is_abstract {
            self.w("abstract ");
        }
        if d.prefix.is_variation {
            self.w("variation ");
        }
        if d.prefix.is_individual && d.kind != DefKind::Individual {
            self.w("individual ");
        }
        self.print_metadata_prefixes(&d.prefix.metadata);
        self.w(Self::def_keyword(d.kind));
        self.w(" ");
        if d.is_sufficient {
            self.w("all ");
        }
        self.print_identification(&d.id);
        if let Some(mult) = &d.multiplicity {
            self.trim_trailing_space();
            self.print_multiplicity(mult);
            self.w(" ");
        }
        if !d.specializes.is_empty() {
            self.w(":> ");
            self.print_target_list(&d.specializes);
            self.w(" ");
        }
        if !d.conjugates.is_empty() {
            self.w("~ ");
            self.print_target_list(&d.conjugates);
            self.w(" ");
        }
        for (kw, list) in [
            ("disjoint from", &d.disjoint_from),
            ("unions", &d.unions),
            ("intersects", &d.intersects),
            ("differences", &d.differences),
        ] {
            if !list.is_empty() {
                self.w(kw);
                self.w(" ");
                self.print_target_list(list);
                self.w(" ");
            }
        }
        if d.is_parallel {
            self.w("parallel ");
        }
        self.trim_trailing_space();
        self.print_body(&d.body, span);
    }

    fn print_target_list(&mut self, list: &[TargetRef]) {
        for (i, t) in list.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            self.print_target(t);
        }
    }

    // ---- usages ----

    fn print_usage_prefix(&mut self, p: &UsagePrefix) {
        if p.is_variant {
            self.w("variant ");
        }
        if p.is_type_member {
            self.w("member ");
        }
        if let Some(dir) = p.direction {
            self.w(match dir {
                FeatureDirection::In => "in ",
                FeatureDirection::Out => "out ",
                FeatureDirection::InOut => "inout ",
            });
        }
        if p.is_derived {
            self.w("derived ");
        }
        if p.is_abstract {
            self.w("abstract ");
        }
        if p.is_variation {
            self.w("variation ");
        }
        if p.is_composite {
            self.w("composite ");
        }
        if p.is_portion {
            self.w("portion ");
        }
        if p.is_variable {
            self.w("var ");
        }
        if p.is_constant {
            self.w(if self.kerml() { "const " } else { "constant " });
        }
        if p.is_end {
            self.w("end ");
            if let Some(cross) = &p.end_cross {
                self.print_cross_feature(cross);
            }
        }
        if p.is_ref {
            self.w("ref ");
        }
        if p.is_individual {
            self.w("individual ");
        }
        if let Some(portion) = p.portion {
            self.w(match portion {
                PortionKind::Snapshot => "snapshot ",
                PortionKind::Timeslice => "timeslice ",
            });
        }
        self.print_metadata_prefixes(&p.metadata);
    }

    /// The cross feature after an `end` prefix: its own basic prefix, then
    /// its declaration.
    fn print_cross_feature(&mut self, c: &CrossFeature) {
        if let Some(dir) = c.direction {
            self.w(match dir {
                FeatureDirection::In => "in ",
                FeatureDirection::Out => "out ",
                FeatureDirection::InOut => "inout ",
            });
        }
        if c.is_derived {
            self.w("derived ");
        }
        if c.is_abstract {
            self.w("abstract ");
        }
        if c.is_variation {
            self.w("variation ");
        }
        if c.is_composite {
            self.w("composite ");
        }
        if c.is_portion {
            self.w("portion ");
        }
        if c.is_variable {
            self.w("var ");
        }
        if c.is_constant {
            self.w(if self.kerml() { "const " } else { "constant " });
        }
        if c.is_ref {
            self.w("ref ");
        }
        self.print_feature_declaration(&c.decl);
    }

    /// The keyword introducing a usage. `None` = keyword-less.
    fn usage_keyword(&self, kind: UsageKind) -> Option<&'static str> {
        Some(match kind {
            UsageKind::Attribute => "attribute",
            UsageKind::Enum => "enum",
            UsageKind::Occurrence => "occurrence",
            UsageKind::Item => "item",
            UsageKind::Part => "part",
            UsageKind::Port => "port",
            UsageKind::Connection => "connection",
            UsageKind::Interface => "interface",
            UsageKind::Allocation => "allocation",
            UsageKind::Flow => "flow",
            UsageKind::Action => "action",
            UsageKind::State => "state",
            UsageKind::Calc => "calc",
            UsageKind::Constraint => "constraint",
            UsageKind::Requirement => "requirement",
            UsageKind::Concern => "concern",
            UsageKind::Case => "case",
            UsageKind::Analysis => "analysis",
            UsageKind::Verification => "verification",
            UsageKind::UseCase => "use case",
            UsageKind::View => "view",
            UsageKind::Viewpoint => "viewpoint",
            UsageKind::Rendering => "rendering",
            UsageKind::Message => "message",
            UsageKind::SuccessionFlow => "succession flow",
            UsageKind::Feature => "feature",
            UsageKind::Step => "step",
            UsageKind::Expr => "expr",
            UsageKind::BoolExpr => "bool",
            UsageKind::Connector => "connector",
            _ => return None,
        })
    }

    /// True if the usage's declaration starts with a reference target
    /// (`perform a.b`, `exhibit s`, …) rather than a declared head.
    fn is_reference_form(u: &Usage) -> bool {
        u.declaration.id.is_empty()
            && matches!(
                u.declaration.specializations.first(),
                Some(FeatureSpecialization::References(_))
            )
    }

    /// A declaration is "present" if it carries anything printable —
    /// including a bare multiplicity (`succession [n] first a then b`).
    fn decl_present(d: &FeatureDeclaration) -> bool {
        !d.id.is_empty()
            || !d.specializations.is_empty()
            || d.multiplicity.is_some()
            || d.is_ordered
            || d.is_nonunique
            || d.is_sufficient
            || d.conjugates.is_some()
            || d.chains.is_some()
            || d.inverse_of.is_some()
            || !d.featured_by.is_empty()
    }

    fn print_usage(&mut self, u: &Usage, span: Span) {
        self.print_usage_prefix(&u.prefix);
        match u.kind {
            UsageKind::Ref | UsageKind::Default | UsageKind::Extended => {
                // Keyword-less (`ref` is printed by the prefix; Extended by
                // its metadata keywords).
                if u.kind == UsageKind::Ref && !u.prefix.is_ref {
                    self.w("ref ");
                }
                self.print_declaration_value_body(u, span);
            }
            UsageKind::Perform => self.print_composite(u, "perform", "action", span),
            UsageKind::Exhibit => self.print_composite(u, "exhibit", "state", span),
            UsageKind::Include => self.print_composite(u, "include", "use case", span),
            UsageKind::Event => self.print_composite(u, "event", "occurrence", span),
            UsageKind::Satisfy => {
                let UsageDetail::Satisfy {
                    asserted,
                    negated,
                    by,
                } = &u.detail
                else {
                    unreachable!("satisfy usage carries Satisfy detail")
                };
                if *asserted {
                    self.w("assert ");
                }
                if *negated {
                    self.w("not ");
                }
                self.w("satisfy");
                if Self::is_reference_form(u) {
                    self.w(" ");
                    self.print_first_reference(u);
                    self.print_remaining_specs(u, 1);
                } else {
                    self.w(" requirement ");
                    self.print_feature_declaration(&u.declaration);
                }
                self.print_value(u.value.as_deref());
                if let Some(by) = by {
                    self.w(" by ");
                    self.print_target(by);
                }
                self.trim_trailing_space();
                self.print_body(&u.body, span);
            }
            UsageKind::AssertConstraint => {
                let negated = matches!(u.detail, UsageDetail::Assert { negated: true });
                self.w("assert ");
                if negated {
                    self.w("not ");
                }
                if Self::is_reference_form(u) {
                    self.print_first_reference(u);
                    self.print_remaining_specs(u, 1);
                } else {
                    self.w("constraint ");
                    self.print_feature_declaration(&u.declaration);
                }
                self.print_value(u.value.as_deref());
                self.trim_trailing_space();
                self.print_body(&u.body, span);
            }
            UsageKind::Invariant => {
                let negated = matches!(u.detail, UsageDetail::Assert { negated: true });
                self.w("inv ");
                if negated {
                    self.w("false ");
                }
                self.print_declaration_value_body(u, span);
            }
            UsageKind::Succession => self.print_succession(u, span),
            UsageKind::Binding => self.print_binding(u, span),
            UsageKind::Transition => self.print_transition(u, span),
            UsageKind::Accept => {
                self.print_node_head(u, "accept");
                if let UsageDetail::Accept {
                    payload,
                    trigger,
                    via,
                } = &u.detail
                {
                    self.print_payload(payload);
                    if let Some(t) = trigger {
                        self.w(match t.kind {
                            TriggerKind::At => "at ",
                            TriggerKind::After => "after ",
                            TriggerKind::When => "when ",
                        });
                        self.print_expr(&t.expr, 0);
                        self.w(" ");
                    }
                    if let Some(via) = via {
                        self.w("via ");
                        self.print_expr(via, 0);
                        self.w(" ");
                    }
                }
                self.trim_trailing_space();
                self.print_body(&u.body, span);
            }
            UsageKind::Send => {
                self.print_node_head(u, "send");
                if let UsageDetail::Send { payload, via, to } = &u.detail {
                    if let Some(p) = payload {
                        self.print_expr(p, 0);
                        self.w(" ");
                    }
                    if let Some(v) = via {
                        self.w("via ");
                        self.print_expr(v, 0);
                        self.w(" ");
                    }
                    if let Some(t) = to {
                        self.w("to ");
                        self.print_expr(t, 0);
                        self.w(" ");
                    }
                }
                self.trim_trailing_space();
                self.print_body(&u.body, span);
            }
            UsageKind::Assign => {
                self.print_node_head(u, "assign");
                if let UsageDetail::Assign { target, value } = &u.detail {
                    self.print_expr(target, 0);
                    self.w(" := ");
                    self.print_expr(value, 0);
                }
                self.print_body(&u.body, span);
            }
            UsageKind::Terminate => {
                self.print_node_head(u, "terminate");
                if let UsageDetail::Terminate { target: Some(t) } = &u.detail {
                    self.print_expr(t, 0);
                }
                self.print_body(&u.body, span);
            }
            UsageKind::IfNode => {
                self.print_node_head(u, "if");
                if let UsageDetail::IfNode {
                    cond,
                    then_body,
                    else_body,
                } = &u.detail
                {
                    self.print_expr(cond, 0);
                    self.w(" ");
                    self.print_action_block(then_body, span);
                    if let Some(else_body) = else_body {
                        self.w(" else ");
                        if else_body.kind == UsageKind::IfNode {
                            // Nested else-if chains print inline.
                            self.print_usage_inline_if(else_body, span);
                        } else {
                            self.print_action_block(else_body, span);
                        }
                    }
                }
                self.out.push('\n');
            }
            UsageKind::WhileLoop => {
                self.print_node_head(u, "");
                if let UsageDetail::WhileLoop { cond, body, until } = &u.detail {
                    match cond {
                        Some(c) => {
                            self.w("while ");
                            self.print_expr(c, 0);
                            self.w(" ");
                        }
                        None => self.w("loop "),
                    }
                    self.print_action_block(body, span);
                    if let Some(untl) = until {
                        self.w(" until ");
                        self.print_expr(untl, 0);
                        self.w(";");
                    }
                }
                self.out.push('\n');
            }
            UsageKind::ForLoop => {
                self.print_node_head(u, "for");
                if let UsageDetail::ForLoop { var, seq, body } = &u.detail {
                    self.print_feature_declaration(var);
                    self.w("in ");
                    self.print_expr(seq, 0);
                    self.w(" ");
                    self.print_action_block(body, span);
                }
                self.out.push('\n');
            }
            UsageKind::Merge => self.print_control(u, "merge", span),
            UsageKind::Decide => self.print_control(u, "decide", span),
            UsageKind::Join => self.print_control(u, "join", span),
            UsageKind::Fork => self.print_control(u, "fork", span),
            UsageKind::Metadata => {
                self.w("@");
                let mut specs = u.declaration.specializations.iter();
                let metaclass = specs.next();
                if !u.declaration.id.is_empty() {
                    self.print_identification(&u.declaration.id);
                    self.w(": ");
                }
                if let Some(FeatureSpecialization::TypedBy(types)) = metaclass {
                    if let Some(t) = types.first() {
                        self.print_target(&t.target);
                    }
                }
                if let UsageDetail::Metadata { about } = &u.detail {
                    if !about.is_empty() {
                        self.w(" about ");
                        for (i, qn) in about.iter().enumerate() {
                            if i > 0 {
                                self.w(", ");
                            }
                            self.print_qn(qn);
                        }
                    }
                }
                self.print_body(&u.body, span);
            }
            UsageKind::Connection | UsageKind::Allocation => {
                let (kw, connect_kw) = if u.kind == UsageKind::Connection {
                    ("connection", "connect")
                } else {
                    ("allocation", "allocate")
                };
                let ends = Self::connector_ends(&u.detail);
                let clause = Self::clause_spells(ends);
                let bare = !Self::decl_present(&u.declaration) && u.value.is_none() && clause;
                if bare {
                    self.w(connect_kw);
                    self.w(" ");
                    self.print_connector_part(&u.detail);
                } else {
                    self.w(kw);
                    self.w(" ");
                    self.print_feature_declaration(&u.declaration);
                    self.print_value(u.value.as_deref());
                    if clause {
                        self.w(" ");
                        self.w(connect_kw);
                        self.w(" ");
                        self.print_connector_part(&u.detail);
                    }
                }
                self.trim_trailing_space();
                self.print_connector_body(ends, &u.body, span);
            }
            UsageKind::Interface => {
                let ends = Self::connector_ends(&u.detail);
                self.w("interface ");
                self.print_feature_declaration(&u.declaration);
                self.print_value(u.value.as_deref());
                if Self::clause_spells(ends) {
                    if Self::decl_present(&u.declaration) {
                        self.w(" connect ");
                    }
                    self.print_connector_part(&u.detail);
                }
                self.trim_trailing_space();
                self.print_connector_body(ends, &u.body, span);
            }
            UsageKind::Connector => {
                let ends = Self::connector_ends(&u.detail);
                self.w("connector ");
                self.print_feature_declaration(&u.declaration);
                self.print_value(u.value.as_deref());
                if ends.len() == 2 {
                    self.w(" from ");
                    self.print_connector_end(&ends[0]);
                    self.w(" to ");
                    self.print_connector_end(&ends[1]);
                } else if Self::clause_spells(ends) {
                    self.w(" ");
                    self.print_connector_ends(ends);
                }
                self.trim_trailing_space();
                self.print_connector_body(ends, &u.body, span);
            }
            UsageKind::Flow | UsageKind::Message | UsageKind::SuccessionFlow => {
                self.w(self.usage_keyword(u.kind).unwrap());
                self.w(" ");
                self.print_feature_declaration(&u.declaration);
                self.print_value(u.value.as_deref());
                if let UsageDetail::Flow {
                    payload,
                    source,
                    target,
                } = &u.detail
                {
                    let bare = !Self::decl_present(&u.declaration) && payload.is_none();
                    if let Some(p) = payload {
                        self.w(" of ");
                        self.print_payload(p);
                    }
                    if let (Some(s), Some(t)) = (source, target) {
                        if !bare {
                            self.w(" from ");
                        }
                        self.print_target(&s.target);
                        self.w(" to ");
                        self.print_target(&t.target);
                    }
                }
                self.trim_trailing_space();
                self.print_body(&u.body, span);
            }
            _ => {
                // Simple keyword kinds.
                if let Some(kw) = self.usage_keyword(u.kind) {
                    self.w(kw);
                    self.w(" ");
                }
                self.print_declaration_value_body(u, span);
            }
        }
    }

    /// `action a1 <node-kw> ` head for action nodes with declared names.
    fn print_node_head(&mut self, u: &Usage, node_kw: &str) {
        if Self::decl_present(&u.declaration) {
            self.w("action ");
            self.print_feature_declaration(&u.declaration);
        }
        if !node_kw.is_empty() {
            self.w(node_kw);
            self.w(" ");
        }
    }

    fn print_control(&mut self, u: &Usage, kw: &str, span: Span) {
        self.w(kw);
        self.w(" ");
        self.print_declaration_value_body(u, span);
    }

    fn print_usage_inline_if(&mut self, u: &Usage, span: Span) {
        // A nested else-if: print without indentation/newline handling.
        self.print_usage_prefix(&u.prefix);
        self.print_node_head(u, "if");
        if let UsageDetail::IfNode {
            cond,
            then_body,
            else_body,
        } = &u.detail
        {
            self.print_expr(cond, 0);
            self.w(" ");
            self.print_action_block(then_body, span);
            if let Some(else_body) = else_body {
                self.w(" else ");
                if else_body.kind == UsageKind::IfNode {
                    self.print_usage_inline_if(else_body, span);
                } else {
                    self.print_action_block(else_body, span);
                }
            }
        }
    }

    /// An anonymous action body block `{ … }` (if/while/for bodies).
    fn print_action_block(&mut self, u: &Usage, span: Span) {
        if Self::decl_present(&u.declaration) {
            self.w("action ");
            self.print_feature_declaration(&u.declaration);
        }
        match &u.body {
            Some(members) => self.print_brace_members(members, span),
            None => self.w("{}"),
        }
    }

    fn print_composite(&mut self, u: &Usage, kw: &str, decl_kw: &str, span: Span) {
        self.w(kw);
        if Self::is_reference_form(u) {
            self.w(" ");
            self.print_first_reference(u);
            self.print_remaining_specs(u, 1);
        } else {
            self.w(" ");
            self.w(decl_kw);
            self.w(" ");
            self.print_feature_declaration(&u.declaration);
        }
        self.print_value(u.value.as_deref());
        if u.is_parallel {
            self.w(" parallel");
        }
        self.trim_trailing_space();
        self.print_body(&u.body, span);
    }

    fn print_first_reference(&mut self, u: &Usage) {
        if let Some(FeatureSpecialization::References(t)) = u.declaration.specializations.first() {
            self.print_target(t);
            self.w(" ");
        }
    }

    fn print_remaining_specs(&mut self, u: &Usage, skip: usize) {
        for spec in u.declaration.specializations.iter().skip(skip) {
            self.print_specialization(spec);
        }
        if let Some(mult) = &u.declaration.multiplicity {
            self.trim_trailing_space();
            self.print_multiplicity(mult);
            self.w(" ");
        }
    }

    fn print_wrapped_usage(&mut self, kw: &str, u: &Usage, span: Span) {
        self.w(kw);
        self.w(" ");
        self.print_metadata_prefixes(&u.prefix.metadata);
        self.print_declaration_value_body(u, span);
    }

    fn print_ref_or_kind_tail(&mut self, u: &Usage, kind_kw: &str, span: Span) {
        self.w(" ");
        self.print_metadata_prefixes(&u.prefix.metadata);
        if Self::is_reference_form(u) {
            self.print_first_reference(u);
            self.print_remaining_specs(u, 1);
        } else {
            if u.prefix.metadata.is_empty() {
                self.w(kind_kw);
                self.w(" ");
            }
            self.print_feature_declaration(&u.declaration);
        }
        self.print_value(u.value.as_deref());
        self.trim_trailing_space();
        self.print_body(&u.body, span);
    }

    fn print_declaration_value_body(&mut self, u: &Usage, span: Span) {
        self.print_feature_declaration(&u.declaration);
        self.print_value(u.value.as_deref());
        if u.is_parallel {
            self.w(" parallel");
        }
        self.trim_trailing_space();
        self.print_body(&u.body, span);
    }

    fn print_succession(&mut self, u: &Usage, span: Span) {
        let UsageDetail::Succession { source, target } = &u.detail else {
            // Plain `succession s : S;` (KerML declaration-only form).
            self.w("succession ");
            self.print_declaration_value_body(u, span);
            return;
        };
        let has_decl = Self::decl_present(&u.declaration);
        // A source end with no target and no name is textually unspelled
        // (the `then [mult]? x;` target-succession shorthand).
        let unspelled_source = |src: &ConnectorEnd| src.name.is_none() && src.target.is_unspelled();
        match source {
            Some(src) if !unspelled_source(src) => {
                if has_decl || self.kerml() {
                    self.w("succession ");
                    if has_decl {
                        self.print_feature_declaration(&u.declaration);
                    }
                }
                self.w("first ");
                self.print_connector_end(src);
                self.w(" then ");
                self.print_connector_end(target);
            }
            source => {
                // Target-succession shorthand.
                self.w("then ");
                if let Some(mult) = source.as_ref().and_then(|s| s.multiplicity.as_ref()) {
                    self.print_multiplicity(mult);
                    self.w(" ");
                }
                self.print_connector_end(target);
            }
        }
        self.trim_trailing_space();
        self.print_body(&u.body, span);
    }

    fn print_binding(&mut self, u: &Usage, span: Span) {
        let has_decl = Self::decl_present(&u.declaration);
        // A binding binds exactly two ends, and that is what the parser
        // builds; a usage assembled from a partial interchange document can
        // carry another arity, held as a plain connector detail. Print the
        // ends that are there instead of assuming the pair.
        let ends = Self::connector_ends(&u.detail);
        // The notation spells a *binding's* ends as one `a = b` pair and
        // has no form for any other count. Printing what is there behind
        // the binding keyword regardless would emit text that is not a
        // binding: one end reads as a missing right side, three as a
        // chain of two whose third end is quietly lost.
        let pair = ends.len() == 2;
        // Ends the head could not spell, carried into the body instead.
        let mut ends_in_body: &[ConnectorEnd] = &[];
        if pair {
            if self.kerml() {
                // KerML spells the pair behind an optional `of`, and the
                // declaration stands without it.
                self.w("binding ");
                if has_decl {
                    self.print_feature_declaration(&u.declaration);
                    self.w("of ");
                }
            } else {
                if has_decl {
                    self.w("binding ");
                    self.print_feature_declaration(&u.declaration);
                }
                self.w("bind ");
            }
        } else {
            // Neither dialect spells a binding that is not a pair. SysML
            // requires the `bind` clause after its keyword (SysML.xtext
            // `BindingConnectorAsUsage`), so a head without the clause
            // does not parse at all; KerML does take the keyword alone,
            // but a binding connector that does not bind two features
            // draws a finding, so the text would parse and not check.
            //
            // What the member can keep is everything but the binding. Its
            // declaration prints as a usage without the keyword, and every
            // end prints as an `end ::> …;` body member — the form the
            // notation gives a connector end that is written out rather
            // than listed in a clause. That spelling parses, draws no
            // finding, and re-lifts each end as an end membership at any
            // count. What is lost is that the connector bound its ends
            // rather than merely relating them.
            //
            // Another connector keyword would keep more of that, but none
            // either dialect offers is both unconstrained and honest: the
            // connection form demands an association structure as its
            // type and refuses an ordinary one, and it spells one end not
            // at all.
            //
            // KerML names a metaclass on every member, so the usage that
            // keeps the declaration is spelled `feature` — with or without
            // one, since a member whose whole text is a body does not
            // parse there either. SysML takes the declaration as a head on
            // its own and spells the keyword-less usage `ref` where there
            // is nothing to declare.
            //
            // Such a usage only comes from a payload, where building it
            // already records that its end count is not two.
            if self.kerml() {
                self.w("feature ");
            }
            if has_decl {
                self.print_feature_declaration(&u.declaration);
            } else if !self.kerml() {
                self.w("ref ");
            }
            ends_in_body = ends;
        }
        if pair {
            for (i, end) in ends.iter().enumerate() {
                if i > 0 {
                    self.w(" = ");
                }
                self.print_connector_end(end);
            }
        }
        self.trim_trailing_space();
        if ends_in_body.is_empty() {
            self.print_body(&u.body, span);
        } else {
            self.print_end_member_body(ends_in_body, &u.body, span);
        }
    }

    /// A body that leads with the connector's ends, each spelled as an
    /// `end ::> …;` member, ahead of whatever members the usage carried.
    /// The notation spells an end this way wherever a clause cannot hold
    /// it, and the lift reads it back as an end membership.
    fn print_end_member_body(
        &mut self,
        ends: &[ConnectorEnd],
        body: &Option<Vec<Member>>,
        span: Span,
    ) {
        self.w(" {\n");
        self.depth += 1;
        for end in ends {
            self.push_indent();
            self.w("end ");
            if end.name.is_none() && end.target.is_unspelled() && end.multiplicity.is_none() {
                // Nothing at all follows the prefix. SysML reads a member
                // that is only its prefix; KerML wants an element after
                // one, and `end;` stops it. Naming the metaclass the end
                // has anyway gives both a member to read, and neither
                // spells anything the bare form did not.
                self.w("feature ");
            }
            if let Some(name) = &end.name {
                self.print_name(name);
                self.w(" ");
            }
            // An end that references no feature spells no subsetting.
            if !end.target.is_unspelled() {
                self.w("::> ");
                self.print_target(&end.target);
            }
            if let Some(mult) = &end.multiplicity {
                // Canonical position for a feature's multiplicity is after
                // what it specializes; ahead of that, a `[` would open the
                // cross feature an end may declare instead.
                self.trim_trailing_space();
                self.print_multiplicity(mult);
            }
            self.trim_trailing_space();
            self.line_end();
        }
        for m in body.iter().flatten() {
            self.print_member(m);
        }
        self.flush_notes(span.end);
        self.depth -= 1;
        self.push_indent();
        self.w("}");
        if let Some(layout) = &self.layout {
            self.prev_line = Some(layout.line(span.end.saturating_sub(1)));
        }
        self.out.push('\n');
    }

    fn print_transition(&mut self, u: &Usage, span: Span) {
        let UsageDetail::Transition {
            source,
            trigger,
            guard,
            effect,
            target,
            is_default,
        } = &u.detail
        else {
            unreachable!("transition usage carries Transition detail")
        };
        if *is_default {
            self.w("else ");
            if let Some(t) = target {
                self.print_connector_end(t);
            }
            self.trim_trailing_space();
            self.print_body(&u.body, span);
            return;
        }
        let has_decl = Self::decl_present(&u.declaration);
        // Pure guarded shorthand (`if g then t;`).
        let pure_guard = source.is_none() && trigger.is_none() && effect.is_none() && !has_decl;
        if !(pure_guard && guard.is_some()) {
            self.w("transition ");
            if has_decl {
                self.print_feature_declaration(&u.declaration);
            }
            if let Some(src) = source {
                self.w("first ");
                self.print_target(src);
                self.w(" ");
            }
        }
        if let Some(trigger) = trigger {
            if let UsageDetail::Accept {
                payload,
                trigger: tk,
                via,
            } = trigger.as_ref()
            {
                self.w("accept ");
                self.print_payload(payload);
                if let Some(t) = tk {
                    self.w(match t.kind {
                        TriggerKind::At => "at ",
                        TriggerKind::After => "after ",
                        TriggerKind::When => "when ",
                    });
                    self.print_expr(&t.expr, 0);
                    self.w(" ");
                }
                if let Some(via) = via {
                    self.w("via ");
                    self.print_expr(via, 0);
                    self.w(" ");
                }
            }
        }
        if let Some(guard) = guard {
            self.w("if ");
            self.print_expr(guard, 0);
            self.w(" ");
        }
        if let Some(effect) = effect {
            self.w("do ");
            let is_empty = effect.kind == UsageKind::Action
                && !Self::decl_present(&effect.declaration)
                && matches!(effect.detail, UsageDetail::None)
                && effect.value.is_none()
                && effect.body.is_none();
            if !is_empty {
                self.print_performed_action(effect, span, false);
                self.w(" ");
            }
        }
        self.w("then ");
        if let Some(t) = target {
            self.print_connector_end(t);
        }
        self.trim_trailing_space();
        self.print_body(&u.body, span);
    }

    /// A performed-action usage (state entry/do/exit, transition effects):
    /// reference form, `action` declaration form, or an accept/send/assign
    /// node. `terminated` controls whether a body/`;` is printed.
    fn print_performed_action(&mut self, u: &Usage, span: Span, terminated: bool) {
        match u.kind {
            UsageKind::Accept | UsageKind::Send | UsageKind::Assign => {
                // Re-use the node printers; they always terminate, so trim
                // when used as a transition effect.
                let saved = self.out.len();
                self.print_usage(u, span);
                if !terminated {
                    // Remove trailing ";\n".
                    while self.out.len() > saved
                        && (self.out.ends_with('\n') || self.out.ends_with(';'))
                    {
                        self.out.pop();
                    }
                }
            }
            _ => {
                if Self::is_reference_form(u) {
                    self.print_first_reference(u);
                    self.print_remaining_specs(u, 1);
                } else {
                    self.w("action ");
                    self.print_feature_declaration(&u.declaration);
                }
                self.print_value(u.value.as_deref());
                self.trim_trailing_space();
                if terminated {
                    self.print_body(&u.body, span);
                } else if let Some(members) = &u.body {
                    self.w(" ");
                    self.print_brace_members(members, span);
                }
            }
        }
    }

    fn print_connector_end(&mut self, end: &ConnectorEnd) {
        if let Some(mult) = &end.multiplicity {
            self.print_multiplicity(mult);
            self.w(" ");
        }
        if let Some(name) = &end.name {
            self.print_name(name);
            self.w(" ::> ");
        }
        self.print_target(&end.target);
    }

    /// The ends a usage's detail carries, if it carries any.
    fn connector_ends(detail: &UsageDetail) -> &[ConnectorEnd] {
        match detail {
            UsageDetail::Binding { ends } | UsageDetail::Connector { ends } => ends,
            _ => &[],
        }
    }

    /// Whether the notation's end clause spells this many ends. It reads
    /// two or more — `from a to b`, `(a, b, c)` — so a connector that an
    /// assembled tree gave fewer has no clause, and its ends go into the
    /// body instead.
    fn clause_spells(ends: &[ConnectorEnd]) -> bool {
        ends.len() >= 2
    }

    /// A connector's body: its own members, behind the ends where no
    /// clause could spell them.
    fn print_connector_body(
        &mut self,
        ends: &[ConnectorEnd],
        body: &Option<Vec<Member>>,
        span: Span,
    ) {
        if ends.is_empty() || Self::clause_spells(ends) {
            self.print_body(body, span);
        } else {
            self.print_end_member_body(ends, body, span);
        }
    }

    fn print_connector_part(&mut self, detail: &UsageDetail) {
        let UsageDetail::Connector { ends } = detail else {
            return;
        };
        if ends.len() == 2 {
            self.print_connector_end(&ends[0]);
            self.w(" to ");
            self.print_connector_end(&ends[1]);
        } else {
            self.print_connector_ends(ends);
        }
    }

    /// The parenthesized end list, which spells any number of ends from
    /// two up: `(a, b, c)`.
    fn print_connector_ends(&mut self, ends: &[ConnectorEnd]) {
        self.w("(");
        for (i, e) in ends.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            self.print_connector_end(e);
        }
        self.w(")");
    }

    fn print_payload(&mut self, p: &PayloadPart) {
        self.print_identification(&p.id);
        for spec in &p.specializations {
            self.print_specialization(spec);
        }
        if let Some(mult) = &p.multiplicity {
            self.trim_trailing_space();
            self.print_multiplicity(mult);
            self.w(" ");
        }
        if p.is_ordered {
            self.w("ordered ");
        }
        if p.is_nonunique {
            self.w("nonunique ");
        }
        if let Some(value) = &p.value {
            self.trim_trailing_space();
            self.print_feature_value(value);
            self.w(" ");
        }
    }

    // ---- feature declarations ----

    /// Multiplicity plus `ordered`/`nonunique` — the grammar only accepts
    /// the ordering markers immediately after the multiplicity part.
    fn print_multiplicity_part(&mut self, d: &FeatureDeclaration) {
        if let Some(mult) = &d.multiplicity {
            self.trim_trailing_space();
            self.print_multiplicity(mult);
            self.w(" ");
        }
        if d.is_ordered {
            self.w("ordered ");
        }
        if d.is_nonunique {
            self.w("nonunique ");
        }
    }

    fn print_feature_declaration(&mut self, d: &FeatureDeclaration) {
        if d.is_sufficient {
            self.w("all ");
        }
        self.print_identification(&d.id);
        let mut mult_printed = false;
        for (i, spec) in d.specializations.iter().enumerate() {
            self.print_specialization(spec);
            // Canonical multiplicity position: after the typing clause.
            if i == 0 && matches!(spec, FeatureSpecialization::TypedBy(_)) {
                self.print_multiplicity_part(d);
                mult_printed = true;
            }
        }
        if !mult_printed {
            self.print_multiplicity_part(d);
        }
        if let Some(t) = &d.conjugates {
            self.w("~ ");
            self.print_target(t);
            self.w(" ");
        }
        if let Some(t) = &d.chains {
            self.w("chains ");
            self.print_target(t);
            self.w(" ");
        }
        if let Some(t) = &d.inverse_of {
            self.w("inverse of ");
            self.print_target(t);
            self.w(" ");
        }
        if !d.featured_by.is_empty() {
            self.w("featured by ");
            self.print_target_list(&d.featured_by);
            self.w(" ");
        }
        for (kw, list) in [
            ("disjoint from", &d.disjoint_from),
            ("unions", &d.unions),
            ("intersects", &d.intersects),
            ("differences", &d.differences),
        ] {
            if !list.is_empty() {
                self.w(kw);
                self.w(" ");
                self.print_target_list(list);
                self.w(" ");
            }
        }
    }

    fn print_specialization(&mut self, spec: &FeatureSpecialization) {
        match spec {
            FeatureSpecialization::TypedBy(types) => {
                self.w(": ");
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    if t.is_conjugated {
                        self.w("~");
                    }
                    self.print_target(&t.target);
                }
                self.w(" ");
            }
            FeatureSpecialization::Subsets(list) => {
                self.w(":> ");
                self.print_target_list(list);
                self.w(" ");
            }
            FeatureSpecialization::Redefines(list) => {
                self.w(":>> ");
                self.print_target_list(list);
                self.w(" ");
            }
            FeatureSpecialization::References(t) => {
                self.w("::> ");
                self.print_target(t);
                self.w(" ");
            }
            FeatureSpecialization::Crosses(t) => {
                self.w("crosses ");
                self.print_target(t);
                self.w(" ");
            }
        }
    }

    fn print_multiplicity(&mut self, m: &Multiplicity) {
        self.w("[");
        if let Some(lower) = &m.lower {
            self.print_mult_bound(lower);
            self.w("..");
        }
        self.print_mult_bound(&m.upper);
        self.w("]");
    }

    /// Bounds re-parse only as literals, names, or a parenthesized
    /// expression — wrap anything else (a Sequence prints its own parens).
    fn print_mult_bound(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Literal(_) | ExprKind::Ref(_) | ExprKind::Sequence(_) => {
                self.print_expr(e, 0);
            }
            _ => {
                self.w("(");
                self.print_expr(e, 0);
                self.w(")");
            }
        }
    }

    fn print_value(&mut self, value: Option<&FeatureValue>) {
        if let Some(v) = value {
            self.trim_trailing_space();
            self.print_feature_value(v);
        }
    }

    fn print_feature_value(&mut self, v: &FeatureValue) {
        self.w(match v.kind {
            ValueKind::Bound => " = ",
            ValueKind::Initial => " := ",
            ValueKind::Default => " default = ",
            ValueKind::DefaultInitial => " default := ",
        });
        self.print_expr(&v.expr, 0);
    }

    // ---- bodies ----

    fn print_body(&mut self, body: &Option<Vec<Member>>, span: Span) {
        match body {
            None => self.line_end(),
            Some(members) => {
                self.w(" ");
                self.print_brace_members(members, span);
                self.out.push('\n');
            }
        }
    }

    fn print_brace_members(&mut self, members: &[Member], span: Span) {
        if members.is_empty() {
            // Flush any notes that lived inside the empty body.
            self.w("{");
            let saved = self.out.len();
            self.out.push('\n');
            self.depth += 1;
            self.flush_notes(span.end);
            self.depth -= 1;
            if self.out.len() == saved + 1 {
                self.out.truncate(saved);
                self.w("}");
            } else {
                self.push_indent();
                self.w("}");
            }
            return;
        }
        self.w("{\n");
        self.depth += 1;
        for m in members {
            self.print_member(m);
        }
        self.flush_notes(span.end);
        self.depth -= 1;
        self.push_indent();
        self.w("}");
        if let Some(layout) = &self.layout {
            self.prev_line = Some(layout.line(span.end.saturating_sub(1)));
        }
    }

    // ---- KerML standalone relationships ----

    fn print_relationship(&mut self, r: &RelationshipDecl) {
        use RelationshipDeclKind::*;
        let (naming, kw, sep) = match r.kind {
            Specialization => ("specialization", "subtype", "specializes"),
            Subclassification => ("specialization", "subclassifier", "specializes"),
            FeatureTyping => ("specialization", "typing", "typed by"),
            Subsetting => ("specialization", "subset", "subsets"),
            Redefinition => ("specialization", "redefinition", "redefines"),
            Conjugation => ("conjugation", "conjugate", "conjugates"),
            Disjoining => ("disjoining", "disjoint", "from"),
            FeatureInverting => ("inverting", "inverse", "of"),
            TypeFeaturing => ("", "featuring", "by"),
        };
        if r.kind == TypeFeaturing {
            self.w("featuring ");
            if !r.id.is_empty() {
                self.print_identification(&r.id);
                self.w("of ");
            }
        } else {
            if !r.id.is_empty() {
                self.w(naming);
                self.w(" ");
                self.print_identification(&r.id);
            }
            self.w(kw);
            self.w(" ");
        }
        self.print_target(&r.source);
        self.w(" ");
        self.w(sep);
        self.w(" ");
        self.print_target(&r.target);
        self.line_end();
    }

    // ---- expressions ----

    /// A body result expression whose logical chain is long enough
    /// breaks one condition per line, continuations led by the
    /// operator (the formatter's `multiline_chains` style):
    ///
    /// ```text
    /// assert constraint {
    ///     ascentMargin > 0
    ///     and tliMargin > 0
    ///     and loiMargin > 0
    /// }
    /// ```
    ///
    /// Only the top-level chain of one operator breaks; nested
    /// sub-chains stay inline unless they qualify on their own when
    /// they are themselves a result expression. Returns false when the
    /// style is off or the expression is not a qualifying chain.
    fn try_print_multiline_chain(&mut self, e: &Expr) -> bool {
        let Some(min) = self.multiline_chains else {
            return false;
        };
        let op = match &e.kind {
            ExprKind::Binary { op, .. }
                if matches!(
                    op,
                    BinaryOp::CondAnd
                        | BinaryOp::CondOr
                        | BinaryOp::Xor
                        | BinaryOp::Implies
                        | BinaryOp::AndAmp
                        | BinaryOp::OrBar
                ) =>
            {
                *op
            }
            _ => return false,
        };
        // Walk the left spine iteratively: a chain of a few hundred operands
        // is ordinary in a generated constraint, and it is the same shape
        // that would drive this apart one stack frame per operand.
        let mut leaves: Vec<&Expr> = Vec::new();
        let mut cur = e;
        while let ExprKind::Binary { op: o, lhs, rhs } = &cur.kind {
            if *o != op {
                break;
            }
            leaves.push(rhs);
            cur = lhs;
        }
        leaves.push(cur);
        leaves.reverse();
        if leaves.len() < usize::from(min) {
            return false;
        }
        let (text, prec, _) = binary_op_info(op);
        self.print_expr(leaves[0], prec);
        for leaf in &leaves[1..] {
            self.out.push('\n');
            self.push_indent();
            self.w(text);
            self.w(" ");
            self.print_expr(leaf, prec + 1);
        }
        true
    }

    fn print_expr(&mut self, e: &Expr, min_prec: u8) {
        let prec = expr_prec(e);
        if prec < min_prec {
            self.w("(");
            self.print_expr_inner(e);
            self.w(")");
        } else {
            self.print_expr_inner(e);
        }
    }

    fn print_expr_inner(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Literal(l) => match l {
                Literal::Bool(b) => self.w(if *b { "true" } else { "false" }),
                Literal::String(s) => self.print_string(s),
                Literal::Integer(raw) | Literal::Real(raw) => self.w(raw),
                Literal::Infinity => self.w("*"),
            },
            ExprKind::Null => self.w("null"),
            ExprKind::Ref(qn) => self.print_qn(qn),
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                self.w("if ");
                self.print_expr(cond, PREC_NULL_COALESCE);
                self.w(" ? ");
                self.print_expr(then_branch, PREC_CONDITIONAL);
                self.w(" else ");
                self.print_expr(else_branch, PREC_CONDITIONAL);
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let (text, prec, right_assoc) = binary_op_info(*op);
                let (lp, rp) = if right_assoc {
                    (prec + 1, prec)
                } else if *op == BinaryOp::Range {
                    (prec + 1, prec + 1)
                } else {
                    (prec, prec + 1)
                };
                self.print_expr(lhs, lp);
                self.w(" ");
                self.w(text);
                self.w(" ");
                self.print_expr(rhs, rp);
            }
            ExprKind::Unary { op, operand } => {
                self.w(match op {
                    UnaryOp::Plus => "+",
                    UnaryOp::Minus => "-",
                    UnaryOp::Tilde => "~",
                    UnaryOp::Not => "not ",
                });
                self.print_expr(operand, PREC_UNARY);
            }
            ExprKind::Classification { op, operand, ty } => {
                if let Some(operand) = operand {
                    // Classification level, not relational: a chained
                    // classification operand (`as T istype U`) prints
                    // without parens and re-parses identically.
                    self.print_expr(operand, PREC_CLASSIFICATION);
                    self.w(" ");
                }
                self.w(match op {
                    ClassificationOp::IsType => "istype ",
                    ClassificationOp::HasType => "hastype ",
                    // `@` binds its type tightly in the implicit-subject
                    // (filter) spelling `@M`; as a binary operator it
                    // spaces like its siblings.
                    ClassificationOp::AtType if operand.is_none() => "@",
                    ClassificationOp::AtType => "@ ",
                    ClassificationOp::MetaAtType => "@@ ",
                    ClassificationOp::As => "as ",
                    ClassificationOp::Meta => "meta ",
                });
                self.print_target(ty);
            }
            ExprKind::Extent { ty } => {
                self.w("all ");
                self.print_target(ty);
            }
            ExprKind::ChainStep { target, member } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w(".");
                self.print_target(member);
            }
            ExprKind::Index { target, index } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w("#(");
                self.print_expr(index, 0);
                self.w(")");
            }
            ExprKind::Bracket { target, arg } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w(" [");
                self.print_expr(arg, 0);
                self.w("]");
            }
            ExprKind::Arrow { target, ty, args } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w("->");
                self.print_target(ty);
                match args {
                    ArrowArgs::Body(body) => {
                        self.w(" ");
                        self.print_expr_inner(body);
                    }
                    ArrowArgs::FunctionRef(f) => {
                        self.w(" ");
                        self.print_qn(f);
                    }
                    ArrowArgs::List(args) => self.print_args(args),
                }
            }
            ExprKind::Collect { target, body } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w(".");
                self.print_expr_inner(body);
            }
            ExprKind::Select { target, body } => {
                self.print_expr(target, PREC_PRIMARY);
                self.w(".?");
                self.print_expr_inner(body);
            }
            ExprKind::Invocation { ty, args } => {
                self.print_target(ty);
                self.print_args(args);
            }
            ExprKind::Constructor { ty, args } => {
                self.w("new ");
                self.print_target(ty);
                self.print_args(args);
            }
            ExprKind::Body { members } => self.print_expr_body(members, e.span),
            ExprKind::BodyTerminator => self.w(";"),
            ExprKind::Sequence(items) => {
                self.w("(");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    self.print_expr(item, 0);
                }
                self.w(")");
            }
            ExprKind::MetadataAccess { target } => {
                self.print_qn(target);
                self.w(".metadata");
            }
        }
    }

    fn print_args(&mut self, args: &[Arg]) {
        self.w("(");
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            if let Some(name) = &a.name {
                self.print_qn(name);
                self.w(" = ");
            }
            self.print_expr(&a.value, 0);
        }
        self.w(")");
    }

    /// `{ … }` expression bodies. Single result expressions print inline;
    /// bodies with parameters or extra members go multi-line.
    fn print_expr_body(&mut self, members: &[Member], span: Span) {
        if let [m] = members {
            if let MemberKind::Result(e) = &m.kind {
                if m.visibility.is_none() {
                    self.w("{");
                    self.print_expr(e, 0);
                    self.w("}");
                    return;
                }
            }
        }
        // Compact param+result form: `{in x; expr}`.
        if Self::compact_body(members) {
            self.w("{");
            for m in members {
                match &m.kind {
                    MemberKind::Usage(u) => self.print_lambda_param(u),
                    MemberKind::Result(e) => self.print_expr(e, 0),
                    _ => unreachable!(),
                }
            }
            self.w("}");
            return;
        }
        // Full calculation-body lambda: multi-line members.
        self.w("{\n");
        self.depth += 1;
        for m in members {
            self.print_member(m);
        }
        self.flush_notes(span.end);
        self.depth -= 1;
        self.push_indent();
        self.w("}");
    }

    /// One lambda parameter of the compact body form (`in x; `).
    fn print_lambda_param(&mut self, u: &Usage) {
        self.w("in ");
        if u.prefix.is_ref {
            self.w("ref ");
        }
        self.print_feature_declaration(&u.declaration);
        self.trim_trailing_space();
        self.w("; ");
    }

    /// Is `members` the compact param+result lambda shape?
    fn compact_body(members: &[Member]) -> bool {
        members.iter().all(|m| {
            (matches!(&m.kind, MemberKind::Result(_)) && m.visibility.is_none())
                || matches!(&m.kind, MemberKind::Usage(u)
                    if u.prefix.direction == Some(FeatureDirection::In)
                        && !u.prefix.is_derived && !u.prefix.is_abstract
                        && u.body.is_none() && u.value.is_none() && m.visibility.is_none())
        })
    }

    // ---- width-aware expression layout (the query formatter) ----

    /// Column the next character would land in.
    fn col(&self) -> usize {
        self.out.len() - self.out.rfind('\n').map_or(0, |i| i + 1)
    }

    /// This expression rendered on one line, in the canonical spelling.
    fn flat_expr(&self, e: &Expr) -> String {
        let mut p = Printer::new_opts(
            self.dialect,
            None,
            PrintOptions {
                indent: Indent::Spaces(4),
                ..PrintOptions::default()
            },
        );
        p.indent = self.indent.clone();
        p.print_expr(e, 0);
        p.out
    }

    /// Print `e`, breaking it across lines only where its flat form
    /// would run past `width`. Constructs with no break points (and
    /// anything already multi-line) print flat.
    fn print_expr_wrapped(&mut self, e: &Expr, width: usize) {
        let flat = self.flat_expr(e);
        if self.col() + flat.chars().count() <= width {
            self.w(&flat);
            return;
        }
        match &e.kind {
            ExprKind::Arrow { .. } => self.print_chain_wrapped(e, width),
            ExprKind::Invocation { ty, args } | ExprKind::Constructor { ty, args } => {
                if matches!(e.kind, ExprKind::Constructor { .. }) {
                    self.w("new ");
                }
                self.print_target(ty);
                self.print_args_wrapped(args, width);
            }
            ExprKind::Body { members } if Self::compact_body(members) => {
                self.print_body_wrapped(members, width)
            }
            _ => self.w(&flat),
        }
    }

    /// A `->` chain: the base, then one step per line, each indented a
    /// level under it (the shape query authors write by hand).
    fn print_chain_wrapped(&mut self, e: &Expr, width: usize) {
        let mut steps: Vec<(&TargetRef, &ArrowArgs)> = Vec::new();
        let mut base = e;
        while let ExprKind::Arrow { target, ty, args } = &base.kind {
            steps.push((ty, args));
            base = target;
        }
        steps.reverse();
        self.print_expr_wrapped(base, width);
        self.depth += 1;
        for (ty, args) in steps {
            self.w("\n");
            self.push_indent();
            self.w("->");
            self.print_target(ty);
            match args {
                ArrowArgs::Body(body) => {
                    self.w(" ");
                    self.print_expr_wrapped(body, width);
                }
                ArrowArgs::FunctionRef(f) => {
                    self.w(" ");
                    self.print_qn(f);
                }
                ArrowArgs::List(a) => self.print_args_wrapped(a, width),
            }
        }
        self.depth -= 1;
    }

    /// An argument list with one argument per line.
    fn print_args_wrapped(&mut self, args: &[Arg], width: usize) {
        self.w("(");
        self.depth += 1;
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                self.w(",");
            }
            self.w("\n");
            self.push_indent();
            if let Some(name) = &a.name {
                self.print_qn(name);
                self.w(" = ");
            }
            self.print_expr_wrapped(&a.value, width);
        }
        self.depth -= 1;
        self.w(")");
    }

    /// A compact lambda body whose result needs its own line:
    /// `{in x;` then the result indented under it.
    fn print_body_wrapped(&mut self, members: &[Member], width: usize) {
        self.w("{");
        self.depth += 1;
        for m in members {
            match &m.kind {
                MemberKind::Usage(u) => self.print_lambda_param(u),
                MemberKind::Result(e) => {
                    self.trim_trailing_space();
                    self.w("\n");
                    self.push_indent();
                    self.print_expr_wrapped(e, width);
                }
                _ => unreachable!(),
            }
        }
        self.depth -= 1;
        self.w("}");
    }
}

// ---- expression precedence ----

const PREC_CONDITIONAL: u8 = 1;
const PREC_NULL_COALESCE: u8 = 2;
const PREC_CLASSIFICATION: u8 = 8;
const PREC_UNARY: u8 = 14;
const PREC_PRIMARY: u8 = 16;

fn binary_op_info(op: BinaryOp) -> (&'static str, u8, bool) {
    use BinaryOp::*;
    match op {
        NullCoalescing => ("??", 2, false),
        Implies => ("implies", 3, false),
        OrBar => ("|", 4, false),
        CondOr => ("or", 4, false),
        Xor => ("xor", 5, false),
        AndAmp => ("&", 6, false),
        CondAnd => ("and", 6, false),
        Eq => ("==", 7, false),
        NotEq => ("!=", 7, false),
        Same => ("===", 7, false),
        NotSame => ("!==", 7, false),
        Lt => ("<", 9, false),
        Gt => (">", 9, false),
        LtEq => ("<=", 9, false),
        GtEq => (">=", 9, false),
        Range => ("..", 10, false),
        Add => ("+", 11, false),
        Sub => ("-", 11, false),
        Mul => ("*", 12, false),
        Div => ("/", 12, false),
        Rem => ("%", 12, false),
        Pow => ("**", 13, true),
        Caret => ("^", 13, true),
    }
}

fn expr_prec(e: &Expr) -> u8 {
    match &e.kind {
        ExprKind::Conditional { .. } => PREC_CONDITIONAL,
        ExprKind::Binary { op, .. } => binary_op_info(*op).1,
        ExprKind::Unary { .. } => PREC_UNARY,
        ExprKind::Classification { .. } => PREC_CLASSIFICATION,
        ExprKind::Extent { .. } => 15,
        ExprKind::ChainStep { .. }
        | ExprKind::Index { .. }
        | ExprKind::Bracket { .. }
        | ExprKind::Arrow { .. }
        | ExprKind::Collect { .. }
        | ExprKind::Select { .. } => PREC_PRIMARY,
        _ => 17,
    }
}

// ---------------------------------------------------------------------------
// Member re-indentation (shared by the edit planner and lint)
// ---------------------------------------------------------------------------

/// The indentation unit a line indented `indent` nests with: tab-
/// indented text nests with a tab, anything else with the canonical
/// four spaces. A depth-0 owner has no indentation of its own to
/// read, so the unit text decides.
#[must_use]
pub fn indent_unit(indent: &str, src: &str) -> &'static str {
    let tabs = if indent.is_empty() {
        src.lines().any(|l| l.starts_with('\t'))
    } else {
        indent.contains('\t')
    };
    if tabs { "\t" } else { "    " }
}

/// Re-spell a member text's indentation for its destination: every
/// line after the first is rewritten as `base` + its own depth in
/// `unit`s, the text's own indent unit detected as the shortest
/// nonzero leading run among its lines. The first line stays bare —
/// callers place it (after a derived indent, or at an existing splice
/// point whose leading whitespace survives). Whitespace beyond whole
/// units is preserved, blank lines stay empty, so ragged input
/// degrades gracefully instead of being guessed at.
///
/// This is both how the edit planner spells inserted members and how
/// integrity checks reproduce that spelling — keep the two in one
/// place.
#[must_use]
pub fn reindent_member_text(text: &str, base: &str, unit: &str) -> String {
    let lines: Vec<&str> = text.split('\n').collect();
    if lines.len() <= 1 {
        return text.to_string();
    }
    let leading = |l: &str| l.len() - l.trim_start_matches([' ', '\t']).len();
    let own: Option<String> = lines[1..]
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l[..leading(l)].to_string())
        .filter(|ws| !ws.is_empty())
        .min_by_key(|ws| ws.len());
    let mut out = Vec::with_capacity(lines.len());
    out.push(lines[0].to_string());
    for l in &lines[1..] {
        if l.trim().is_empty() {
            out.push(String::new());
            continue;
        }
        let ws = &l[..leading(l)];
        let rest = &l[leading(l)..];
        let (depth, leftover) = match &own {
            Some(u) if !u.is_empty() => {
                let mut d = 0usize;
                let mut r = ws;
                while r.starts_with(u.as_str()) {
                    d += 1;
                    r = &r[u.len()..];
                }
                (d, r)
            }
            _ => (0, ws),
        };
        out.push(format!("{base}{}{leftover}{rest}", unit.repeat(depth)));
    }
    out.join("\n")
}
