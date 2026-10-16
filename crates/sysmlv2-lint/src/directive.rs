//! Suppression directives: a finding a project accepts at one site is
//! silenced where it sits, with its rule named, and the directives are
//! themselves policed (rule `lint-directive`) so a misspelled or stale
//! one never hides anything silently.
//!
//! The carrier is the hidden channel — `// …` line notes and
//! `//* … */` block notes — never a `/* … */` body, which is a
//! `Comment` element of the model. A note is a directive when its text
//! starts with [`PREFIX`]; four verbs follow it, each with the
//! comma-separated ids of the rules it governs and an optional
//! ` -- <reason>`:
//!
//! - `sysmlint-disable-next-line <rules>` governs the line after the
//!   note;
//! - `sysmlint-disable-line <rules>` governs the note's own line;
//! - `sysmlint-disable <rules>` opens a range from the note's line that
//!   `sysmlint-enable <rules>` closes on its own line, or that runs to
//!   the end of the unit when nothing re-enables the rule.
//!
//! A finding is suppressed when its primary span starts on a governed
//! line of its unit and its rule is listed; of the directives covering
//! it, the earliest in the source takes the credit, so a line directive
//! inside a range for the same rule suppresses nothing. Directives
//! filter what a pass reports, never what the rules see: a
//! majority-spelling tally still counts a suppressed site.
//!
//! Suppression applies whatever `lint-directive`'s own severity is;
//! that severity governs only the reports about the directives: one
//! that is malformed (an unknown verb or rule id, no rule named, an
//! `enable` with nothing to re-enable), one that suppresses nothing
//! (with a fix removing it), or one without a reason when the `reason`
//! option requires it. A directive naming a rule the configuration
//! turns off is dormant, not unused: it may be written for a stricter
//! policy elsewhere.

use std::collections::BTreeMap;

use sysmlv2_syntax::Span;
use sysmlv2_syntax::lexer::tokenize;
use sysmlv2_syntax::span::LineIndex;
use sysmlv2_syntax::token::TokenKind;

use crate::{Config, Edit, Finding, Fix, RuleId, Severity, finding};

/// What a note's text starts with to be read as a directive.
pub const PREFIX: &str = "sysmlint-";

/// The verb that governs the line after the note.
pub const NEXT_LINE: &str = "disable-next-line";

/// The directive a host writes above a finding's line to suppress one
/// rule there: `// sysmlint-disable-next-line <rule>`.
#[must_use]
pub fn next_line_directive(rule: &str) -> String {
    format!("// {PREFIX}{NEXT_LINE} {rule}")
}

/// Read `line` as a `// sysmlint-disable-next-line …` note: the rule
/// ids it lists and the byte offset in `line` where another id is
/// appended (before any ` -- reason`). `None` for any other line, block
/// notes included — a host extends a line note it would otherwise
/// duplicate, and writes a fresh one everywhere else.
#[must_use]
pub fn next_line_directive_rules(line: &str) -> Option<(Vec<&str>, usize)> {
    let body = line.trim_start().strip_prefix("//")?;
    if body.starts_with('*') {
        return None;
    }
    let after = body
        .trim_start()
        .strip_prefix(PREFIX)?
        .strip_prefix(NEXT_LINE)?;
    if !after.is_empty() && !after.starts_with(char::is_whitespace) {
        return None;
    }
    let (list, _) = split_reason(after.trim_start());
    let list = list.trim_end();
    let insert_at = offset_in(line, list) + list.len();
    Some((rule_items(list).collect(), insert_at))
}

/// Split what follows a verb into the rule list and the reason after
/// the first ` -- ` separator (a `--` at the start or after whitespace).
fn split_reason(rest: &str) -> (&str, Option<&str>) {
    let sep = rest
        .match_indices("--")
        .map(|(i, _)| i)
        .find(|&i| i == 0 || rest[..i].ends_with(char::is_whitespace));
    match sep {
        Some(i) => (
            &rest[..i],
            Some(rest[i + 2..].trim()).filter(|r| !r.is_empty()),
        ),
        None => (rest, None),
    }
}

/// The non-empty, trimmed items of a comma-separated list.
fn rule_items(list: &str) -> impl Iterator<Item = &str> {
    list.split(',').map(str::trim).filter(|s| !s.is_empty())
}

/// Byte offset of `part` (a subslice of `whole`) within `whole`.
fn offset_in(whole: &str, part: &str) -> usize {
    part.as_ptr() as usize - whole.as_ptr() as usize
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Verb {
    DisableNextLine,
    DisableLine,
    Disable,
    Enable,
}

const VERBS: &[(Verb, &str)] = &[
    (Verb::DisableNextLine, NEXT_LINE),
    (Verb::DisableLine, "disable-line"),
    (Verb::Disable, "disable"),
    (Verb::Enable, "enable"),
];

impl Verb {
    fn parse(word: &str) -> Option<Verb> {
        VERBS.iter().find(|(_, w)| *w == word).map(|(v, _)| *v)
    }

    fn word(self) -> &'static str {
        VERBS
            .iter()
            .find(|(v, _)| *v == self)
            .map_or("", |(_, w)| *w)
    }
}

/// One parsed directive note.
struct Directive {
    /// The whole note token.
    span: Span,
    /// The note's first and last line, 1-based.
    start_line: u32,
    end_line: u32,
    verb: Verb,
    /// The rules listed, each with the span of its spelling.
    rules: Vec<(RuleId, Span)>,
    /// The ` -- reason`, trimmed, when one is given.
    reason: Option<String>,
    /// A `//* … */` note (the re-spelling fix keeps the note's kind).
    block: bool,
}

/// One rule's suppression over a line range: the directive and mention
/// it came from, the `enable` that closed it, and whether it hid a
/// finding.
struct Suppression {
    rule: RuleId,
    from: u32,
    to: u32,
    directive: usize,
    mention: usize,
    closer: Option<(usize, usize)>,
    used: bool,
}

/// One unit's directive pass.
struct Scan<'a> {
    unit: usize,
    src: &'a str,
    lines: LineIndex,
    config: &'a Config,
    severity: Severity,
    reports: Vec<Finding>,
}

/// Apply the directives of every unit with text to `out`: the
/// suppressed findings are moved out and returned, the `lint-directive`
/// findings pushed (unless that rule is off). A unit without text keeps
/// its findings — the textual tier cannot read what it is not handed.
pub(crate) fn apply(
    config: &Config,
    units: &[(usize, &str, &str)],
    out: &mut Vec<Finding>,
) -> Vec<Finding> {
    let severity = config.cfg(RuleId::LintDirective).base;
    let mut suppressed = Vec::new();
    for &(unit, _, src) in units {
        // The common case costs one scan: no prefix, no directive.
        if !src.contains(PREFIX) {
            continue;
        }
        let mut scan = Scan {
            unit,
            src,
            lines: LineIndex::new(src),
            config,
            severity,
            reports: Vec::new(),
        };
        let directives = scan.parse_unit();
        if !directives.is_empty() {
            let mut sups = scan.suppressions(&directives);
            let mut kept = Vec::with_capacity(out.len());
            for f in out.drain(..) {
                let covered = match (f.unit, f.span) {
                    (Some(u), Some(span)) if u == unit => {
                        let line = scan.lines.line_col(span.start).line;
                        sups.iter_mut()
                            .find(|s| s.rule == f.rule && s.from <= line && line <= s.to)
                    }
                    _ => None,
                };
                match covered {
                    Some(s) => {
                        s.used = true;
                        suppressed.push(f);
                    }
                    None => kept.push(f),
                }
            }
            *out = kept;
            scan.unused(&directives, &sups);
        }
        if severity != Severity::Off {
            out.append(&mut scan.reports);
        }
    }
    suppressed
}

impl Scan<'_> {
    fn report(&mut self, span: Span, message: String) {
        let mut f = finding(RuleId::LintDirective, self.severity, message);
        f.unit = Some(self.unit);
        f.span = Some(span);
        self.reports.push(f);
    }

    /// Every directive of the unit, in source order; malformed ones are
    /// reported as they are met.
    fn parse_unit(&mut self) -> Vec<Directive> {
        let (tokens, _) = tokenize(self.src);
        tokens
            .iter()
            .filter(|t| matches!(t.kind, TokenKind::LineNote | TokenKind::BlockNote))
            .filter_map(|t| self.parse_note(t.span))
            .collect()
    }

    fn parse_note(&mut self, span: Span) -> Option<Directive> {
        let text = span.slice(self.src);
        let (block, inner) = match text.strip_prefix("//*") {
            Some(rest) => (true, rest.strip_suffix("*/").unwrap_or(rest)),
            None => (false, text.strip_prefix("//").unwrap_or(text)),
        };
        let after = inner.trim_start().strip_prefix(PREFIX)?;
        // Spans of pieces of the note text, as source offsets.
        let at = |part: &str| {
            let start = span.start + u32::try_from(offset_in(text, part)).unwrap_or(u32::MAX);
            Span::new(start, start + u32::try_from(part.len()).unwrap_or(0))
        };
        let (word, rest) = after.split_once(char::is_whitespace).unwrap_or((after, ""));
        let Some(verb) = Verb::parse(word) else {
            let word_span = at(word);
            let span = Span::new(word_span.start - PREFIX.len() as u32, word_span.end);
            self.report(
                span,
                format!(
                    "`{PREFIX}{word}` is not a lint directive; the directives are \
                     `{PREFIX}disable-next-line`, `{PREFIX}disable-line`, \
                     `{PREFIX}disable` and `{PREFIX}enable`"
                ),
            );
            return None;
        };
        let (list, reason) = split_reason(rest.trim_start());
        let mut rules: Vec<(RuleId, Span)> = Vec::new();
        for item in rule_items(list) {
            let item_span = at(item);
            match item.parse::<RuleId>() {
                Err(e) => self.report(item_span, e.to_string()),
                Ok(RuleId::LintConfig) => self.report(
                    item_span,
                    "`lint-config` findings have no location and cannot be suppressed".to_string(),
                ),
                Ok(RuleId::LintDirective) => self.report(
                    item_span,
                    "a directive cannot suppress `lint-directive`".to_string(),
                ),
                Ok(rule) if rules.iter().any(|(r, _)| *r == rule) => {
                    self.report(item_span, format!("`{rule}` is listed twice"));
                }
                Ok(rule) => rules.push((rule, item_span)),
            }
        }
        if rule_items(list).next().is_none() {
            self.report(
                span,
                "the directive names no rule; list the ids it governs, comma-separated".to_string(),
            );
        }
        if self.config.directive_reason_required && reason.is_none() {
            self.report(
                span,
                "the directive gives no reason; add ` -- <why>` after the rule list".to_string(),
            );
        }
        if rules.is_empty() {
            return None;
        }
        let start_line = self.lines.line_col(span.start).line;
        let end_line = self
            .lines
            .line_col(span.end.saturating_sub(1).max(span.start))
            .line;
        Some(Directive {
            span,
            start_line,
            end_line,
            verb,
            rules,
            reason: reason.map(str::to_string),
            block,
        })
    }

    /// The line ranges each directive governs, per listed rule. A
    /// `disable` of a rule already disabled adds nothing and is reported
    /// (with its removal); an `enable` of a rule not disabled is
    /// malformed.
    fn suppressions(&mut self, directives: &[Directive]) -> Vec<Suppression> {
        let mut sups: Vec<Suppression> = Vec::new();
        let mut open: BTreeMap<RuleId, usize> = BTreeMap::new();
        for (di, d) in directives.iter().enumerate() {
            for (mi, &(rule, mention)) in d.rules.iter().enumerate() {
                let sup = |from: u32, to: u32| Suppression {
                    rule,
                    from,
                    to,
                    directive: di,
                    mention: mi,
                    closer: None,
                    used: false,
                };
                match d.verb {
                    Verb::DisableNextLine => sups.push(sup(d.end_line + 1, d.end_line + 1)),
                    Verb::DisableLine => sups.push(sup(d.start_line, d.end_line)),
                    Verb::Disable => match open.get(&rule) {
                        Some(&si) => {
                            if self.config.cfg(rule).enabled() {
                                let since = directives[sups[si].directive].start_line;
                                let fix = self.removal_fix(directives, di, mi, None);
                                self.report(
                                    mention,
                                    format!(
                                        "`{rule}` is already disabled by the directive on line \
                                         {since}; this one suppresses nothing"
                                    ),
                                );
                                if let Some(f) = self.reports.last_mut() {
                                    f.fix = Some(fix);
                                }
                            }
                        }
                        None => {
                            open.insert(rule, sups.len());
                            sups.push(sup(d.start_line, u32::MAX));
                        }
                    },
                    Verb::Enable => match open.remove(&rule) {
                        Some(si) => {
                            sups[si].to = d.end_line;
                            sups[si].closer = Some((di, mi));
                        }
                        None => self.report(
                            mention,
                            format!("`{rule}` is not disabled here; nothing to re-enable"),
                        ),
                    },
                }
            }
        }
        sups
    }

    /// A suppression that hid nothing, for a rule the configuration
    /// runs, is reported at its mention with a fix removing it.
    fn unused(&mut self, directives: &[Directive], sups: &[Suppression]) {
        for s in sups.iter().filter(|s| !s.used) {
            if !self.config.cfg(s.rule).enabled() {
                continue;
            }
            let d = &directives[s.directive];
            let (place, what) = match (d.verb, s.closer) {
                (Verb::DisableNextLine | Verb::DisableLine, _) => {
                    (format!("on line {}", s.from), "directive")
                }
                (_, Some(_)) => (format!("between lines {} and {}", s.from, s.to), "range"),
                (_, None) => (format!("from line {} on", s.from), "directive"),
            };
            let fix = self.removal_fix(directives, s.directive, s.mention, s.closer);
            self.report(
                d.rules[s.mention].1,
                format!(
                    "`{}` is not reported {place}; the {what} suppresses nothing",
                    s.rule
                ),
            );
            if let Some(f) = self.reports.last_mut() {
                f.fix = Some(fix);
            }
        }
    }

    /// Remove mention `mi` of directive `di` (the whole note when it is
    /// the only rule listed), and the same from the `enable` closing it.
    fn removal_fix(
        &self,
        directives: &[Directive],
        di: usize,
        mi: usize,
        closer: Option<(usize, usize)>,
    ) -> Fix {
        let d = &directives[di];
        let rule = d.rules[mi].0;
        let mut edits = vec![self.drop_mention(d, mi)];
        let mut label = if d.rules.len() == 1 {
            "remove the unused directive".to_string()
        } else {
            format!("remove `{rule}` from the directive")
        };
        if let Some((cj, cm)) = closer {
            let c = &directives[cj];
            edits.push(self.drop_mention(c, cm));
            label.push_str(if c.rules.len() == 1 {
                " and its `enable`"
            } else {
                " and from its `enable`"
            });
        }
        Fix {
            label,
            deletes: true,
            semantic: false,
            edits,
        }
    }

    fn drop_mention(&self, d: &Directive, mi: usize) -> Edit {
        if d.rules.len() == 1 {
            let (start, end) = note_removal(self.src, d.span);
            return Edit {
                unit: self.unit,
                span: Span::new(start, end),
                replacement: String::new(),
            };
        }
        let rules: Vec<&str> = d
            .rules
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != mi)
            .map(|(_, (r, _))| r.id())
            .collect();
        let mut text = format!(
            "{} {PREFIX}{} {}",
            if d.block { "//*" } else { "//" },
            d.verb.word(),
            rules.join(", ")
        );
        if let Some(reason) = &d.reason {
            text.push_str(" -- ");
            text.push_str(reason);
        }
        if d.block {
            text.push_str(" */");
        }
        Edit {
            unit: self.unit,
            span: d.span,
            replacement: text,
        }
    }
}

/// The byte range deleting a note cleanly: its whole line(s) when it
/// has them to itself, the note and the whitespace before it when it
/// trails code, the note and the whitespace after it when code follows.
fn note_removal(src: &str, span: Span) -> (u32, u32) {
    let (start, end) = (span.start as usize, span.end as usize);
    let line_start = src[..start].rfind('\n').map_or(0, |i| i + 1);
    let line_end = src[end..].find('\n').map_or(src.len(), |i| end + i);
    let before = &src[line_start..start];
    let after = &src[end..line_end];
    let (from, to) = if before.trim().is_empty() && after.trim().is_empty() {
        (line_start, (line_end + 1).min(src.len()))
    } else if before.trim().is_empty() {
        (start, end + (after.len() - after.trim_start().len()))
    } else {
        (start - (before.len() - before.trim_end().len()), end)
    };
    (
        u32::try_from(from).unwrap_or(u32::MAX),
        u32::try_from(to).unwrap_or(u32::MAX),
    )
}
