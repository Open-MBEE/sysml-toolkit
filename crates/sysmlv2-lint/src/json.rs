//! JSON projection of findings and diagnostics — the one report shape
//! `sysmlv2 lint --format json`, `sysmlv2 check --format json` and the
//! wasm `Session.lint` surface emit, so a consumer parses one schema
//! whichever verb produced it.
//!
//! ```text
//! {
//!   "findings": [
//!     {
//!       "stage": "lint" | "parse" | "context" | "referential" | "semantic",
//!       "rule": "<lint rule id>" | null,
//!       "severity": "error" | "warn" | "info" | "hint",
//!       "message": "…",
//!       "unit": <index> | null,   "unitName": "<name>" | null,
//!       "start": <byte>, "end": <byte>,                    // null without a location
//!       "line": …, "col": …, "endLine": …, "endCol": …,    // 1-based; null without a location
//!       "element": "<qualified name | @id>" | null,
//!       "suggest": "<respelled name>" | null,
//!       "fix": { "label", "deletes", "semantic",
//!                "edits": [ { "unit", "unitName", "start", "end", "replacement" } ] } | null,
//!       "alternatives": [ <fix>, … ]
//!     }
//!   ],
//!   "summary": { "errors", "warnings", "infos", "hints" }
//! }
//! ```
//!
//! Findings without a location (a `lint-config` complaint) carry null
//! for `unit`, `unitName` and every position. Positions are computed
//! from the unit's source text, indexed on first use, so a report over
//! many clean units never scans them.

use std::cell::OnceCell;
use std::collections::HashMap;

use serde_json::{Value, json};
use sysmlv2_syntax::span::LineIndex;
use sysmlv2_syntax::{Diagnostic, Span};

use crate::{Finding, Fix, Severity};

/// The units a report may cite, each under the index and name the
/// report spells. The lint engine numbers units its own way (library
/// units first), so a host maps every engine index a finding may
/// carry onto a reported one with [`Units::alias`] — the wasm session
/// aliases each unit to itself, the CLI aliases model units to
/// input-file indexes. An engine unit without an alias is reported
/// without a location rather than under a wrong unit.
#[derive(Default)]
pub struct Units<'a> {
    units: HashMap<usize, Unit<'a>>,
    engine: HashMap<usize, usize>,
}

struct Unit<'a> {
    name: String,
    text: &'a str,
    lines: OnceCell<LineIndex>,
}

impl<'a> Units<'a> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register the unit reported as `index`, with the name the report
    /// spells and the source text positions are computed from.
    pub fn add(&mut self, index: usize, name: impl Into<String>, text: &'a str) {
        self.units.insert(
            index,
            Unit {
                name: name.into(),
                text,
                lines: OnceCell::new(),
            },
        );
    }

    /// Report engine unit `engine_unit` (a `Finding::unit` or
    /// `Edit::unit`) as `index`.
    pub fn alias(&mut self, engine_unit: usize, index: usize) {
        self.engine.insert(engine_unit, index);
    }

    fn reported(&self, engine_unit: usize) -> Option<usize> {
        self.engine.get(&engine_unit).copied()
    }

    fn get(&self, index: usize) -> Option<&Unit<'a>> {
        self.units.get(&index)
    }
}

impl Unit<'_> {
    fn lines(&self) -> &LineIndex {
        self.lines.get_or_init(|| LineIndex::new(self.text))
    }
}

/// The report's severity vocabulary — the lint config spelling.
#[derive(Clone, Copy)]
enum Sev {
    Error,
    Warn,
    Info,
    Hint,
}

impl Sev {
    fn as_str(self) -> &'static str {
        match self {
            Sev::Error => "error",
            Sev::Warn => "warn",
            Sev::Info => "info",
            Sev::Hint => "hint",
        }
    }
}

/// A report under construction: findings in push order plus the
/// severity tallies for `summary`.
#[derive(Default)]
pub struct Report {
    findings: Vec<Value>,
    errors: usize,
    warnings: usize,
    infos: usize,
    hints: usize,
}

impl Report {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a lint finding. Its unit and any fix-edit units are
    /// translated through the table's aliases; an unaliased unit
    /// leaves the location null.
    pub fn push_finding(&mut self, f: &Finding, units: &Units<'_>) {
        let severity = match f.severity {
            Severity::Error => Sev::Error,
            Severity::Info => Sev::Info,
            Severity::Hint => Sev::Hint,
            Severity::Warn | Severity::Off => Sev::Warn,
        };
        self.tally(severity);
        let unit = f.unit.and_then(|u| units.reported(u));
        let mut item = item(
            "lint",
            Some(f.rule.id()),
            severity,
            &f.message,
            unit.zip(f.span),
            units,
        );
        item["element"] = json!(f.element);
        item["suggest"] = json!(f.suggest);
        item["fix"] = f.fix.as_ref().map_or(Value::Null, |fx| fix_json(fx, units));
        item["alternatives"] = Value::Array(
            f.alternatives
                .iter()
                .map(|fx| fix_json(fx, units))
                .collect(),
        );
        self.findings.push(item);
    }

    /// Add a checker diagnostic from `stage` (`parse`, `context`,
    /// `referential`, `semantic`) located in the unit reported as
    /// `index`. No alias translation: a parse-stage diagnostic belongs
    /// to a unit the engine never numbered, so the caller already
    /// speaks in reported indexes, and running those through the
    /// engine aliases would remap them wrongly wherever the two index
    /// spaces overlap.
    pub fn push_diagnostic(
        &mut self,
        stage: &str,
        index: usize,
        d: &Diagnostic,
        units: &Units<'_>,
    ) {
        let severity = match d.severity {
            sysmlv2_syntax::diag::Severity::Error => Sev::Error,
            sysmlv2_syntax::diag::Severity::Warning => Sev::Warn,
        };
        self.tally(severity);
        let mut item = item(
            stage,
            None,
            severity,
            &d.message,
            Some((index, d.span)),
            units,
        );
        item["element"] = Value::Null;
        item["suggest"] = Value::Null;
        item["fix"] = Value::Null;
        item["alternatives"] = json!([]);
        self.findings.push(item);
    }

    /// `(errors, warnings, infos, hints)` so far.
    #[must_use]
    pub fn counts(&self) -> (usize, usize, usize, usize) {
        (self.errors, self.warnings, self.infos, self.hints)
    }

    /// The report document: `{"findings": […], "summary": {…}}`.
    #[must_use]
    pub fn into_value(self) -> Value {
        json!({
            "findings": self.findings,
            "summary": {
                "errors": self.errors,
                "warnings": self.warnings,
                "infos": self.infos,
                "hints": self.hints,
            },
        })
    }

    fn tally(&mut self, severity: Sev) {
        match severity {
            Sev::Error => self.errors += 1,
            Sev::Warn => self.warnings += 1,
            Sev::Info => self.infos += 1,
            Sev::Hint => self.hints += 1,
        }
    }
}

/// The keys every item carries, whichever verb produced it; the
/// lint-only keys are added by the caller.
fn item(
    stage: &str,
    rule: Option<&str>,
    severity: Sev,
    message: &str,
    location: Option<(usize, Span)>,
    units: &Units<'_>,
) -> Value {
    let unit = location.map(|(u, _)| u);
    let entry = unit.and_then(|u| units.get(u));
    let (start, end) = location.map(|(_, s)| (s.start, s.end)).unzip();
    let (from, to) = location
        .zip(entry)
        .map(|((_, span), unit)| {
            let lines = unit.lines();
            (lines.line_col(span.start), lines.line_col(span.end))
        })
        .unzip();
    json!({
        "stage": stage,
        "rule": rule,
        "severity": severity.as_str(),
        "message": message,
        "unit": unit,
        "unitName": entry.map(|u| u.name.as_str()),
        "start": start,
        "end": end,
        "line": from.map(|p| p.line),
        "col": from.map(|p| p.col),
        "endLine": to.map(|p| p.line),
        "endCol": to.map(|p| p.col),
    })
}

fn fix_json(fx: &Fix, units: &Units<'_>) -> Value {
    let edits: Vec<Value> = fx
        .edits
        .iter()
        .map(|e| {
            let unit = units.reported(e.unit);
            json!({
                "unit": unit,
                "unitName": unit.and_then(|u| units.get(u)).map(|u| u.name.as_str()),
                "start": e.span.start,
                "end": e.span.end,
                "replacement": e.replacement,
            })
        })
        .collect();
    json!({
        "label": fx.label,
        "deletes": fx.deletes,
        "semantic": fx.semantic,
        "edits": edits,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Edit, RuleId};

    fn finding(unit: Option<usize>, span: Option<Span>) -> Finding {
        Finding {
            rule: RuleId::UnusedParameter,
            severity: Severity::Warn,
            message: "`radius` is never read".into(),
            unit,
            span,
            element: Some("P::T::radius".into()),
            suggest: None,
            fix: Some(Fix {
                label: "remove `radius`".into(),
                deletes: true,
                semantic: false,
                edits: vec![Edit {
                    unit: unit.unwrap_or(0),
                    span: span.unwrap_or_else(|| Span::new(0, 0)),
                    replacement: String::new(),
                }],
            }),
            alternatives: Vec::new(),
        }
    }

    #[test]
    fn findings_report_positions_under_aliased_units() {
        let text = "package P {\n    in radius : Real;\n}\n";
        let mut units = Units::new();
        units.add(0, "m.sysml", text);
        units.alias(7, 0); // engine unit 7 is the first (only) input
        let mut report = Report::new();
        report.push_finding(&finding(Some(7), Some(Span::new(19, 25))), &units);
        let (e, w, i, h) = report.counts();
        assert_eq!((e, w, i, h), (0, 1, 0, 0));
        let v = report.into_value();
        let f = &v["findings"][0];
        assert_eq!(f["stage"], "lint");
        assert_eq!(f["rule"], "unused-parameter");
        assert_eq!(f["severity"], "warn");
        assert_eq!(f["unit"], 0);
        assert_eq!(f["unitName"], "m.sysml");
        assert_eq!(
            (f["start"].as_u64(), f["end"].as_u64()),
            (Some(19), Some(25))
        );
        assert_eq!((f["line"].as_u64(), f["col"].as_u64()), (Some(2), Some(8)));
        assert_eq!(
            (f["endLine"].as_u64(), f["endCol"].as_u64()),
            (Some(2), Some(14))
        );
        assert_eq!(f["element"], "P::T::radius");
        assert_eq!(f["fix"]["deletes"], true);
        assert_eq!(f["fix"]["edits"][0]["unit"], 0);
        assert_eq!(f["fix"]["edits"][0]["unitName"], "m.sysml");
        assert_eq!(
            v["summary"],
            json!({"errors": 0, "warnings": 1, "infos": 0, "hints": 0})
        );
    }

    #[test]
    fn unlocated_findings_carry_nulls_not_zeros() {
        let units = Units::new();
        let mut report = Report::new();
        let mut f = finding(None, None);
        f.rule = RuleId::LintConfig;
        f.severity = Severity::Error;
        f.fix = None;
        report.push_finding(&f, &units);
        let v = report.into_value();
        let f = &v["findings"][0];
        for key in [
            "unit", "unitName", "start", "end", "line", "col", "endLine", "endCol", "fix",
        ] {
            assert!(f[key].is_null(), "{key} should be null: {f}");
        }
        assert_eq!(v["summary"]["errors"], 1);
    }

    #[test]
    fn unaliased_engine_units_lose_their_location_not_their_finding() {
        let text = "package P;\n";
        let mut units = Units::new();
        units.add(0, "m.sysml", text);
        units.alias(5, 0);
        let mut report = Report::new();
        // Engine unit 2 (a library unit, say) was never aliased: the
        // finding stays, its location and its edit's unit go null.
        report.push_finding(&finding(Some(2), Some(Span::new(0, 4))), &units);
        let v = report.into_value();
        let f = &v["findings"][0];
        assert_eq!(f["rule"], "unused-parameter");
        for key in ["unit", "unitName", "start", "end", "line", "col"] {
            assert!(f[key].is_null(), "{key}: {f}");
        }
        assert!(f["fix"]["edits"][0]["unit"].is_null(), "{f}");
        assert!(f["fix"]["edits"][0]["unitName"].is_null(), "{f}");
        assert_eq!(f["fix"]["edits"][0]["start"], 0);
        assert_eq!(v["summary"]["warnings"], 1);
    }

    #[test]
    fn diagnostics_share_the_finding_shape() {
        let text = "part def A {\n";
        let mut units = Units::new();
        units.add(3, "broken.sysml", text);
        let mut report = Report::new();
        report.push_diagnostic(
            "parse",
            3,
            &Diagnostic::error(Span::new(13, 13), "expected `}`"),
            &units,
        );
        report.push_diagnostic(
            "semantic",
            3,
            &Diagnostic::warning(Span::new(0, 4), "unused"),
            &units,
        );
        assert_eq!(report.counts(), (1, 1, 0, 0));
        let v = report.into_value();
        let d = &v["findings"][0];
        assert_eq!(d["stage"], "parse");
        assert!(d["rule"].is_null());
        assert_eq!(d["severity"], "error");
        assert_eq!(d["unit"], 3);
        assert_eq!(d["unitName"], "broken.sysml");
        assert_eq!((d["line"].as_u64(), d["col"].as_u64()), (Some(2), Some(1)));
        assert_eq!(d["alternatives"], json!([]));
        assert_eq!(v["findings"][1]["severity"], "warn");
        let keys: Vec<String> = d.as_object().unwrap().keys().cloned().collect();
        let mut units = Units::new();
        units.add(0, "m.sysml", text);
        units.alias(0, 0);
        let mut r = Report::new();
        r.push_finding(&finding(Some(0), Some(Span::new(0, 4))), &units);
        let lint_keys: Vec<String> = r.into_value()["findings"][0]
            .as_object()
            .unwrap()
            .keys()
            .cloned()
            .collect();
        assert_eq!(
            keys, lint_keys,
            "check and lint items must share one key set"
        );
    }
}
