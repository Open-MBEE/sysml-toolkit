//! Configurable lint rules over the resolved model: the
//! findings the checker deliberately does not emit — style, hygiene,
//! and dead-model observations that are project policy rather than
//! language law. Additive beside `check` (lint never blocks or changes
//! checking); closed-world (user units only — library elements are
//! exempt); deterministic (findings sorted by unit, position, rule).
//!
//! Config is JSON: `{ "rules": { "<id>": "off" | "hint" | "info" |
//! "warn" | "error" | { "severity": …, …options } } }`. Unknown rule
//! ids and options produce a configuration *finding* (never a silent
//! ignore); absent config means every rule at its default severity.
//!
//! **Scopes.** Every rule accepts a `scopes` object mapping abstract-
//! syntax metaclasses to per-context settings — the same policy knob
//! at stereotype granularity: `{"scopes": {"ActionDefinition": "off"}}`
//! silences a rule for one context, `{"severity": "off", "scopes":
//! {"PartDefinition": "warn"}}` enables it for exactly one. A scope
//! value is a severity string or an object (`severity`, plus
//! rule-specific keys: naming's `style`/`regex`, undocumented's
//! `depth`). The effective severity of an element is its scope's, else
//! the rule's base; a rule runs when its base or any scope is non-off.
//!
//! **Tiers.** Most rules read the resolved model. `indentation` reads
//! the *source text* instead — layout is not in the model — so it runs
//! only for the units a host hands to [`lint_with_sources`]; [`lint`]
//! (no text) reports a configuration finding rather than skipping it
//! silently.
//!
//! A finding may carry a [`Fix`]. Fixes that delete model text are
//! marked [`Fix::deletes`] so hosts can guard them behind explicit
//! opt-in. Findings also carry `element` (the engine's edit-target
//! spelling — a `::`-qualified name, or `@<id>` for anonymous
//! elements) and, for naming findings under a preset style, `suggest`
//! (the declared name re-spelled in the required style) — the hooks a
//! host's quick fixes key on.

use regex_lite::Regex;
use std::collections::{BTreeMap, BTreeSet};
use sysmlv2_model::json::{ElementRef, ResolvedModel};
use sysmlv2_syntax::Span;

/// How a rule's findings surface, in ascending gravity: `Hint` (an
/// unobtrusive nudge — editors render it faded, without a squiggle),
/// `Info`, `Warn`, `Error`. `Off` disables the rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    Off,
    Hint,
    Info,
    Warn,
    Error,
}

impl Severity {
    fn parse(s: &str) -> Option<Severity> {
        match s {
            "off" => Some(Severity::Off),
            "hint" => Some(Severity::Hint),
            "info" => Some(Severity::Info),
            "warn" => Some(Severity::Warn),
            "error" => Some(Severity::Error),
            _ => None,
        }
    }

    /// The config spelling ("off" | "hint" | "info" | "warn" | "error").
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::Off => "off",
            Severity::Hint => "hint",
            Severity::Info => "info",
            Severity::Warn => "warn",
            Severity::Error => "error",
        }
    }
}

/// The severity ladder in config spelling, ascending — for UIs and
/// validation messages.
pub const SEVERITIES: &[&str] = &["off", "hint", "info", "warn", "error"];

/// Naming style presets — the names are the config spellings.
pub const STYLES: &[(&str, &str)] = &[
    ("camelCase", "^[a-z][a-zA-Z0-9]*$"),
    ("PascalCase", "^[A-Z][a-zA-Z0-9]*$"),
    ("snake_case", "^[a-z][a-z0-9_]*$"),
    ("UPPER_SNAKE_CASE", "^[A-Z][A-Z0-9_]*$"),
    ("kebab-case", "^[a-z][a-z0-9-]*$"),
];

/// Style-preset names, for inventories and validation messages.
pub fn style_names() -> Vec<&'static str> {
    STYLES.iter().map(|(n, _)| *n).collect()
}

/// One scope a rule's inventory advertises — what a configuration UI
/// renders as a per-context row. `default` `None` = inherits the
/// rule's base severity; `Some` seeds the scope softly (it holds
/// while the rule is on, but `"off"` at the rule level silences it —
/// only a user-set severity survives that); `default_style` only for
/// styled rules. Config accepts metaclass keys beyond this list (the
/// inventory curates the UI, it does not bound the policy).
pub struct ScopeInfo {
    pub key: &'static str,
    pub label: &'static str,
    pub default: Option<Severity>,
    pub default_style: Option<&'static str>,
}

/// One rule's identity and configuration surface: stable kebab-case
/// id, one-line description (doubles as UI copy), default severity,
/// the scopes its inventory advertises, the style presets its scopes
/// accept (empty = severity-only scopes), and family-level style
/// options (`(key, label, default style)`).
pub struct Rule {
    pub id: &'static str,
    pub description: &'static str,
    pub default: Severity,
    pub scopes: &'static [ScopeInfo],
    pub styles: &'static [&'static str],
    pub families: &'static [(&'static str, &'static str, &'static str)],
    /// Rule-level options beyond severity — what a configuration UI
    /// renders as typed controls instead of raw JSON.
    pub options: &'static [OptionInfo],
}

/// One rule option's identity and value shape (`{"rules": {"<id>":
/// {"severity": …, "<key>": <value>}}}`).
pub struct OptionInfo {
    pub key: &'static str,
    pub label: &'static str,
    pub kind: OptionKind,
}

/// What an option accepts — the control a form should offer.
pub enum OptionKind {
    /// A whole number at or above `min`, with `zero` naming what 0
    /// means where it is a legal sentinel below that floor.
    Int {
        default: i64,
        min: i64,
        zero: Option<&'static str>,
    },
    /// One of a fixed set of names; `default` absent = the rule's own
    /// behavior when unset.
    Choice {
        default: Option<&'static str>,
        values: &'static [&'static str],
    },
}

const STYLE_NAMES: &[&str] = &[
    "camelCase",
    "PascalCase",
    "snake_case",
    "UPPER_SNAKE_CASE",
    "kebab-case",
];

macro_rules! scope {
    ($key:literal, $label:literal) => {
        ScopeInfo {
            key: $key,
            label: $label,
            default: None,
            default_style: None,
        }
    };
    ($key:literal, $label:literal, off) => {
        ScopeInfo {
            key: $key,
            label: $label,
            default: Some(Severity::Off),
            default_style: None,
        }
    };
}

const NAMING_SCOPES: &[ScopeInfo] = &[
    scope!("PartDefinition", "part def"),
    scope!("ItemDefinition", "item def"),
    scope!("AttributeDefinition", "attribute def"),
    scope!("PortDefinition", "port def"),
    scope!("ActionDefinition", "action def"),
    scope!("StateDefinition", "state def"),
    scope!("ConstraintDefinition", "constraint def"),
    scope!("CalculationDefinition", "calc def"),
    scope!("RequirementDefinition", "requirement def"),
    scope!("EnumerationDefinition", "enum def"),
    scope!("PartUsage", "part"),
    scope!("AttributeUsage", "attribute"),
    scope!("PortUsage", "port"),
    scope!("ActionUsage", "action"),
    scope!("StateUsage", "state"),
    scope!("EnumerationUsage", "enum literal"),
];

const UNUSED_PARAM_SCOPES: &[ScopeInfo] = &[
    scope!("CalculationDefinition", "calc def"),
    scope!("ConstraintDefinition", "constraint def"),
    scope!("ActionDefinition", "action def"),
];

const UNTYPED_SCOPES: &[ScopeInfo] = &[
    scope!("PartUsage", "part"),
    scope!("ItemUsage", "item"),
    scope!("AttributeUsage", "attribute"),
    scope!("PortUsage", "port"),
    scope!("ActionUsage", "action"),
    scope!("StateUsage", "state"),
    scope!("EnumerationUsage", "enum literal", off),
    scope!("TransitionUsage", "transition", off),
];

const DEF_SCOPES: &[ScopeInfo] = &[
    scope!("PartDefinition", "part def"),
    scope!("ItemDefinition", "item def"),
    scope!("AttributeDefinition", "attribute def"),
    scope!("PortDefinition", "port def"),
    scope!("ActionDefinition", "action def"),
    scope!("StateDefinition", "state def"),
    scope!("ConstraintDefinition", "constraint def"),
    scope!("CalculationDefinition", "calc def"),
    scope!("RequirementDefinition", "requirement def"),
    scope!("EnumerationDefinition", "enum def"),
];

/// Every rule the engine knows, in documentation order.
pub const RULES: &[Rule] = &[
    Rule {
        id: "naming-convention",
        description: "a declared name off the project's casing conventions — definitions \
                      PascalCase, usages and features camelCase by default; families and \
                      per-stereotype scopes take a style preset or a regex (info by \
                      default: a nudge, not a verdict — tighten or disable per project)",
        default: Severity::Info,
        scopes: NAMING_SCOPES,
        styles: STYLE_NAMES,
        families: &[
            ("definitions", "definitions (family default)", "PascalCase"),
            (
                "usages",
                "usages and features (family default)",
                "camelCase",
            ),
        ],
        options: NAMING_OPTIONS,
    },
    Rule {
        id: "undocumented-element",
        description: "a definition without a documentation body — its own `doc` or a \
                      comment written `about` it; `depth` extends below the top-level \
                      default, scopes tune severity and depth per stereotype",
        default: Severity::Off,
        scopes: DEF_SCOPES,
        styles: &[],
        families: &[],
        options: UNDOCUMENTED_OPTIONS,
    },
    Rule {
        id: "untyped-usage",
        description: "a named usage declaring no typing, subsetting, or redefinition \
                      clause; enumeration literals and transitions are off by default \
                      (scopes re-enable or silence per stereotype)",
        default: Severity::Off,
        scopes: UNTYPED_SCOPES,
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "unused-definition",
        description: "a user definition nothing in the user model references (closed \
                      world: off by default — models are interchange artifacts and \
                      outside consumers are invisible here)",
        default: Severity::Off,
        scopes: DEF_SCOPES,
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "unused-parameter",
        description: "an input parameter of a calc/constraint/action definition never \
                      used in its body (fix: delete the parameter); scopes toggle each \
                      definition context; off by default",
        default: Severity::Off,
        scopes: UNUSED_PARAM_SCOPES,
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "unit-spelling",
        description: "quantity-bracket unit spellings — the same unit spelled two ways \
                      across the model (`'m⋅s⁻¹'` here, `m/s` there), and, with the \
                      `style` option (`quoted-product` | `expression`), any multi-factor \
                      spelling off the preferred form (fix: re-spell); off by default",
        default: Severity::Off,
        scopes: &[],
        styles: &[],
        families: &[],
        options: UNIT_OPTIONS,
    },
    Rule {
        id: "dimensional-consistency",
        description: "a quantity attribute whose declared type and value unit disagree \
                      dimensionally (`: MassValue = 9.8 [m/s^2]` — fix: re-type to the \
                      unit's quantity type); the `untyped` scope (warn by default) \
                      covers an untyped attribute whose value determines a type to \
                      declare (fix: write the inferred type). Both sides must be \
                      determinate — models without the standard library stay silent",
        default: Severity::Warn,
        scopes: DIMENSIONAL_SCOPES,
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "qualified-names",
        description: "one element, one reference spelling — the same target written \
                      `MassValue` here and `ISQ::MassValue` there flags the minority \
                      sites (fix: re-spell to the majority form); the `style` option \
                      enforces a policy instead: `qualified` (always fully \
                      qualified), `minimal` (qualify only where a shorter spelling \
                      would not resolve), `imported` (simple names, the fix adding \
                      an import when the target is not yet visible and the simple \
                      name is free); off by default",
        default: Severity::Off,
        scopes: &[],
        styles: &[],
        families: &[],
        options: QUALIFIED_OPTIONS,
    },
    Rule {
        id: "multiline-conditions",
        description: "a long condition chain written on one source line — chains of \
                      `min` or more operands (default 3) read best one condition per \
                      line, the connective leading each continuation, which is what \
                      Format Document produces; `min` also carries the formatter's \
                      threshold (0 keeps chains inline everywhere); off by default",
        default: Severity::Off,
        scopes: CHAIN_SCOPES,
        styles: &[],
        families: &[],
        options: CHAIN_OPTIONS,
    },
    Rule {
        id: "indentation",
        description: "leading whitespace off the project's indentation style — tabs by \
                      default, or a fixed number of spaces (`style` picks the character, \
                      `size` the columns one level takes); lines inside a verbatim \
                      `/* … */` body or a multi-line note keep the author's layout and \
                      are never flagged (fix: re-indent the line); off by default",
        default: Severity::Off,
        scopes: &[],
        styles: &[],
        families: &[],
        options: INDENT_OPTIONS,
    },
    Rule {
        id: "generated-provenance-invalid",
        description: "corrupted transformer ownership — a Generated marker without a \
                      provenance record, a record whose `about` target is missing, \
                      multiple, unmarked, or carries the wrong key, duplicate \
                      (transformId, key) claims, a provenance record and an exclusion \
                      for one pair, malformed baseline digests, or stores/records \
                      outside the derived sidecar contract; managed content whose \
                      ownership is corrupt must be repaired or adopted explicitly, \
                      never silently treated as hand-written",
        default: Severity::Error,
        scopes: &[],
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "generated-provenance-baseline-outdated",
        description: "a provenance record predating the structure/policy baseline \
                      fields — valid legacy provenance, not tamper; the next \
                      successful sync backfills the record without changing the \
                      generated member",
        default: Severity::Info,
        scopes: &[],
        styles: &[],
        families: &[],
        options: &[],
    },
    Rule {
        id: "generated-element-modified",
        description: "a generated member drifting from its provenance baseline, \
                      classified without consulting the data source: a changed \
                      canonicalization policy/schema is baseline drift the next sync \
                      refreshes, a changed id-normalized structure is a semantic edit, \
                      and an equal structure whose spelling left the canonical form is \
                      format-only drift; raise to `error` for a hard gate — the \
                      transformer still heals it, since repair updates member and \
                      record in one candidate model",
        default: Severity::Warn,
        scopes: &[],
        styles: &[],
        families: &[],
        options: &[],
    },
];

const UNDOCUMENTED_OPTIONS: &[OptionInfo] = &[OptionInfo {
    key: "depth",
    label: "documented depth (levels below a top-level definition)",
    kind: OptionKind::Int {
        default: 1,
        min: 1,
        zero: None,
    },
}];

const UNIT_OPTIONS: &[OptionInfo] = &[OptionInfo {
    key: "style",
    label: "compound unit spelling",
    kind: OptionKind::Choice {
        default: None,
        values: &["quoted-product", "expression"],
    },
}];

const QUALIFIED_OPTIONS: &[OptionInfo] = &[OptionInfo {
    key: "style",
    label: "reference qualification policy",
    kind: OptionKind::Choice {
        default: None,
        values: &["qualified", "minimal", "imported"],
    },
}];

const CHAIN_OPTIONS: &[OptionInfo] = &[OptionInfo {
    key: "min",
    label: "conditions before a chain breaks across lines",
    kind: OptionKind::Int {
        default: sysmlv2_syntax::print::FORMAT_CHAIN_MIN as i64,
        min: 2,
        zero: Some("keep chains inline everywhere"),
    },
}];

const NAMING_OPTIONS: &[OptionInfo] = &[];

const INDENT_OPTIONS: &[OptionInfo] = &[
    OptionInfo {
        key: "style",
        label: "indentation character",
        kind: OptionKind::Choice {
            default: Some("tabs"),
            values: &["tabs", "spaces"],
        },
    },
    OptionInfo {
        key: "size",
        label: "columns one indentation level occupies",
        kind: OptionKind::Int {
            default: DEFAULT_INDENT_SIZE as i64,
            min: 1,
            zero: None,
        },
    },
];

/// Columns one indentation level occupies when the project indents with
/// spaces — and the tab width the rule assumes when measuring existing
/// leading whitespace.
pub const DEFAULT_INDENT_SIZE: u8 = 4;

/// `dimensional-consistency` contexts are the rule's two aspects, not
/// metaclasses: `mismatch` (declared type vs value unit, the rule's
/// base severity) and `untyped` (type inference for untyped
/// attributes — an unobtrusive hint unless the scope re-tunes it; the
/// default is applied in the rule, not seeded, so `"off"` stays off).
const DIMENSIONAL_SCOPES: &[ScopeInfo] = &[
    ScopeInfo {
        key: "mismatch",
        label: "declared type vs value unit",
        default: None,
        default_style: None,
    },
    ScopeInfo {
        key: "untyped",
        label: "untyped attribute with an inferable type",
        default: Some(Severity::Warn),
        default_style: None,
    },
];

const CHAIN_SCOPES: &[ScopeInfo] = &[
    scope!("ConstraintUsage", "constraint"),
    scope!("AssertConstraintUsage", "assert constraint"),
    scope!("ConstraintDefinition", "constraint def"),
    scope!("RequirementUsage", "requirement"),
    scope!("RequirementDefinition", "requirement def"),
    scope!("SatisfyRequirementUsage", "satisfy"),
    scope!("Invariant", "invariant"),
];

fn rule(id: &str) -> Option<&'static Rule> {
    RULES.iter().find(|r| r.id == id)
}

/// A compiled naming pattern with the words used to describe it in
/// findings and, for presets, the style name suggestions convert to.
#[derive(Clone)]
struct Pattern {
    regex: Regex,
    describe: String,
    style: Option<&'static str>,
}

impl Pattern {
    fn preset(name: &str) -> Option<Pattern> {
        let (style, source) = STYLES.iter().find(|(n, _)| *n == name)?;
        Some(Pattern {
            regex: Regex::new(source).expect("built-in style compiles"),
            describe: (*style).to_string(),
            style: Some(style),
        })
    }

    fn custom(source: &str) -> Result<Pattern, String> {
        Ok(Pattern {
            regex: Regex::new(source).map_err(|e| e.to_string())?,
            describe: format!("match the configured pattern `{source}`"),
            style: None,
        })
    }
}

/// Per-scope overrides — everything optional, absent = inherit.
#[derive(Clone, Default)]
struct ScopeSetting {
    severity: Option<Severity>,
    pattern: Option<Pattern>,
    depth: Option<u32>,
    /// The severity came from the inventory's advertised default, not
    /// the user's config. Seeded severities are soft: they neither
    /// keep a rule alive under `"off"` nor survive it (a user-set
    /// scope severity does both).
    seeded: bool,
}

/// One rule's effective configuration: base severity + scope map,
/// seeded from the rule's inventory defaults and overlaid by config.
#[derive(Clone)]
struct RuleConfig {
    base: Severity,
    scopes: BTreeMap<String, ScopeSetting>,
}

impl RuleConfig {
    fn seeded(r: &Rule) -> RuleConfig {
        let mut scopes = BTreeMap::new();
        for s in r.scopes {
            if s.default.is_some() || s.default_style.is_some() {
                scopes.insert(
                    s.key.to_string(),
                    ScopeSetting {
                        severity: s.default,
                        pattern: s.default_style.and_then(Pattern::preset),
                        depth: None,
                        seeded: true,
                    },
                );
            }
        }
        RuleConfig {
            base: r.default,
            scopes,
        }
    }

    /// Effective severity for a metaclass; `Off` = skip the element.
    /// A seeded severity applies only while the rule itself is on —
    /// `"off"` at the rule level silences advertised scope defaults.
    fn severity(&self, metaclass: &str) -> Severity {
        match self.scopes.get(metaclass) {
            Some(s) if s.seeded && self.base == Severity::Off => Severity::Off,
            Some(s) => s.severity.unwrap_or(self.base),
            None => self.base,
        }
    }

    /// Whether anything at all can fire. Seeded severities don't
    /// count: only a user-set scope re-enables an off rule.
    fn enabled(&self) -> bool {
        self.base != Severity::Off
            || self
                .scopes
                .values()
                .any(|s| !s.seeded && matches!(s.severity, Some(sev) if sev != Severity::Off))
    }
}

/// Effective rule configurations: inventory defaults overlaid with
/// config and any host overrides. Unknown ids, options, and malformed
/// values collect as configuration findings.
pub struct Config {
    rules: BTreeMap<&'static str, RuleConfig>,
    naming_definitions: Pattern,
    naming_usages: Pattern,
    undocumented_depth: u32,
    /// `unit-spelling`'s preferred multi-factor form; `None` = flag
    /// inconsistencies only.
    unit_style: Option<UnitStyle>,
    /// `qualified-names`' qualification policy; `None` = flag
    /// inconsistent spellings of one element only.
    qualified_style: Option<QualifiedStyle>,
    /// `multiline-conditions`' operand threshold — findings and the
    /// formatter both key on it; 0 keeps chains inline everywhere.
    chain_min: u8,
    /// `indentation`'s character and the width one level takes —
    /// findings and the formatter both key on them
    /// ([`Config::format_indent`]).
    indent_style: IndentStyle,
    indent_size: u8,
    /// Complaints gathered while reading config — surfaced as
    /// `lint-config` findings so a typo never silently disables a rule.
    complaints: Vec<String>,
}

/// The `indentation` rule's style presets: which character carries one
/// level of leading whitespace. Tabs by default — the width is then the
/// reader's choice, which is the point.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IndentStyle {
    Tabs,
    Spaces,
}

/// The `unit-spelling` rule's style presets: how a multi-factor unit
/// should be written in a quantity bracket.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UnitStyle {
    /// A single quoted power-product name: `'m⋅s⁻¹'`, `'m³⋅s⁻²'`.
    QuotedProduct,
    /// A unit arithmetic expression: `m/s`, `m**3/s**2`.
    Expression,
}

/// The `qualified-names` rule's qualification policies: how a
/// reference should spell its target when the option is set (unset =
/// flag inconsistent spellings of one element only).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum QualifiedStyle {
    /// Always the full owner-chain qualification (`ISQBase::MassValue`).
    Qualified,
    /// The shortest spelling that resolves at the site — qualify only
    /// where a shorter spelling would not (the "on conflict" policy;
    /// an imported target reads as its simple name).
    Minimal,
    /// Simple names everywhere they are free: an already-visible
    /// target re-spells directly, an invisible one gains an import; a
    /// simple name bound to a *different* element keeps the written
    /// qualification (no finding).
    Imported,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            rules: RULES
                .iter()
                .map(|r| (r.id, RuleConfig::seeded(r)))
                .collect(),
            naming_definitions: Pattern::preset("PascalCase").unwrap(),
            naming_usages: Pattern::preset("camelCase").unwrap(),
            undocumented_depth: 1,
            unit_style: None,
            qualified_style: None,
            chain_min: sysmlv2_syntax::print::FORMAT_CHAIN_MIN,
            indent_style: IndentStyle::Tabs,
            indent_size: DEFAULT_INDENT_SIZE,
            complaints: Vec::new(),
        }
    }
}

impl Config {
    /// The multiline-chain threshold for formatters: `None` keeps
    /// chains inline, `Some(n)` breaks chains of ≥ n operands (the
    /// `multiline-conditions` rule's `min` option; defaults to the
    /// formatter's own [`sysmlv2_syntax::print::FORMAT_CHAIN_MIN`]).
    pub fn format_chain_min(&self) -> Option<u8> {
        match self.chain_min {
            0 => None,
            n => Some(n),
        }
    }

    /// The project's indentation style for printers and formatters (the
    /// `indentation` rule's `style`/`size` options; tabs by default).
    /// Independent of the rule's severity: the style is the project's
    /// even when nobody wants findings about it.
    pub fn format_indent(&self) -> sysmlv2_syntax::print::Indent {
        match self.indent_style {
            IndentStyle::Tabs => sysmlv2_syntax::print::Indent::Tabs,
            IndentStyle::Spaces => sysmlv2_syntax::print::Indent::Spaces(self.indent_size),
        }
    }

    /// Parse the JSON config form. Errors are unreadable JSON only —
    /// unknown ids/levels/options become findings, not errors.
    pub fn from_json(text: &str) -> Result<Config, String> {
        let v: serde_json::Value =
            serde_json::from_str(text).map_err(|e| format!("config is not JSON: {e}"))?;
        let mut cfg = Config::default();
        let Some(rules) = v.get("rules") else {
            return Ok(cfg);
        };
        let Some(rules) = rules.as_object() else {
            cfg.complaints
                .push("`rules` should be an object of rule-id → level".to_string());
            return Ok(cfg);
        };
        for (id, val) in rules {
            match val {
                serde_json::Value::String(s) => match Severity::parse(s) {
                    Some(level) => cfg.set(id, level),
                    None => cfg.complaints.push(format!(
                        "rule `{id}`: level must be one of {}",
                        SEVERITIES.join(", ")
                    )),
                },
                serde_json::Value::Object(o) => {
                    if let Some(s) = o.get("severity") {
                        match s.as_str().and_then(Severity::parse) {
                            Some(level) => cfg.set(id, level),
                            None => cfg.complaints.push(format!(
                                "rule `{id}`: severity must be one of {}",
                                SEVERITIES.join(", ")
                            )),
                        }
                    }
                    for (key, val) in o.iter().filter(|(k, _)| *k != "severity") {
                        cfg.set_option(id, key, val);
                    }
                }
                _ => cfg.complaints.push(format!(
                    "rule `{id}`: level must be one of {}",
                    SEVERITIES.join(", ")
                )),
            }
        }
        Ok(cfg)
    }

    /// Override one rule's base severity (the CLI's `--rule id=level`).
    /// Unknown ids become configuration findings.
    pub fn set(&mut self, id: &str, level: Severity) {
        match rule(id) {
            Some(r) => self.rules.get_mut(r.id).expect("seeded").base = level,
            None => self.complaints.push(format!("unknown lint rule `{id}`")),
        }
    }

    /// Apply one rule option from config. Unknown keys and malformed
    /// values become configuration findings; the rule keeps its
    /// defaults for anything that fails to parse.
    fn set_option(&mut self, id: &str, key: &str, val: &serde_json::Value) {
        let complaint = match (id, key) {
            ("naming-convention", "definitions" | "usages") => match parse_style_spec(val) {
                Ok(pat) => {
                    match key {
                        "definitions" => self.naming_definitions = pat,
                        _ => self.naming_usages = pat,
                    }
                    return;
                }
                Err(e) => format!("rule `{id}`: option `{key}` {e}"),
            },
            ("unit-spelling", "style") => match val.as_str() {
                Some("quoted-product") => {
                    self.unit_style = Some(UnitStyle::QuotedProduct);
                    return;
                }
                Some("expression") => {
                    self.unit_style = Some(UnitStyle::Expression);
                    return;
                }
                _ => {
                    format!("rule `{id}`: option `{key}` must be `quoted-product` or `expression`")
                }
            },
            ("qualified-names", "style") => match val.as_str() {
                Some("qualified") => {
                    self.qualified_style = Some(QualifiedStyle::Qualified);
                    return;
                }
                Some("minimal") => {
                    self.qualified_style = Some(QualifiedStyle::Minimal);
                    return;
                }
                Some("imported") => {
                    self.qualified_style = Some(QualifiedStyle::Imported);
                    return;
                }
                _ => {
                    format!(
                        "rule `{id}`: option `{key}` must be `qualified`, `minimal`, or `imported`"
                    )
                }
            },
            ("undocumented-element", "depth") => match val.as_u64() {
                Some(d) if d >= 1 => {
                    self.undocumented_depth = d.min(u32::MAX as u64) as u32;
                    return;
                }
                _ => format!("rule `{id}`: option `{key}` must be a positive integer"),
            },
            ("multiline-conditions", "min") => match val.as_u64() {
                Some(0) => {
                    self.chain_min = 0;
                    return;
                }
                Some(n) if n >= 2 => {
                    self.chain_min = n.min(u8::MAX as u64) as u8;
                    return;
                }
                _ => format!(
                    "rule `{id}`: option `{key}` must be 0 (keep chains inline) or an \
                     integer ≥ 2"
                ),
            },
            ("indentation", "style") => match val.as_str() {
                Some("tabs") => {
                    self.indent_style = IndentStyle::Tabs;
                    return;
                }
                Some("spaces") => {
                    self.indent_style = IndentStyle::Spaces;
                    return;
                }
                _ => format!("rule `{id}`: option `{key}` must be `tabs` or `spaces`"),
            },
            ("indentation", "size") => match val.as_u64() {
                Some(n) if n >= 1 => {
                    self.indent_size = n.min(u8::MAX as u64) as u8;
                    return;
                }
                _ => format!("rule `{id}`: option `{key}` must be a positive integer"),
            },
            (_, "scopes") if rule(id).is_some() => {
                let Some(map) = val.as_object() else {
                    self.complaints.push(format!(
                        "rule `{id}`: `scopes` must be an object of metaclass → setting"
                    ));
                    return;
                };
                for (scope_key, scope_val) in map {
                    self.set_scope(id, scope_key, scope_val);
                }
                return;
            }
            _ => format!("rule `{id}`: unknown option `{key}`"),
        };
        self.complaints.push(complaint);
    }

    /// One `scopes` entry: key validated against the rule's context
    /// shape, value = severity string, style name (styled rules), or
    /// an object of per-scope settings.
    fn set_scope(&mut self, id: &str, key: &str, val: &serde_json::Value) {
        let Some(r) = rule(id) else { return };
        let valid_key = r.scopes.iter().any(|s| s.key == key)
            || match id {
                "unused-parameter" => false, // strict: the three contexts only
                // Textual rule: a line has no metaclass to scope by.
                "indentation" => false,
                // Aspect scopes, not metaclasses: the two inventory keys only.
                "dimensional-consistency" => false,
                // Reference sites have no metaclass to scope by.
                "qualified-names" => false,
                "untyped-usage" => key.ends_with("Usage"),
                "undocumented-element" | "unused-definition" => key.ends_with("Definition"),
                _ => key.ends_with("Definition") || key.ends_with("Usage") || key == "Feature",
            };
        if !valid_key {
            self.complaints.push(format!(
                "rule `{id}`: `scopes` key `{key}` is not a known context"
            ));
            return;
        }
        let styled = !r.styles.is_empty();
        let mut setting = ScopeSetting::default();
        match val {
            serde_json::Value::String(s) => {
                if let Some(sev) = Severity::parse(s) {
                    setting.severity = Some(sev);
                } else if styled && Pattern::preset(s).is_some() {
                    setting.pattern = Pattern::preset(s);
                } else {
                    self.complaints.push(format!(
                        "rule `{id}`: scope `{key}` wants a severity{}",
                        if styled { " or style name" } else { "" }
                    ));
                    return;
                }
            }
            serde_json::Value::Object(o) => {
                for (k, v) in o {
                    match (k.as_str(), v) {
                        ("severity", v) => match v.as_str().and_then(Severity::parse) {
                            Some(sev) => setting.severity = Some(sev),
                            None => self.complaints.push(format!(
                                "rule `{id}`: scope `{key}`: severity must be one of {}",
                                SEVERITIES.join(", ")
                            )),
                        },
                        ("style", v) if styled => match v.as_str().and_then(Pattern::preset) {
                            Some(p) => setting.pattern = Some(p),
                            None => self.complaints.push(format!(
                                "rule `{id}`: scope `{key}`: style must be one of {}",
                                STYLE_NAMES.join(", ")
                            )),
                        },
                        ("regex", v) if styled => match v.as_str() {
                            Some(src) => match Pattern::custom(src) {
                                Ok(p) => setting.pattern = Some(p),
                                Err(e) => self.complaints.push(format!(
                                    "rule `{id}`: scope `{key}`: regex is invalid: {e}"
                                )),
                            },
                            None => self.complaints.push(format!(
                                "rule `{id}`: scope `{key}`: regex must be a string"
                            )),
                        },
                        ("depth", v) if id == "undocumented-element" => match v.as_u64() {
                            Some(d) if d >= 1 => {
                                setting.depth = Some(d.min(u32::MAX as u64) as u32)
                            }
                            _ => self.complaints.push(format!(
                                "rule `{id}`: scope `{key}`: depth must be a positive integer"
                            )),
                        },
                        (other, _) => self.complaints.push(format!(
                            "rule `{id}`: scope `{key}`: unknown setting `{other}`"
                        )),
                    }
                }
            }
            _ => {
                self.complaints.push(format!(
                    "rule `{id}`: scope `{key}` wants a severity{} or an object",
                    if styled { ", a style name," } else { "" }
                ));
                return;
            }
        }
        // Overlay onto any seeded entry (a config severity flip keeps
        // the seeded style, and vice versa).
        let entry = self
            .rules
            .get_mut(r.id)
            .expect("seeded")
            .scopes
            .entry(key.to_string())
            .or_default();
        if setting.severity.is_some() {
            entry.severity = setting.severity;
            entry.seeded = false;
        }
        if setting.pattern.is_some() {
            entry.pattern = setting.pattern;
        }
        if setting.depth.is_some() {
            entry.depth = setting.depth;
        }
    }

    fn cfg(&self, id: &str) -> &RuleConfig {
        self.rules.get(id).expect("every rule is seeded")
    }
}

/// A family style spec: a preset name or `{"regex": "…"}`.
fn parse_style_spec(val: &serde_json::Value) -> Result<Pattern, String> {
    match val {
        serde_json::Value::String(s) => Pattern::preset(s).ok_or_else(|| {
            format!(
                "must be a style preset ({}) or {{\"regex\": …}}",
                STYLE_NAMES.join(", ")
            )
        }),
        serde_json::Value::Object(o) => match o.get("regex").and_then(|v| v.as_str()) {
            Some(src) => Pattern::custom(src).map_err(|e| format!("regex is invalid: {e}")),
            None => Err("must be a style preset or {\"regex\": …}".to_string()),
        },
        _ => Err(format!(
            "must be a style preset ({}) or {{\"regex\": …}}",
            STYLE_NAMES.join(", ")
        )),
    }
}

/// Re-spell `name` in a preset style: split into words on `_`, `-`,
/// spaces, and lower→upper case boundaries, then recompose. `None`
/// when the name yields no words.
pub fn convert_to_style(name: &str, style: &str) -> Option<String> {
    let mut words: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut prev_lower = false;
    for c in name.chars() {
        if c == '_' || c == '-' || c.is_whitespace() {
            if !cur.is_empty() {
                words.push(std::mem::take(&mut cur));
            }
            prev_lower = false;
            continue;
        }
        if c.is_uppercase() && prev_lower && !cur.is_empty() {
            words.push(std::mem::take(&mut cur));
        }
        prev_lower = c.is_lowercase() || c.is_numeric();
        cur.push(c);
    }
    if !cur.is_empty() {
        words.push(cur);
    }
    if words.is_empty() {
        return None;
    }
    let lower = |w: &str| w.to_lowercase();
    let cap = |w: &str| {
        let mut cs = w.chars();
        match cs.next() {
            Some(first) => first.to_uppercase().collect::<String>() + &cs.as_str().to_lowercase(),
            None => String::new(),
        }
    };
    Some(match style {
        "camelCase" => words
            .iter()
            .enumerate()
            .map(|(i, w)| if i == 0 { lower(w) } else { cap(w) })
            .collect(),
        "PascalCase" => words.iter().map(|w| cap(w)).collect(),
        "snake_case" => words.iter().map(|w| lower(w)).collect::<Vec<_>>().join("_"),
        "UPPER_SNAKE_CASE" => words
            .iter()
            .map(|w| w.to_uppercase())
            .collect::<Vec<_>>()
            .join("_"),
        "kebab-case" => words.iter().map(|w| lower(w)).collect::<Vec<_>>().join("-"),
        _ => return None,
    })
}

/// One source edit of a [`Fix`]: replace `span` in `unit` with
/// `replacement` (empty = delete).
#[derive(Clone, Debug)]
pub struct Edit {
    pub unit: usize,
    pub span: Span,
    pub replacement: String,
}

/// An automatic remedy for a finding. `deletes` marks fixes that
/// remove model text — hosts must gate those behind explicit opt-in.
#[derive(Clone, Debug)]
pub struct Fix {
    pub label: String,
    pub deletes: bool,
    pub edits: Vec<Edit>,
}

/// One lint finding. `unit`/`span` are absent only for configuration
/// findings (rule `lint-config`), which have no model location.
/// `element` is the finding's edit-target spelling (qualified name,
/// or `@<id>` when unnameable); `suggest` is a naming finding's
/// style-converted replacement name. `fix` is the preferred remedy —
/// what `--fix` applies; `alternatives` are equally-valid remedies a
/// host's quick-fix menu offers alongside it (a dimensionally
/// ambiguous unit lists every compatible quantity type) and are never
/// applied automatically.
#[derive(Clone, Debug)]
pub struct Finding {
    pub rule: &'static str,
    pub severity: Severity,
    pub message: String,
    pub unit: Option<usize>,
    pub span: Option<Span>,
    pub element: Option<String>,
    pub suggest: Option<String>,
    pub fix: Option<Fix>,
    pub alternatives: Vec<Fix>,
}

fn finding(rule: &'static str, severity: Severity, message: String) -> Finding {
    Finding {
        rule,
        severity,
        message,
        unit: None,
        span: None,
        element: None,
        suggest: None,
        fix: None,
        alternatives: Vec::new(),
    }
}

/// The engine's edit-target spelling for `e`.
fn edit_target(resolved: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    resolved
        .element_qualified_name(e)
        .or_else(|| Some(format!("@{}", resolved.element_id(e))))
}

/// Run every enabled rule over the resolved model. Deterministic:
/// findings sort by (unit, position, rule id), configuration findings
/// first. `&mut` because rule passes read the model's lazily-built
/// ownership, annotation, and qualified-name tables.
///
/// Model-tier rules only: the textual `indentation` rule needs source
/// text, so use [`lint_with_sources`] where the host has it.
pub fn lint(resolved: &mut ResolvedModel, config: &Config) -> Vec<Finding> {
    lint_with_sources(resolved, config, &[])
}

/// [`lint`] plus the source text the textual tier reads: `(model unit
/// index, text)` for every user unit the host holds — exactly the pairs
/// spans in findings are resolved against. Passing nothing while a
/// textual rule is enabled yields a `lint-config` finding: a rule that
/// silently checks nothing reads as a broken rule.
pub fn lint_with_sources(
    resolved: &mut ResolvedModel,
    config: &Config,
    sources: &[(usize, &str)],
) -> Vec<Finding> {
    let units: Vec<(usize, &str, &str)> = sources.iter().map(|&(i, t)| (i, "", t)).collect();
    lint_units(resolved, config, &units)
}

/// [`lint_with_sources`] plus unit *names*: `(model unit index, unit
/// name, text)`. The generated-provenance rules audit the sidecar
/// placement contract, which is spelled in unit names — hosts that
/// cannot provide names get every other rule and a `lint-config` note
/// when a generated rule is enabled but nameless.
pub fn lint_units(
    resolved: &mut ResolvedModel,
    config: &Config,
    units: &[(usize, &str, &str)],
) -> Vec<Finding> {
    let sources: Vec<(usize, &str)> = units.iter().map(|&(i, _, t)| (i, t)).collect();
    let sources = sources.as_slice();
    let mut out = Vec::new();
    for c in &config.complaints {
        out.push(finding("lint-config", Severity::Warn, c.clone()));
    }
    if config.cfg("naming-convention").enabled() {
        naming_convention(resolved, config, &mut out);
    }
    if config.cfg("undocumented-element").enabled() {
        undocumented_element(resolved, config, &mut out);
    }
    if config.cfg("untyped-usage").enabled() {
        untyped_usage(resolved, config, &mut out);
    }
    if config.cfg("unused-parameter").enabled() {
        unused_parameter(resolved, config, &mut out);
    }
    if config.cfg("unused-definition").enabled() {
        unused_definition(resolved, config, &mut out);
    }
    if config.cfg("unit-spelling").enabled() {
        unit_spelling(resolved, config, &mut out);
    }
    if config.cfg("dimensional-consistency").enabled() {
        dimensional_consistency(resolved, config, &mut out);
    }
    if config.cfg("qualified-names").enabled() {
        if sources.is_empty() {
            out.push(finding(
                "lint-config",
                Severity::Warn,
                "rule `qualified-names` reads source text, which this host did not \
                 provide — no references were checked"
                    .to_string(),
            ));
        } else {
            qualified_names(resolved, config, sources, &mut out);
        }
    }
    if config.cfg("multiline-conditions").enabled() {
        multiline_conditions(resolved, config, &mut out);
    }
    if config.cfg("indentation").enabled() {
        if sources.is_empty() {
            out.push(finding(
                "lint-config",
                Severity::Warn,
                "rule `indentation` reads source text, which this host did not provide — \
                 no lines were checked"
                    .to_string(),
            ));
        } else {
            indentation(config, sources, &mut out);
        }
    }
    let generated_rules = [
        "generated-provenance-invalid",
        "generated-provenance-baseline-outdated",
        "generated-element-modified",
    ];
    if generated_rules.iter().any(|id| config.cfg(id).enabled()) {
        if units.iter().any(|(_, name, _)| !name.is_empty()) {
            generated_guard(resolved, config, units, &mut out, None, false);
        } else if generated_rules.iter().any(|id| {
            let default = RULES.iter().find(|r| r.id == *id).map(|r| r.default);
            default.is_some_and(|d| config.cfg(id).base != d)
        }) {
            // Only an explicitly configured rule complains — the rules
            // are on by default, and a nameless host (plain
            // lint_with_sources) skipping defaults silently beats a
            // warning on every model without provenance.
            out.push(finding(
                "lint-config",
                Severity::Warn,
                "the generated-provenance rules read unit names (the sidecar contract is \
                 spelled in them), which this host did not provide — no generated \
                 members were checked"
                    .to_string(),
            ));
        }
    }
    out.sort_by(|a, b| {
        (a.unit, a.span.map(|s| s.start), a.rule, &a.message).cmp(&(
            b.unit,
            b.span.map(|s| s.start),
            b.rule,
            &b.message,
        ))
    });
    out
}

/// `naming-convention`: declared names against the effective pattern —
/// a scope's own style/regex, else the family default (metaclasses
/// ending `Definition` form one family; usages and KerML features the
/// other). Only written names are checked (synthesized elements have
/// no declaration site). Preset-style findings carry a `suggest`.
fn naming_convention(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    let cfg = config.cfg("naming-convention");
    let elems: Vec<ElementRef> = resolved.user_elements().collect();
    for e in elems {
        let ty = resolved.element_type(e);
        let (family, family_pat) = if ty.ends_with("Definition") {
            ("definition", &config.naming_definitions)
        } else if ty.ends_with("Usage") || ty == "Feature" {
            ("usage", &config.naming_usages)
        } else {
            continue;
        };
        let severity = cfg.severity(ty);
        if severity == Severity::Off {
            continue;
        }
        let Some((unit, span)) = resolved.declaration_site(e) else {
            continue;
        };
        let Some(name) = resolved.element_name(e).map(str::to_string) else {
            continue;
        };
        let pat = cfg
            .scopes
            .get(ty)
            .and_then(|s| s.pattern.as_ref())
            .unwrap_or(family_pat);
        if pat.regex.is_match(&name) {
            continue;
        }
        let suggest = pat
            .style
            .and_then(|style| convert_to_style(&name, style))
            .filter(|c| c != &name && pat.regex.is_match(c));
        let mut f = finding(
            "naming-convention",
            severity,
            format!("{family} name `{name}` should be {}", pat.describe),
        );
        f.unit = Some(unit);
        f.span = Some(span);
        f.element = edit_target(resolved, e);
        f.suggest = suggest;
        out.push(f);
    }
}

/// `undocumented-element`: definitions in scope without a
/// documentation body — their own `doc` member or a comment written
/// `about` them. Coverage defaults to top-level definitions; `depth`
/// (rule-level or per-scope) extends into nested types, and scope
/// severities tune each stereotype.
fn undocumented_element(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    let cfg = config.cfg("undocumented-element");
    let documented: BTreeSet<ElementRef> = resolved
        .annotation_notes()
        .into_iter()
        .map(|(_, target, _, _)| target)
        .collect();
    let defs: Vec<ElementRef> = resolved
        .user_elements()
        .filter(|e| resolved.element_type(*e).ends_with("Definition"))
        .collect();
    for def in defs {
        let ty = resolved.element_type(def);
        let severity = cfg.severity(ty);
        if severity == Severity::Off {
            continue;
        }
        let Some((unit, span)) = resolved.declaration_site(def) else {
            continue;
        };
        // Nesting depth: 1 = owned by packages/namespaces only, +1 for
        // every enclosing definition or usage.
        let mut depth = 1u32;
        let mut cur = def;
        while let Some(owner) = resolved.owner(cur) {
            let oty = resolved.element_type(owner);
            if oty.ends_with("Definition") || oty.ends_with("Usage") || oty == "Feature" {
                depth += 1;
            }
            cur = owner;
        }
        let max_depth = cfg
            .scopes
            .get(ty)
            .and_then(|s| s.depth)
            .unwrap_or(config.undocumented_depth);
        if depth > max_depth || documented.contains(&def) {
            continue;
        }
        let name = resolved
            .element_name(def)
            .unwrap_or("<anonymous>")
            .to_string();
        let mut f = finding(
            "undocumented-element",
            severity,
            format!("`{name}` has no documentation body (`doc /* … */`)"),
        );
        f.unit = Some(unit);
        f.span = Some(span);
        f.element = edit_target(resolved, def);
        out.push(f);
    }
}

/// `untyped-usage`: a named usage whose declaration carries no typing,
/// subsetting, or redefinition clause — nothing states what it is.
/// Subsetting and redefinition count as typed (the type arrives
/// through the specialization). Enumeration literals and transitions
/// are off by default; scopes tune every stereotype.
fn untyped_usage(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    let cfg = config.cfg("untyped-usage");
    let elems: Vec<ElementRef> = resolved.user_elements().collect();
    for e in elems {
        let ty = resolved.element_type(e);
        if !ty.ends_with("Usage") {
            continue;
        }
        let severity = cfg.severity(ty);
        if severity == Severity::Off {
            continue;
        }
        let Some((unit, span)) = resolved.declaration_site(e) else {
            continue;
        };
        let Some(name) = resolved.element_name(e).map(str::to_string) else {
            continue;
        };
        if !resolved.specialization_spans(e).is_empty() {
            continue;
        }
        let mut f = finding(
            "untyped-usage",
            severity,
            format!("usage `{name}` declares no typing, subsetting, or redefinition"),
        );
        f.unit = Some(unit);
        f.span = Some(span);
        f.element = edit_target(resolved, e);
        // An attribute whose value determines a type gets the declaring
        // fixes (the `dimensional-consistency` untyped inference), the
        // preferred candidate first and the rest as alternatives.
        if ty == "AttributeUsage" {
            let spellings = inferred_type_spellings(resolved, e);
            if let Some(first) = spellings.first() {
                let declare = |s: &String| Fix {
                    label: format!("declare the type `{s}`"),
                    deletes: false,
                    edits: vec![Edit {
                        unit,
                        span: Span {
                            start: span.end,
                            end: span.end,
                        },
                        replacement: format!(" : {s}"),
                    }],
                };
                f.suggest = Some(first.clone());
                f.fix = Some(declare(first));
                f.alternatives = spellings[1..].iter().map(declare).collect();
            }
        }
        out.push(f);
    }
}

/// `unused-parameter`: an `in`/`inout` parameter of a callable user
/// definition with no reference inside the definition's own body,
/// per-context configurable (calc / constraint / action defs). The
/// deletion fix is offered only when nothing anywhere references the
/// parameter — a call site's named argument would be stranded by the
/// deletion, so those findings carry no fix.
fn unused_parameter(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    let cfg = config.cfg("unused-parameter");
    for scope in UNUSED_PARAM_SCOPES {
        let severity = cfg.severity(scope.key);
        if severity == Severity::Off {
            continue;
        }
        for def in resolved.elements_of_metaclass(scope.key) {
            if resolved.is_library_element(def) {
                continue;
            }
            let ret = resolved.calc_return_param(def);
            let extent = resolved.member_extent(def);
            let def_name = resolved
                .element_name(def)
                .unwrap_or("<anonymous>")
                .to_string();
            for p in resolved.owned_features(def) {
                if Some(p) == ret
                    || !matches!(resolved.declared_direction(p), Some("in") | Some("inout"))
                {
                    continue;
                }
                let sites = resolved.references_to(p);
                let used_in_body = sites.iter().any(|s| {
                    extent.is_some_and(|(u, sp)| {
                        s.unit == u && sp.start <= s.name_span.start && s.name_span.end <= sp.end
                    })
                });
                if used_in_body {
                    continue;
                }
                let Some((unit, span)) = resolved.declaration_site(p) else {
                    continue;
                };
                let name = resolved.element_name(p).unwrap_or("_").to_string();
                let (message, fix) = if sites.is_empty() {
                    let fix = resolved.member_extent(p).map(|(u, sp)| Fix {
                        label: format!("delete unused parameter `{name}`"),
                        deletes: true,
                        edits: vec![Edit {
                            unit: u,
                            span: sp,
                            replacement: String::new(),
                        }],
                    });
                    (
                        format!("input parameter `{name}` of `{def_name}` is never used"),
                        fix,
                    )
                } else {
                    (
                        format!(
                            "input parameter `{name}` of `{def_name}` is never used in its \
                             body (referenced only outside it — no fix offered)"
                        ),
                        None,
                    )
                };
                let mut f = finding("unused-parameter", severity, message);
                f.unit = Some(unit);
                f.span = Some(span);
                f.element = edit_target(resolved, p);
                f.fix = fix;
                out.push(f);
            }
        }
    }
}

/// `unused-definition`: a user definition nothing in the user model
/// references — dead code, under a closed-world caveat: libraries are
/// exempt and consumers outside these units are invisible, which is
/// why the rule defaults off. Scopes tune each stereotype.
/// How a quantity bracket spells its unit.
#[derive(Clone, Copy, PartialEq)]
enum UnitForm {
    /// One quoted power-product name: `'m⋅s⁻¹'`.
    QuotedProduct,
    /// Unit arithmetic: `m/s`, `m**3/s**2`.
    Expression,
    /// A single plain name (`m`, `km`, `N`) — fine under every style.
    Plain,
}

/// A unit's factor list: `(name, exponent)` pairs of a power-product.
type UnitFactors = Vec<(String, i32)>;

/// A unit expression's reconstructed spelling, form, and — when every
/// factor is a simple name with an integer exponent — its factor list
/// (the material style fixes re-spell from). `None` for shapes this
/// rule does not reason about (conditionals, chains, non-integer
/// exponents).
fn unit_shape(e: &sysmlv2_syntax::ast::Expr) -> Option<(String, UnitForm, Option<UnitFactors>)> {
    use sysmlv2_syntax::ast::{BinaryOp, ExprKind, Literal};
    fn int_of(e: &sysmlv2_syntax::ast::Expr) -> Option<i32> {
        match &e.kind {
            ExprKind::Literal(Literal::Integer(raw)) => raw.parse().ok(),
            ExprKind::Unary {
                op: sysmlv2_syntax::ast::UnaryOp::Minus,
                operand,
            } => int_of(operand).map(|k| -k),
            _ => None,
        }
    }
    match &e.kind {
        ExprKind::Ref(qn) => {
            let name = qn.segments.last()?.value.clone();
            if qn.segments.len() > 1 {
                // Qualified references keep their spelling but offer no
                // factor list (a style fix would drop the qualifier).
                let full: Vec<&str> = qn.segments.iter().map(|s| s.value.as_str()).collect();
                return Some((full.join("::"), UnitForm::Plain, None));
            }
            match sysmlv2_model::eval::parse_unit_spelling(&name) {
                Some(factors) => {
                    Some((format!("'{name}'"), UnitForm::QuotedProduct, Some(factors)))
                }
                None => Some((name.clone(), UnitForm::Plain, Some(vec![(name, 1)]))),
            }
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let (ls, _, lf) = unit_shape(lhs)?;
            match op {
                BinaryOp::Mul | BinaryOp::Div => {
                    let (rs, _, rf) = unit_shape(rhs)?;
                    let sign = if matches!(op, BinaryOp::Mul) { 1 } else { -1 };
                    let glyph = if sign == 1 { "*" } else { "/" };
                    let factors = match (lf, rf) {
                        (Some(mut l), Some(r)) => {
                            l.extend(r.into_iter().map(|(n, k)| (n, k * sign)));
                            Some(l)
                        }
                        _ => None,
                    };
                    Some((format!("{ls}{glyph}{rs}"), UnitForm::Expression, factors))
                }
                BinaryOp::Pow | BinaryOp::Caret => {
                    let k = int_of(rhs)?;
                    let factors =
                        lf.map(|l| l.into_iter().map(|(n, e)| (n, e * k)).collect::<Vec<_>>());
                    Some((format!("{ls}**{k}"), UnitForm::Expression, factors))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Compose factors as a quoted power-product name (`'m⋅s⁻¹'`); `None`
/// when a factor name would not read back (quotes inside, separators).
fn spell_quoted_product(factors: &[(String, i32)]) -> Option<String> {
    fn sup(k: i32) -> String {
        const DIGITS: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
        let mut out = String::new();
        if k < 0 {
            out.push('⁻');
        }
        for d in k.unsigned_abs().to_string().bytes() {
            out.push(DIGITS[(d - b'0') as usize]);
        }
        out
    }
    let mut parts = Vec::new();
    for (name, k) in factors {
        if *k == 0 {
            continue;
        }
        if name.contains(['\'', '⋅', '·', '*', '/', '(', ')'])
            || name.chars().any(|c| c.is_whitespace())
        {
            return None;
        }
        let exp = if *k == 1 { String::new() } else { sup(*k) };
        parts.push(format!("{name}{exp}"));
    }
    (!parts.is_empty()).then(|| format!("'{}'", parts.join("⋅")))
}

/// Compose factors as a unit arithmetic expression (`m/s`,
/// `m**3/s**2`); `None` when a factor name is not a plain identifier
/// or nothing remains in the numerator (`1/s` is not a unit
/// expression).
fn spell_expression(factors: &[(String, i32)]) -> Option<String> {
    let ident = |n: &str| {
        let mut cs = n.chars();
        cs.next().is_some_and(|c| c.is_alphabetic() || c == '_')
            && n.chars().all(|c| c.is_alphanumeric() || c == '_')
    };
    let mut num = Vec::new();
    let mut den = Vec::new();
    for (name, k) in factors {
        if *k == 0 {
            continue;
        }
        if !ident(name) {
            return None;
        }
        let mag = k.unsigned_abs();
        let part = if mag == 1 {
            name.clone()
        } else {
            format!("{name}**{mag}")
        };
        if *k > 0 {
            num.push(part)
        } else {
            den.push(part)
        }
    }
    if num.is_empty() {
        return None;
    }
    let mut out = num.join("*");
    for d in den {
        out.push('/');
        out.push_str(&d);
    }
    Some(out)
}

/// `unit-spelling`: every quantity bracket in the user units, grouped
/// by the canonical unit it denotes. Two spellings for one unit flag
/// the minority sites; with a configured `style`, any multi-factor
/// spelling off the preferred form flags too, with a re-spelling fix
/// where one is derivable. Unresolvable unit expressions are the
/// checker's business, not this rule's.
fn unit_spelling(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    use sysmlv2_syntax::ast::{Expr, ExprKind};
    use sysmlv2_syntax::visit::{Visit, walk_expr};
    let cfg = config.cfg("unit-spelling");

    struct Brackets<'a> {
        args: Vec<&'a Expr>,
    }
    impl<'a> Visit<'a> for Brackets<'a> {
        fn visit_expr(&mut self, e: &'a Expr) {
            if let ExprKind::Bracket { arg, .. } = &e.kind {
                self.args.push(arg);
            }
            walk_expr(self, e);
        }
    }

    // Expression sources: user feature values, then user constraint
    // bodies (their brackets live in the same unit as the owner).
    let users: BTreeSet<ElementRef> = resolved.user_elements().collect();
    let mut sources: Vec<(ElementRef, usize, sysmlv2_model::json::ScopeRef, Expr)> = Vec::new();
    for &e in &users {
        let Some((scope, expr)) = resolved.value_expr(e) else {
            continue;
        };
        let Some((unit, _)) = resolved.declaration_site(e) else {
            continue;
        };
        sources.push((e, unit, scope, expr));
    }
    for c in resolved.constraints() {
        if users.contains(&c.element) {
            sources.push((c.element, c.unit, c.scope, c.expr));
        }
    }

    struct Site {
        owner: ElementRef,
        unit: usize,
        span: Span,
        key: String,
        spelling: String,
        form: UnitForm,
        factors: Option<Vec<(String, i32)>>,
    }
    let mut sites: Vec<Site> = Vec::new();
    for (owner, unit, scope, expr) in sources {
        let mut v = Brackets { args: Vec::new() };
        v.visit_expr(&expr);
        for arg in v.args {
            let Ok(u) = resolved.unit_of_in(scope, arg) else {
                continue;
            };
            if u.dims_key().is_empty() {
                continue; // dimensionless (cancelled) — nothing to spell
            }
            let Some((spelling, form, factors)) = unit_shape(arg) else {
                continue;
            };
            sites.push(Site {
                owner,
                unit,
                span: arg.span,
                key: u.key(),
                spelling,
                form,
                factors,
            });
        }
    }

    // Consistency: group by denoted unit; the majority spelling (ties:
    // first encountered) is the reference, every other spelling flags.
    let mut groups: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (i, s) in sites.iter().enumerate() {
        groups.entry(&s.key).or_default().push(i);
    }
    for idxs in groups.values() {
        let mut counts: Vec<(&str, usize)> = Vec::new();
        for &i in idxs {
            match counts.iter_mut().find(|(sp, _)| *sp == sites[i].spelling) {
                Some((_, n)) => *n += 1,
                None => counts.push((&sites[i].spelling, 1)),
            }
        }
        if counts.len() < 2 {
            continue;
        }
        let (majority, n) = counts
            .iter()
            .max_by_key(|(_, n)| *n)
            .map(|(sp, n)| (sp.to_string(), *n))
            .expect("non-empty");
        let total = idxs.len();
        for &i in idxs {
            let s = &sites[i];
            if s.spelling == majority {
                continue;
            }
            let severity = cfg.severity(resolved.element_type(s.owner));
            if severity == Severity::Off {
                continue;
            }
            let mut f = finding(
                "unit-spelling",
                severity,
                format!(
                    "unit spelled `{}` here but `{majority}` at {n} of {total} sites — \
                     one unit, one spelling",
                    s.spelling
                ),
            );
            f.unit = Some(s.unit);
            f.span = Some(s.span);
            f.element = edit_target(resolved, s.owner);
            f.fix = Some(Fix {
                label: format!("re-spell as `{majority}`"),
                deletes: false,
                edits: vec![Edit {
                    unit: s.unit,
                    span: s.span,
                    replacement: majority.clone(),
                }],
            });
            out.push(f);
        }
    }

    // Style: multi-factor spellings must take the preferred form.
    let Some(style) = config.unit_style else {
        return;
    };
    for s in &sites {
        let multi_factor = match &s.factors {
            Some(f) => f.len() > 1 || f.iter().any(|(_, k)| *k != 1),
            // No factor list but a compound form is still style-relevant.
            None => s.form == UnitForm::Expression,
        };
        if !multi_factor || s.form == UnitForm::Plain {
            continue;
        }
        let wanted = match style {
            UnitStyle::QuotedProduct => UnitForm::QuotedProduct,
            UnitStyle::Expression => UnitForm::Expression,
        };
        if s.form == wanted {
            continue;
        }
        let severity = cfg.severity(resolved.element_type(s.owner));
        if severity == Severity::Off {
            continue;
        }
        let respelled = s.factors.as_deref().and_then(|f| match style {
            UnitStyle::QuotedProduct => spell_quoted_product(f),
            UnitStyle::Expression => spell_expression(f),
        });
        let (want_name, want_example) = match style {
            UnitStyle::QuotedProduct => ("a quoted product name", "'m⋅s⁻¹'"),
            UnitStyle::Expression => ("a unit expression", "m/s"),
        };
        let mut f = finding(
            "unit-spelling",
            severity,
            format!(
                "unit spelled `{}` — this project spells compound units as {want_name} \
                 (like `{want_example}`)",
                s.spelling
            ),
        );
        f.unit = Some(s.unit);
        f.span = Some(s.span);
        f.element = edit_target(resolved, s.owner);
        f.fix = respelled.map(|r| Fix {
            label: format!("re-spell as `{r}`"),
            deletes: false,
            edits: vec![Edit {
                unit: s.unit,
                span: s.span,
                replacement: r,
            }],
        });
        out.push(f);
    }
}

/// The declaring fix for an untyped attribute whose value determines a
/// type: every compatible type, in preference order, spelled as the
/// shortest reference that resolves from the declaration's scope. A
/// unit written as a single named reference ranks the types its unit
/// definition denotes first (`[J]` names the energy unit, so the
/// energy type outranks torque, which merely shares the dimension),
/// then every library type of the same dimension; a plain literal has
/// exactly its scalar-value type. Empty whenever any link is
/// indeterminate — no value, no library, an opaque unit, no
/// resolvable spelling.
fn inferred_type_spellings(resolved: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    use sysmlv2_model::eval::Value;
    let Some((scope, expr)) = resolved.value_expr(e) else {
        return Vec::new();
    };
    let Ok(value) = resolved.evaluate(e) else {
        return Vec::new();
    };
    let mut targets: Vec<ElementRef> = Vec::new();
    match &value {
        Value::Quantity(_, u) => {
            if let Some(unit_elem) = bracket_unit_ref(resolved, scope, &expr) {
                for def in resolved.typings(unit_elem) {
                    for t in resolved.quantity_types_for_unit_def(def) {
                        if !targets.contains(&t) {
                            targets.push(t);
                        }
                    }
                }
            }
            if let Some(dims) = resolved.unit_quantity_dims(u) {
                for t in resolved.quantity_type_candidates(&dims) {
                    if !targets.contains(&t) {
                        targets.push(t);
                    }
                }
            }
        }
        v => targets.extend(resolved.scalar_literal_type(v)),
    }
    let mut spellings: Vec<String> = Vec::new();
    for t in targets {
        if let Some(s) = resolved.type_spelling_at(scope, t) {
            if !spellings.contains(&s) {
                spellings.push(s);
            }
        }
    }
    spellings
}

/// The written unit reference of the value's first quantity bracket —
/// a bracket whose unit is a single name (`[J]`, `[SI::J]`), resolved.
/// `None` for computed unit expressions (`[m/s**2]`): those denote no
/// single named unit and rank by dimension alone.
fn bracket_unit_ref(
    resolved: &mut ResolvedModel,
    scope: sysmlv2_model::json::ScopeRef,
    expr: &sysmlv2_syntax::ast::Expr,
) -> Option<ElementRef> {
    use sysmlv2_syntax::ast::{Expr, ExprKind};
    use sysmlv2_syntax::visit::{Visit, walk_expr};
    struct FirstBracket<'a> {
        arg: Option<&'a Expr>,
    }
    impl<'a> Visit<'a> for FirstBracket<'a> {
        fn visit_expr(&mut self, e: &'a Expr) {
            if self.arg.is_none() {
                if let ExprKind::Bracket { arg, .. } = &e.kind {
                    self.arg = Some(arg);
                }
                walk_expr(self, e);
            }
        }
    }
    let mut v = FirstBracket { arg: None };
    v.visit_expr(expr);
    match &v.arg?.kind {
        ExprKind::Ref(qn) => resolved.resolve_in(scope, qn),
        _ => None,
    }
}

/// Render the inference message's alternates clause: nothing for an
/// unambiguous inference, else the next candidates by name (two at
/// most) with a count for the rest.
fn alternates_clause(spellings: &[String]) -> String {
    let alts = &spellings[1..];
    if alts.is_empty() {
        return String::new();
    }
    let named: Vec<String> = alts.iter().take(2).map(|s| format!("`{s}`")).collect();
    let rest = alts.len().saturating_sub(named.len());
    if rest == 0 {
        format!(" (also compatible: {})", named.join(", "))
    } else {
        format!(" (also compatible: {}, +{rest} more)", named.join(", "))
    }
}

/// `dimensional-consistency`: quantity typing against value units. The
/// `mismatch` aspect (the rule's base severity) flags an attribute
/// whose declared quantity type and value unit disagree dimensionally,
/// with a re-typing fix to the unit's quantity type; the `untyped`
/// aspect (warn unless scoped) flags an untyped attribute whose value
/// determines a type, with the declaring fix. Both sides must be
/// determinate — no standard library, an opaque user unit, or an
/// unevaluable value stays silent, never a guess.
fn dimensional_consistency(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    use sysmlv2_model::eval::Value;
    let cfg = config.cfg("dimensional-consistency");
    let mismatch_sev = cfg.severity("mismatch");
    // The untyped aspect's inventory default is warn — seeded, so it
    // holds while the rule is on and dies under `"off"`.
    let untyped_sev = cfg.severity("untyped");
    if mismatch_sev == Severity::Off && untyped_sev == Severity::Off {
        return;
    }
    let elems: Vec<ElementRef> = resolved.user_elements().collect();
    for e in elems {
        if resolved.element_type(e) != "AttributeUsage" || resolved.value_expr(e).is_none() {
            continue;
        }
        let Some((unit_idx, name_span)) = resolved.declaration_site(e) else {
            continue;
        };
        let Some(name) = resolved.element_name(e).map(str::to_string) else {
            continue;
        };
        let typings = resolved.typings(e);
        if typings.is_empty() {
            // Untyped: only a declaration with no specialization clause
            // at all (subsetting/redefinition deliver a type indirectly).
            if untyped_sev == Severity::Off || !resolved.specialization_spans(e).is_empty() {
                continue;
            }
            let spellings = inferred_type_spellings(resolved, e);
            let Some(first) = spellings.first().cloned() else {
                continue;
            };
            let declare = |s: &String| Fix {
                label: format!("declare the type `{s}`"),
                deletes: false,
                edits: vec![Edit {
                    unit: unit_idx,
                    span: Span {
                        start: name_span.end,
                        end: name_span.end,
                    },
                    replacement: format!(" : {s}"),
                }],
            };
            let mut f = finding(
                "dimensional-consistency",
                untyped_sev,
                format!(
                    "attribute `{name}` declares no type — its value infers `{first}`{}",
                    alternates_clause(&spellings)
                ),
            );
            f.unit = Some(unit_idx);
            // The finding covers the whole `name = value` declaration —
            // the fix's insertion point stays right after the name.
            let value_end = resolved
                .value_expr(e)
                .map(|(_, x)| x.span.end)
                .filter(|&end| end > name_span.end)
                .unwrap_or(name_span.end);
            f.span = Some(Span {
                start: name_span.start,
                end: value_end,
            });
            f.element = edit_target(resolved, e);
            f.suggest = Some(first.clone());
            f.fix = Some(declare(&first));
            f.alternatives = spellings[1..].iter().map(declare).collect();
            out.push(f);
            continue;
        }
        if mismatch_sev == Severity::Off {
            continue;
        }
        let Ok(Value::Quantity(_, u)) = resolved.evaluate(e) else {
            continue;
        };
        let Some(actual) = resolved.unit_quantity_dims(&u) else {
            continue;
        };
        let Some((decl, expected)) = typings
            .iter()
            .find_map(|&t| resolved.quantity_dims_of_type(t).map(|d| (t, d)))
        else {
            continue;
        };
        if expected == actual {
            continue;
        }
        let ty_name = resolved
            .element_name(decl)
            .unwrap_or("<anonymous>")
            .to_string();
        // Anchor on the written type when the declaration has exactly
        // one typing clause — that is also the re-typing fix's edit
        // target; multiple clauses keep the name anchor and no fix.
        let spans = resolved.typing_spans(e);
        let (anchor_unit, anchor_span, fixable) = match spans[..] {
            [(u, s)] => (u, s, true),
            _ => (unit_idx, name_span, false),
        };
        let spellings = if fixable {
            inferred_type_spellings(resolved, e)
        } else {
            Vec::new()
        };
        let retype = |s: &String| Fix {
            label: format!("re-type as `{s}`"),
            deletes: false,
            edits: vec![Edit {
                unit: anchor_unit,
                span: anchor_span,
                replacement: s.clone(),
            }],
        };
        let mut f = finding(
            "dimensional-consistency",
            mismatch_sev,
            format!(
                "attribute `{name}` is typed `{ty_name}` (dimension {}) but its value's \
                 unit `{}` measures {}",
                expected.render(resolved),
                u.display(),
                actual.render(resolved),
            ),
        );
        f.unit = Some(anchor_unit);
        f.span = Some(anchor_span);
        f.element = edit_target(resolved, e);
        f.suggest = spellings.first().cloned();
        f.fix = spellings.first().map(&retype);
        f.alternatives = spellings.iter().skip(1).map(&retype).collect();
        out.push(f);
    }
}

/// Every quantity-bracket unit-expression span in the user units —
/// the regions `qualified-names` leaves alone (`[m/s**2]` is the
/// `unit-spelling` rule's business, and qualifying unit symbols reads
/// terribly).
fn bracket_arg_spans(resolved: &mut ResolvedModel) -> Vec<(usize, Span)> {
    use sysmlv2_syntax::ast::{Expr, ExprKind};
    use sysmlv2_syntax::visit::{Visit, walk_expr};
    struct Brackets {
        spans: Vec<Span>,
    }
    impl<'a> Visit<'a> for Brackets {
        fn visit_expr(&mut self, e: &'a Expr) {
            if let ExprKind::Bracket { arg, .. } = &e.kind {
                self.spans.push(arg.span);
            }
            walk_expr(self, e);
        }
    }
    let users: BTreeSet<ElementRef> = resolved.user_elements().collect();
    let mut sources: Vec<(usize, sysmlv2_syntax::ast::Expr)> = Vec::new();
    for &e in &users {
        let Some((_, expr)) = resolved.value_expr(e) else {
            continue;
        };
        let Some((unit, _)) = resolved.declaration_site(e) else {
            continue;
        };
        sources.push((unit, expr));
    }
    for c in resolved.constraints() {
        if users.contains(&c.element) {
            sources.push((c.unit, c.expr));
        }
    }
    let mut out = Vec::new();
    for (unit, expr) in sources {
        let mut v = Brackets { spans: Vec::new() };
        v.visit_expr(&expr);
        out.extend(v.spans.into_iter().map(|s| (unit, s)));
    }
    out
}

/// Split a written reference spelling into its raw segment names:
/// `::`-separated, quoted segments unwrapped with the source escapes
/// undone. `None` for text this simple reader cannot take apart.
fn split_spelling(text: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    for seg in text.split("::") {
        let seg = seg.trim();
        if seg.is_empty() {
            return None;
        }
        if let Some(inner) = seg.strip_prefix('\'').and_then(|s| s.strip_suffix('\'')) {
            let mut name = String::new();
            let mut chars = inner.chars();
            while let Some(c) = chars.next() {
                if c != '\\' {
                    name.push(c);
                    continue;
                }
                match chars.next() {
                    Some('b') => name.push('\u{0008}'),
                    Some('t') => name.push('\t'),
                    Some('n') => name.push('\n'),
                    Some('f') => name.push('\u{000C}'),
                    Some('r') => name.push('\r'),
                    Some(c @ ('"' | '\'' | '\\')) => name.push(c),
                    _ => return None,
                }
            }
            out.push(name);
        } else {
            out.push(seg.to_string());
        }
    }
    Some(out)
}

/// Where an added import lands in `unit`: right after the unit's last
/// existing import statement (its target reference's trailing `;`),
/// reusing that line's leading indentation. `None` when the unit has
/// no import to anchor on (the finding then carries no fix —
/// inventing a position inside an arbitrary namespace body is how a
/// fix breaks a model).
fn import_anchor(resolved: &mut ResolvedModel, unit: usize, text: &str) -> Option<(u32, String)> {
    let last = resolved
        .reference_sites()
        .iter()
        .filter(|s| s.unit == unit && s.kind.starts_with("imported"))
        .map(|s| s.span)
        .max_by_key(|s| s.end)?;
    // The statement ends at the `;` after the imported name (a `::*`
    // or filter suffix may intervene).
    let tail = text.get(last.end as usize..)?;
    let semi = last.end as usize + tail.find(';')?;
    let line_start = text[..last.start as usize]
        .rfind('\n')
        .map(|i| i + 1)
        .unwrap_or(0);
    let indent: String = text[line_start..]
        .chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .collect();
    Some((semi as u32 + 1, indent))
}

/// `qualified-names`: reference-spelling discipline over the plain
/// reference sites of the user units (chain steps, import targets, and
/// quantity-bracket units are exempt). Without a `style`, one element
/// spelled two ways flags the minority sites with a re-spelling fix to
/// the majority form; with a `style`, every site off the policy flags:
/// `qualified` wants the full owner chain, `minimal` the shortest
/// spelling that resolves at the site, `imported` the simple name —
/// re-spelling directly when the target is visible, adding an import
/// (anchored after the unit's last existing one) when it is not, and
/// keeping the qualification silently when the simple name is bound to
/// a different element. Every generated respelling is verified by
/// resolution before it becomes an edit.
fn qualified_names(
    resolved: &mut ResolvedModel,
    config: &Config,
    sources: &[(usize, &str)],
    out: &mut Vec<Finding>,
) {
    let severity = config.cfg("qualified-names").base;
    let text_of = |unit: usize| sources.iter().find(|(i, _)| *i == unit).map(|(_, t)| *t);
    let user_units: BTreeSet<usize> = {
        let elems: Vec<ElementRef> = resolved.user_elements().collect();
        elems
            .iter()
            .filter_map(|&e| resolved.declaration_site(e))
            .map(|(u, _)| u)
            .collect()
    };
    let brackets = bracket_arg_spans(resolved);
    struct Site {
        unit: usize,
        span: Span,
        target: ElementRef,
        scope: sysmlv2_model::json::ScopeRef,
        exclude: Option<ElementRef>,
        written: String,
    }
    let sites: Vec<Site> = resolved
        .reference_sites()
        .iter()
        .filter(|s| s.plain && user_units.contains(&s.unit))
        // Import targets are spelled from the import's own vantage
        // point — qualification policy does not apply to them.
        .filter(|s| !s.kind.starts_with("imported"))
        .filter(|s| {
            !brackets
                .iter()
                .any(|(u, b)| *u == s.unit && b.start <= s.span.start && s.span.end <= b.end)
        })
        .filter_map(|s| {
            let text = text_of(s.unit)?;
            let written = text.get(s.span.start as usize..s.span.end as usize)?;
            Some(Site {
                unit: s.unit,
                span: s.span,
                target: s.target,
                scope: s.scope,
                exclude: s.exclude,
                written: written.to_string(),
            })
        })
        .collect();

    let mut push = |resolved: &mut ResolvedModel,
                    site: &Site,
                    message: String,
                    fix: Option<Fix>,
                    suggest: String| {
        let mut f = finding("qualified-names", severity, message);
        f.unit = Some(site.unit);
        f.span = Some(site.span);
        f.element = edit_target(resolved, site.target);
        f.suggest = Some(suggest);
        f.fix = fix;
        out.push(f);
    };

    let Some(style) = config.qualified_style else {
        // Consistency: group sites by target; the majority spelling
        // (ties: first encountered) is the reference form.
        let mut groups: BTreeMap<ElementRef, Vec<usize>> = BTreeMap::new();
        for (i, s) in sites.iter().enumerate() {
            groups.entry(s.target).or_default().push(i);
        }
        for (&target, idxs) in &groups {
            let mut counts: Vec<(&str, usize)> = Vec::new();
            for &i in idxs {
                match counts.iter_mut().find(|(w, _)| *w == sites[i].written) {
                    Some((_, n)) => *n += 1,
                    None => counts.push((&sites[i].written, 1)),
                }
            }
            if counts.len() < 2 {
                continue;
            }
            // Ties break to the first-encountered spelling (max_by_key
            // would keep the last maximum).
            let (majority, n) = counts
                .iter()
                .rev()
                .max_by_key(|(_, n)| *n)
                .map(|(w, n)| (w.to_string(), *n))
                .expect("non-empty");
            let total = idxs.len();
            let segments = split_spelling(&majority);
            for &i in idxs {
                let site = &sites[i];
                if site.written == majority {
                    continue;
                }
                // A site where the majority spelling does not resolve to
                // the target had no choice — a member reference outside
                // its owner's body *must* qualify. That is necessity,
                // not inconsistency: exempt, never flag-without-fix.
                let adoptable = segments.as_ref().is_some_and(|segs| {
                    resolved.segments_resolve_to(site.scope, site.exclude, segs, target)
                });
                if !adoptable {
                    continue;
                }
                let name = resolved
                    .element_name(target)
                    .unwrap_or("<anonymous>")
                    .to_string();
                push(
                    resolved,
                    site,
                    format!(
                        "reference to `{name}` is spelled `{}` here but `{majority}` at \
                         {n} of {total} sites — one element, one spelling",
                        site.written
                    ),
                    Some(Fix {
                        label: format!("re-spell as `{majority}`"),
                        deletes: false,
                        edits: vec![Edit {
                            unit: site.unit,
                            span: site.span,
                            replacement: majority.clone(),
                        }],
                    }),
                    majority.clone(),
                );
            }
        }
        return;
    };

    for site in &sites {
        match style {
            QualifiedStyle::Qualified => {
                let Some(full) = resolved.full_spelling(site.target) else {
                    continue;
                };
                if site.written == full {
                    continue;
                }
                let ok = split_spelling(&full).is_some_and(|segs| {
                    resolved.segments_resolve_to(site.scope, site.exclude, &segs, site.target)
                });
                let fix = ok.then(|| Fix {
                    label: format!("qualify as `{full}`"),
                    deletes: false,
                    edits: vec![Edit {
                        unit: site.unit,
                        span: site.span,
                        replacement: full.clone(),
                    }],
                });
                push(
                    resolved,
                    site,
                    format!(
                        "reference `{}` should be fully qualified as `{full}`",
                        site.written
                    ),
                    fix,
                    full,
                );
            }
            QualifiedStyle::Minimal => {
                let Some(minimal) =
                    resolved.reference_spelling_at(site.scope, site.exclude, site.target)
                else {
                    continue;
                };
                if site.written == minimal || minimal.len() >= site.written.len() {
                    continue;
                }
                push(
                    resolved,
                    site,
                    format!(
                        "reference `{}` qualifies more than resolution needs — `{minimal}` \
                         resolves here",
                        site.written
                    ),
                    Some(Fix {
                        label: format!("re-spell as `{minimal}`"),
                        deletes: false,
                        edits: vec![Edit {
                            unit: site.unit,
                            span: site.span,
                            replacement: minimal.clone(),
                        }],
                    }),
                    minimal,
                );
            }
            QualifiedStyle::Imported => {
                let Some(name) = resolved.element_name(site.target).map(str::to_string) else {
                    continue;
                };
                let simple = sysmlv2_syntax::ast::escape_name(&name);
                if site.written == simple {
                    continue;
                }
                let seg = vec![name.clone()];
                let visible =
                    resolved.segments_resolve_to(site.scope, site.exclude, &seg, site.target);
                if visible {
                    push(
                        resolved,
                        site,
                        format!(
                            "reference `{}` spells a visible name — `{simple}` resolves here",
                            site.written
                        ),
                        Some(Fix {
                            label: format!("re-spell as `{simple}`"),
                            deletes: false,
                            edits: vec![Edit {
                                unit: site.unit,
                                span: site.span,
                                replacement: simple.clone(),
                            }],
                        }),
                        simple,
                    );
                    continue;
                }
                // Bound to something else = a genuine conflict — the
                // qualification is earning its keep; stay silent.
                let taken = resolved
                    .resolve_in_excluding(site.scope, &simple_reference(&name), site.exclude)
                    .is_some();
                if taken {
                    continue;
                }
                let Some(import_qn) = resolved.full_spelling(site.target) else {
                    continue;
                };
                let fix = text_of(site.unit).and_then(|text| {
                    import_anchor(resolved, site.unit, text).map(|(at, indent)| Fix {
                        label: format!("import `{import_qn}` and re-spell as `{simple}`"),
                        deletes: false,
                        edits: vec![
                            Edit {
                                unit: site.unit,
                                span: Span { start: at, end: at },
                                replacement: format!("\n{indent}private import {import_qn};"),
                            },
                            Edit {
                                unit: site.unit,
                                span: site.span,
                                replacement: simple.clone(),
                            },
                        ],
                    })
                });
                push(
                    resolved,
                    site,
                    format!(
                        "reference `{}` could be `{simple}` with `{import_qn}` imported",
                        site.written
                    ),
                    fix,
                    simple,
                );
            }
        }
    }
}

/// A one-segment [`QualifiedName`] for resolution probes.
fn simple_reference(name: &str) -> sysmlv2_syntax::ast::QualifiedName {
    use sysmlv2_syntax::ast::{Name, QualifiedName};
    QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: name.to_string(),
            span: Span::default(),
        }],
        span: Span::default(),
    }
}

/// `multiline-conditions`: a constraint-style result expression whose
/// logical chain has enough operands to deserve one condition per
/// line, written on a single source line. No auto-fix — Format
/// Document produces exactly the wanted shape (the formatter shares
/// this rule's threshold via [`Config::format_chain_min`]).
fn multiline_conditions(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    use sysmlv2_syntax::ast::{BinaryOp, Expr, ExprKind};
    let cfg = config.cfg("multiline-conditions");
    let min = config.chain_min;
    if min == 0 {
        return;
    }
    fn chain(e: &Expr) -> Option<(&'static str, usize)> {
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
            _ => return None,
        };
        fn count(e: &Expr, op: BinaryOp) -> usize {
            match &e.kind {
                ExprKind::Binary { op: o, lhs, rhs } if *o == op => count(lhs, op) + count(rhs, op),
                _ => 1,
            }
        }
        let text = match op {
            BinaryOp::CondAnd => "and",
            BinaryOp::CondOr => "or",
            BinaryOp::Xor => "xor",
            BinaryOp::Implies => "implies",
            BinaryOp::AndAmp => "&",
            BinaryOp::OrBar => "|",
            _ => unreachable!(),
        };
        Some((text, count(e, op)))
    }
    let users: BTreeSet<ElementRef> = resolved.user_elements().collect();
    for c in resolved.constraints() {
        if !users.contains(&c.element) {
            continue;
        }
        let severity = cfg.severity(resolved.element_type(c.element));
        if severity == Severity::Off {
            continue;
        }
        let Some((op, n)) = chain(&c.expr) else {
            continue;
        };
        if n < min as usize {
            continue;
        }
        let span = c.expr.span;
        let Some((first, last)) = resolved.span_lines(c.unit, span) else {
            continue;
        };
        if first != last {
            continue; // already broken across lines
        }
        let mut f = finding(
            "multiline-conditions",
            severity,
            format!(
                "a {n}-condition `{op}` chain on one line — one condition per line reads \
                 better, `{op}` leading each continuation (Format Document does this)"
            ),
        );
        f.unit = Some(c.unit);
        f.span = Some(span);
        f.element = edit_target(resolved, c.element);
        out.push(f);
    }
}

/// `indentation`: leading whitespace against the project's style —
/// tabs, or a multiple of `size` spaces. The one rule of the textual
/// tier: layout is not in the model, so this reads the units' source
/// text directly.
///
/// Skipped, deliberately: blank lines (nothing is indented), lines with
/// no leading whitespace, and the interior lines of any multi-line
/// token — a verbatim `/* … */` documentation body, a `//* … */` note,
/// a multi-line string. Their layout belongs to the author (the
/// formatter reproduces those bodies byte for byte), so a finding there
/// would demand an edit no formatter would make.
///
/// The fix re-indents to the same *level*: existing whitespace is
/// measured in columns (a tab advances to the next `size` boundary) and
/// rounded to the nearest level, with a floor of one — an indented line
/// never dedents to column 0 because its indentation was narrow.
fn indentation(config: &Config, sources: &[(usize, &str)], out: &mut Vec<Finding>) {
    let severity = config.cfg("indentation").base;
    if severity == Severity::Off {
        return;
    }
    let size = config.indent_size.max(1) as usize;
    let wanted = match config.indent_style {
        IndentStyle::Tabs => "tabs".to_string(),
        IndentStyle::Spaces => format!("{size} spaces"),
    };
    for &(unit, src) in sources {
        // Interior lines of multi-line tokens, as (start, end) source
        // ranges in token order. Trivia whitespace spans line breaks by
        // construction — it *is* the indentation under scrutiny — so
        // only content tokens count here.
        let (tokens, _) = sysmlv2_syntax::lexer::tokenize(src);
        let verbatim: Vec<(u32, u32)> = tokens
            .iter()
            .filter(|t| {
                t.kind != sysmlv2_syntax::token::TokenKind::Whitespace && t.text(src).contains('\n')
            })
            .map(|t| (t.span.start, t.span.end))
            .collect();
        let mut offset = 0u32;
        for line in src.split_inclusive('\n') {
            let start = offset;
            offset += line.len() as u32;
            let ws = &line[..line.len() - line.trim_start_matches([' ', '\t']).len()];
            if ws.is_empty() || line[ws.len()..].trim().is_empty() {
                continue; // column 0, or nothing but whitespace
            }
            if verbatim.iter().any(|(s, e)| *s < start && start < *e) {
                continue;
            }
            let tabs = ws.bytes().filter(|b| *b == b'\t').count();
            let spaces = ws.len() - tabs;
            let conforms = match config.indent_style {
                IndentStyle::Tabs => spaces == 0,
                IndentStyle::Spaces => tabs == 0 && ws.len() % size == 0,
            };
            if conforms {
                continue;
            }
            let found = match (tabs, spaces) {
                (0, n) => format!("{n} space{}", plural(n)),
                (n, 0) => format!("{n} tab{}", plural(n)),
                _ => "mixed tabs and spaces".to_string(),
            };
            let message = if config.indent_style == IndentStyle::Spaces && tabs == 0 {
                format!("indented with {found} — not a multiple of this project's {size}")
            } else {
                format!("indented with {found} — this project indents with {wanted}")
            };
            // Column width of what is there, then the nearest level.
            let mut width = 0usize;
            for c in ws.chars() {
                width += if c == '\t' { size - (width % size) } else { 1 };
            }
            let levels = ((width + size / 2) / size).max(1);
            let replacement = match config.indent_style {
                IndentStyle::Tabs => "\t".repeat(levels),
                IndentStyle::Spaces => " ".repeat(levels * size),
            };
            let span = Span::new(start, start + ws.len() as u32);
            let mut f = finding("indentation", severity, message);
            f.unit = Some(unit);
            f.span = Some(span);
            f.fix = Some(Fix {
                label: format!("re-indent this line with {wanted}"),
                deletes: false,
                edits: vec![Edit {
                    unit,
                    span,
                    replacement,
                }],
            });
            out.push(f);
        }
    }
}

fn plural(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

fn unused_definition(resolved: &mut ResolvedModel, config: &Config, out: &mut Vec<Finding>) {
    let cfg = config.cfg("unused-definition");
    let defs: Vec<ElementRef> = resolved
        .user_elements()
        .filter(|e| resolved.element_type(*e).ends_with("Definition"))
        .collect();
    for def in defs {
        let severity = cfg.severity(resolved.element_type(def));
        if severity == Severity::Off {
            continue;
        }
        if !resolved.references_to(def).is_empty() {
            continue;
        }
        let Some((unit, span)) = resolved.declaration_site(def) else {
            continue;
        };
        let name = resolved
            .element_name(def)
            .unwrap_or("<anonymous>")
            .to_string();
        let mut f = finding(
            "unused-definition",
            severity,
            format!(
                "`{name}` is never referenced in these units (closed world: outside \
                 consumers are not visible to lint)"
            ),
        );
        f.unit = Some(unit);
        f.span = Some(span);
        f.element = edit_target(resolved, def);
        out.push(f);
    }
}

// ---------------------------------------------------------------------------
// Generated-element guard: the durable baseline
// and ownership audit over transformer provenance. Three rules share
// one parsed inventory:
//   generated-provenance-invalid            — ownership corruption
//   generated-provenance-baseline-outdated  — valid legacy records
//   generated-element-modified              — drift classification
// ---------------------------------------------------------------------------

/// Bump whenever canonical structure or formatting changes meaning:
/// the fingerprint below folds it in, so every recorded baseline
/// becomes "policy drift" (refreshed by the next sync) instead of
/// falsely reading as a manual edit.
pub const CANONICALIZER_SCHEMA_VERSION: u32 = 1;

/// Fingerprint of the effective canonicalization policy: resolved
/// formatter options plus the enabled auto-fix-capable rules and the
/// options that shape their fixes — never unrelated severities. One
/// implementation serves record writers and this crate's verifier.
pub fn canonicalization_digest(config: &Config) -> String {
    let fix_policy = |id: &str, contexts: &[&str]| {
        let cfg = config.cfg(id);
        if contexts.is_empty() {
            return ((cfg.base != Severity::Off) as u8).to_string();
        }
        contexts
            .iter()
            .map(|scope| format!("{scope}:{}", (cfg.severity(scope) != Severity::Off) as u8))
            .collect::<Vec<_>>()
            .join(",")
    };
    let indent = match config.indent_style {
        IndentStyle::Tabs => "tab".to_string(),
        IndentStyle::Spaces => format!("space:{}", config.indent_size),
    };
    let unit_style = match config.unit_style {
        None => "-",
        Some(UnitStyle::QuotedProduct) => "quoted-product",
        Some(UnitStyle::Expression) => "expression",
    };
    let qualified_style = match config.qualified_style {
        None => "-",
        Some(QualifiedStyle::Qualified) => "qualified",
        Some(QualifiedStyle::Minimal) => "minimal",
        Some(QualifiedStyle::Imported) => "imported",
    };
    let text = format!(
        "v{};indent={indent};chain={};dimensional-consistency={};indentation={};\
         qualified-names={},{qualified_style};unit-spelling={},{unit_style};untyped-usage={}",
        CANONICALIZER_SCHEMA_VERSION,
        config.chain_min,
        fix_policy("dimensional-consistency", &["mismatch", "untyped"]),
        fix_policy("indentation", &[]),
        fix_policy("qualified-names", &[]),
        fix_policy("unit-spelling", &[]),
        fix_policy("untyped-usage", &["AttributeUsage"]),
    );
    format!(
        "sha256:{}",
        sysmlv2_model::structure::sha256_hex(text.as_bytes())
    )
}

const GEN_PROVENANCE_QN: &str = "TransformMeta::TransformProvenance";
const GEN_EXCLUSION_QN: &str = "TransformMeta::TransformExclusion";
const GEN_STATE_QN: &str = "TransformMeta::TransformState";
const GEN_SOURCE_QN: &str = "TransformMeta::TransformSource";
const STORE_KEY_PREFIX: &str = "provenance:";

fn digest_shaped(v: &str) -> bool {
    v.len() == 71
        && v.starts_with("sha256:")
        && v[7..]
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// The derived sidecar unit name for a content unit — keep in
/// lockstep with the materializer's derivation.
fn sidecar_unit_name(content_unit: &str) -> String {
    let stem = content_unit
        .strip_suffix(".sysml")
        .or_else(|| content_unit.strip_suffix(".kerml"))
        .unwrap_or(content_unit);
    format!("{stem}.provenance.sysml")
}

fn line_indent_of(src: &str, pos: usize) -> &str {
    let line_start = src[..pos.min(src.len())]
        .rfind('\n')
        .map(|i| i + 1)
        .unwrap_or(0);
    let line = &src[line_start..pos.min(src.len())];
    &line[..line.len() - line.trim_start_matches([' ', '\t']).len()]
}

fn unwrap_formatted(formatted: &str) -> String {
    let mut lines: Vec<&str> = formatted.split('\n').collect();
    while lines.last().is_some_and(|l| l.trim().is_empty()) {
        lines.pop();
    }
    if lines.len() < 2 {
        return String::new();
    }
    let inner = &lines[1..lines.len() - 1];
    let indent = inner
        .iter()
        .find(|l| !l.trim().is_empty())
        .map(|l| &l[..l.len() - l.trim_start_matches([' ', '\t']).len()])
        .unwrap_or("");
    inner
        .iter()
        .map(|l| l.strip_prefix(indent).unwrap_or(l.trim_start()))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Canonical member bytes under the project's formatter options —
/// format only, no auto-fix pass: recorded text already went through
/// the fixes, and a fix-relevant policy change reads as fingerprint
/// drift before any byte comparison happens. Public so record writers
/// and fixtures compute the exact bytes this crate verifies.
pub fn canonical_member_text(raw: &str, config: &Config) -> Result<String, String> {
    let lf = raw.replace("\r\n", "\n");
    let wrapped = format!("package __sysmlGeneratedGuard__ {{\n{lf}\n}}");
    let formatted = sysmlv2_syntax::print::format_source_opts(
        &wrapped,
        sysmlv2_syntax::ast::Dialect::Sysml,
        sysmlv2_syntax::print::PrintOptions {
            indent: config.format_indent(),
            multiline_chains: config.format_chain_min(),
            ..Default::default()
        },
    )
    .map_err(|d| {
        d.first()
            .map(|d| d.message.clone())
            .unwrap_or_else(|| "unparseable member".into())
    })?;
    Ok(unwrap_formatted(&formatted))
}

struct GenRecord {
    el: ElementRef,
    exclusion: bool,
    anchor: Option<(usize, Span)>,
    transform_id: Option<String>,
    key: Option<String>,
    source: Option<String>,
    path: Option<String>,
    row_digest: Option<String>,
    spelling_digest: Option<String>,
    structure_digest: Option<String>,
    policy_digest: Option<String>,
    sources: Vec<GenStateSource>,
    valid: bool,
    targets: Vec<ElementRef>,
    store: Option<ElementRef>,
}

/// One source entry of a parsed TransformState record (AA7h0),
/// span-ordered so `sources` reads in declaration order.
struct GenStateSource {
    alias: Option<String>,
    source_ref: Option<String>,
    input_digest: Option<String>,
    /// Rows the source delivered at the last run — a diagnostic-tier
    /// fact for approximate staleness arithmetic. Lenient: a missing
    /// or malformed spelling degrades to None and never invalidates
    /// the record.
    row_count: Option<u64>,
    start: u32,
}

/// The per-(store, transformId) state record (AA7h0): the last
/// successful run's checkpoint. Managed provenance resolves its
/// transformer-level facts through this record — never inline.
struct GenState {
    el: ElementRef,
    anchor: Option<(usize, Span)>,
    store: Option<ElementRef>,
    transform_id: Option<String>,
    transformer_path: Option<String>,
    script_digest: Option<String>,
    forced: bool,
    forced_valid: bool,
    sources: Vec<GenStateSource>,
    /// Complete, internally valid checkpoint fields. Pair uniqueness
    /// and managed-record correspondence are audited separately.
    valid: bool,
}

/// One ownership range that is safe for an editor to guard. Rows are
/// emitted only after the same store/pair/target audit used by the
/// generated-provenance lint rules succeeds completely.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedRange {
    pub unit: usize,
    pub start: u32,
    pub end: u32,
    pub key: String,
    pub transform_id: String,
    pub source: Option<String>,
    /// Complete ordered source identity. Managed rows resolve this
    /// through TransformState; exclusions carry it themselves.
    pub sources: Vec<GeneratedStateSource>,
    pub transformer_path: Option<String>,
    pub member_qn: Option<String>,
    pub member_id: String,
    pub record_id: String,
    pub raw: String,
    pub excluded: bool,
    /// The record's stored row digest (AA7h/AA7h0) — the staleness
    /// monitor's membership key. None when the record predates it.
    pub row_digest: Option<String>,
}

/// A valid targetless exclusion. Its source/path facts make tombstones
/// reachable from editor management UI even though they have no member
/// range to decorate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedTombstone {
    pub key: String,
    pub transform_id: String,
    pub source: Option<String>,
    pub sources: Vec<GeneratedStateSource>,
    pub transformer_path: Option<String>,
    pub record_id: String,
}

/// One state-record source entry, declaration-ordered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedStateSource {
    pub alias: String,
    pub source_ref: String,
    pub input_digest: Option<String>,
    /// Rows the source delivered at the last run (diagnostic-tier;
    /// never part of validity).
    pub row_count: Option<u64>,
}

/// The validated per-(store, transformId) state record (AA7h0): the
/// last successful run's checkpoint — transformer-level facts managed
/// provenance resolves through instead of restating.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedState {
    pub transform_id: String,
    pub transformer_path: String,
    pub script_digest: Option<String>,
    pub forced_schema_drift: bool,
    pub sources: Vec<GeneratedStateSource>,
    pub target_qn: Option<String>,
    pub record_id: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GeneratedInventory {
    pub members: Vec<GeneratedRange>,
    pub excluded: Vec<GeneratedRange>,
    pub tombstones: Vec<GeneratedTombstone>,
    pub states: Vec<GeneratedState>,
}

/// Native, validated generated-ownership inventory for editor hosts.
/// This deliberately performs only the ownership audit, not baseline
/// formatting/drift classification, so a 10k-member guard refresh stays
/// linear and does not re-format every member.
pub fn generated_inventory(
    resolved: &mut ResolvedModel,
    units: &[(usize, &str, &str)],
) -> GeneratedInventory {
    let mut inventory = GeneratedInventory::default();
    generated_guard(
        resolved,
        &Config::default(),
        units,
        &mut Vec::new(),
        Some(&mut inventory),
        true,
    );
    inventory
}

/// One parsed inventory feeding all three rules.
fn generated_guard(
    resolved: &mut ResolvedModel,
    config: &Config,
    units: &[(usize, &str, &str)],
    out: &mut Vec<Finding>,
    inventory: Option<&mut GeneratedInventory>,
    inventory_only: bool,
) {
    let invalid_cfg = config.cfg("generated-provenance-invalid");
    let outdated_cfg = config.cfg("generated-provenance-baseline-outdated");
    let modified_cfg = config.cfg("generated-element-modified");
    let unit_names: std::collections::HashMap<usize, &str> =
        units.iter().map(|&(i, n, _)| (i, n)).collect();
    let unit_texts: std::collections::HashMap<usize, &str> =
        units.iter().map(|&(i, _, t)| (i, t)).collect();

    // Resolve the two record types once. Asking for typings twice and
    // re-rendering every type's qualified name dominated large editor
    // inventories (20k metadata usages at the 10k-member gate).
    let provenance_type = resolved.resolve_qualified(GEN_PROVENANCE_QN);
    let exclusion_type = resolved.resolve_qualified(GEN_EXCLUSION_QN);
    let state_type = resolved.resolve_qualified(GEN_STATE_QN);
    let source_type = resolved.resolve_qualified(GEN_SOURCE_QN);
    // Prefix markers (`#TransformMeta::Generated …`) are metadata
    // usages with no recorded typing — identify them by the owner's
    // head text, exactly as the materializer does.
    let generated_head = regex_lite::Regex::new(r"^#\s*(TransformMeta\s*::\s*)?Generated\b")
        .expect("static pattern");
    let store_head = regex_lite::Regex::new(r"^#\s*(TransformMeta\s*::\s*)?ProvenanceStore\b")
        .expect("static pattern");
    let head_of = |resolved: &mut ResolvedModel,
                   unit_texts: &std::collections::HashMap<usize, &str>,
                   e: ElementRef|
     -> Option<String> {
        let (unit, span) = resolved.member_extent(e)?;
        let text = unit_texts.get(&unit)?;
        let raw = text.get(span.start as usize..span.end as usize)?;
        Some(raw.trim_start().chars().take(80).collect())
    };
    let anchor_of = |resolved: &mut ResolvedModel, e: ElementRef| {
        resolved
            .declaration_site(e)
            .or_else(|| resolved.member_extent(e))
    };
    let push = |out: &mut Vec<Finding>,
                rule: &'static str,
                severity: Severity,
                message: String,
                anchor: Option<(usize, Span)>,
                element: Option<String>| {
        let mut f = finding(rule, severity, message);
        if let Some((unit, span)) = anchor {
            f.unit = Some(unit);
            f.span = Some(span);
        }
        f.element = element;
        out.push(f);
    };

    // ---- collect markers, stores, records ----
    let user_elements: Vec<ElementRef> = resolved.user_elements().collect();
    let usages: Vec<ElementRef> = user_elements
        .iter()
        .copied()
        .filter(|e| resolved.element_type(*e) == "MetadataUsage")
        .collect();
    // `ResolvedModel::owned_members` is optimized for occasional
    // navigation and scans the element arena. Inventory needs the
    // fields of every record, so invert ownership once instead of
    // paying one arena scan per record.
    let mut owned_by: std::collections::HashMap<ElementRef, Vec<ElementRef>> = Default::default();
    for e in user_elements {
        if let Some(owner) = resolved.owner(e) {
            owned_by.entry(owner).or_default().push(e);
        }
    }
    let mut marked_members: std::collections::HashSet<ElementRef> = Default::default();
    let mut marked_stores: std::collections::HashSet<ElementRef> = Default::default();
    let mut records: Vec<GenRecord> = Vec::new();
    let mut states: Vec<GenState> = Vec::new();
    // Attribute name/value pairs of one metadata usage — the shared
    // extraction records, states, and state sources all read through.
    fn metadata_fields(
        resolved: &mut ResolvedModel,
        owned_by: &std::collections::HashMap<ElementRef, Vec<ElementRef>>,
        unit_texts: &std::collections::HashMap<usize, &str>,
        e: ElementRef,
    ) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for a in owned_by.get(&e).into_iter().flatten().copied() {
            let Some(name) = resolved.element_name(a).map(str::to_string) else {
                continue;
            };
            let Some((_, expr)) = resolved.value_expr(a) else {
                continue;
            };
            let Some((unit, _)) = resolved
                .declaration_site(a)
                .or_else(|| resolved.member_extent(a))
            else {
                continue;
            };
            let Some(text) = unit_texts.get(&unit) else {
                continue;
            };
            let Some(spelling) = text.get(expr.span.start as usize..expr.span.end as usize) else {
                continue;
            };
            let value =
                serde_json::from_str::<String>(spelling).unwrap_or_else(|_| spelling.to_string());
            out.push((name, value));
        }
        out
    }
    fn metadata_sources(
        resolved: &mut ResolvedModel,
        owned_by: &std::collections::HashMap<ElementRef, Vec<ElementRef>>,
        unit_texts: &std::collections::HashMap<usize, &str>,
        source_type: Option<ElementRef>,
        owner: ElementRef,
    ) -> Vec<GenStateSource> {
        let mut sources = Vec::new();
        for child in owned_by.get(&owner).into_iter().flatten().copied() {
            if resolved.element_type(child) != "MetadataUsage"
                || !source_type.is_some_and(|ty| resolved.typings(child).contains(&ty))
            {
                continue;
            }
            let mut source = GenStateSource {
                alias: None,
                source_ref: None,
                input_digest: None,
                row_count: None,
                start: resolved
                    .member_extent(child)
                    .map(|(_, span)| span.start)
                    .unwrap_or(u32::MAX),
            };
            for (name, value) in metadata_fields(resolved, owned_by, unit_texts, child) {
                match name.as_str() {
                    "sourceAlias" => source.alias = Some(value),
                    "sourceRef" => source.source_ref = Some(value),
                    "inputDigest" => source.input_digest = Some(value),
                    "rowCount" => source.row_count = value.parse().ok(),
                    _ => {}
                }
            }
            sources.push(source);
        }
        sources.sort_by_key(|source| source.start);
        sources
    }
    for u in usages {
        let typings = resolved.typings(u);
        let is_prov = provenance_type.is_some_and(|ty| typings.contains(&ty));
        let is_excl = exclusion_type.is_some_and(|ty| typings.contains(&ty));
        let is_state = state_type.is_some_and(|ty| typings.contains(&ty));
        let is_source = source_type.is_some_and(|ty| typings.contains(&ty));
        if is_source {
            // Parsed through its owning state record below.
            continue;
        }
        if is_state {
            let mut st = GenState {
                el: u,
                anchor: anchor_of(resolved, u),
                store: resolved.owner(u),
                transform_id: None,
                transformer_path: None,
                script_digest: None,
                forced: false,
                forced_valid: true,
                sources: Vec::new(),
                valid: false,
            };
            for (name, value) in metadata_fields(resolved, &owned_by, &unit_texts, u) {
                match name.as_str() {
                    "transformId" => st.transform_id = Some(value),
                    "transformerPath" => st.transformer_path = Some(value),
                    "scriptDigest" => st.script_digest = Some(value),
                    "forcedSchemaDrift" => {
                        st.forced = value == "true";
                        st.forced_valid = st.forced;
                    }
                    _ => {}
                }
            }
            st.sources = metadata_sources(resolved, &owned_by, &unit_texts, source_type, u);
            states.push(st);
            continue;
        }
        if !is_prov && !is_excl {
            // A typing-less usage may be a prefix marker; the owner's
            // head text decides.
            if let Some(owner) = resolved.owner(u) {
                if let Some(head) = head_of(resolved, &unit_texts, owner) {
                    if generated_head.is_match(&head) {
                        marked_members.insert(owner);
                    } else if store_head.is_match(&head) {
                        marked_stores.insert(owner);
                    }
                }
            }
            continue;
        }
        let mut rec = GenRecord {
            el: u,
            exclusion: is_excl,
            anchor: anchor_of(resolved, u),
            transform_id: None,
            key: None,
            source: None,
            path: None,
            row_digest: None,
            spelling_digest: None,
            structure_digest: None,
            policy_digest: None,
            sources: Vec::new(),
            valid: true,
            targets: resolved.annotated_elements(u),
            store: resolved.owner(u),
        };
        for a in owned_by.get(&u).into_iter().flatten().copied() {
            let Some(name) = resolved.element_name(a).map(str::to_string) else {
                continue;
            };
            let Some((_, expr)) = resolved.value_expr(a) else {
                continue;
            };
            let Some((unit, _)) = anchor_of(resolved, a) else {
                continue;
            };
            let Some(text) = unit_texts.get(&unit) else {
                continue;
            };
            let Some(spelling) = text.get(expr.span.start as usize..expr.span.end as usize) else {
                continue;
            };
            let value =
                serde_json::from_str::<String>(spelling).unwrap_or_else(|_| spelling.to_string());
            match name.as_str() {
                "transformId" => rec.transform_id = Some(value),
                "key" => rec.key = Some(value),
                "source" => rec.source = Some(value),
                "transformerPath" => rec.path = Some(value),
                "rowDigest" => rec.row_digest = Some(value),
                "spellingDigest" => rec.spelling_digest = Some(value),
                "structureDigest" => rec.structure_digest = Some(value),
                "policyDigest" => rec.policy_digest = Some(value),
                _ => {}
            }
        }
        if rec.exclusion {
            rec.sources = metadata_sources(resolved, &owned_by, &unit_texts, source_type, u);
        }
        records.push(rec);
    }

    // ---- store contract audit ----
    let mut store_ok: std::collections::HashMap<ElementRef, bool> = Default::default();
    let mut store_targets: std::collections::HashMap<ElementRef, ElementRef> = Default::default();
    for store in marked_stores
        .iter()
        .copied()
        .chain(records.iter().filter_map(|r| r.store))
        .collect::<std::collections::BTreeSet<_>>()
    {
        let severity = invalid_cfg.severity(resolved.element_type(store));
        let anchor = anchor_of(resolved, store);
        let element = edit_target(resolved, store);
        let fail = |out: &mut Vec<Finding>, detail: String, ok: &mut bool| {
            *ok = false;
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    detail,
                    anchor,
                    element.clone(),
                );
            }
        };
        let mut ok = true;
        let spelled = resolved
            .element_qualified_name(store)
            .unwrap_or_else(|| "<anonymous>".into());
        let marked = marked_stores.contains(&store);
        let ty = resolved.element_type(store).to_string();
        let short = resolved.element_short_name(store).map(str::to_string);
        let top_level = match resolved.owner(store) {
            None => true,
            Some(parent) => {
                resolved.element_type(parent) == "Namespace" && resolved.owner(parent).is_none()
            }
        };
        if !marked {
            fail(
                out,
                format!(
                    "`{spelled}` holds provenance records but carries no ProvenanceStore marker"
                ),
                &mut ok,
            );
        }
        if ty != "Package" {
            fail(
                out,
                format!("provenance store `{spelled}` is a {ty}, not a Package"),
                &mut ok,
            );
        }
        if !top_level {
            fail(
                out,
                format!("provenance store `{spelled}` is not a top-level member of its unit"),
                &mut ok,
            );
        }
        match short.as_deref() {
            Some(short) if short.starts_with(STORE_KEY_PREFIX) => {
                let target_qn = &short[STORE_KEY_PREFIX.len()..];
                match resolved.resolve_qualified(target_qn) {
                    None => fail(
                        out,
                        format!(
                            "provenance store `{spelled}` is keyed to `{target_qn}`, which \
                             does not resolve"
                        ),
                        &mut ok,
                    ),
                    Some(target) => {
                        store_targets.insert(store, target);
                        let content_unit = resolved
                            .member_extent(target)
                            .and_then(|(u, _)| unit_names.get(&u).copied())
                            .unwrap_or("");
                        let expected = sidecar_unit_name(content_unit);
                        let actual = resolved
                            .member_extent(store)
                            .and_then(|(u, _)| unit_names.get(&u).copied())
                            .unwrap_or("");
                        if !content_unit.is_empty() && actual != expected {
                            fail(
                                out,
                                format!(
                                    "provenance store `{spelled}` lives in `{actual}`; its \
                                     target's derived sidecar is `{expected}`"
                                ),
                                &mut ok,
                            );
                        }
                    }
                }
            }
            _ => fail(
                out,
                format!(
                    "provenance store `{spelled}` lacks the `{STORE_KEY_PREFIX}<target>` \
                     short-name key"
                ),
                &mut ok,
            ),
        }
        store_ok.insert(store, ok);
    }

    // ---- state audit (AA7h0): one TransformState per (store, id) ----
    // The state record is the only home of transformer-level facts;
    // managed provenance resolves through it. Missing or duplicate
    // state is corruption under the clean-break protocol: findings
    // here, and the affected rows never reach the inventory.
    let mut state_by_pair: std::collections::HashMap<(ElementRef, String), Vec<usize>> =
        Default::default();
    for (i, st) in states.iter_mut().enumerate() {
        let severity = invalid_cfg.severity(resolved.element_type(st.el));
        let element = edit_target(resolved, st.el);
        let mut problems = Vec::new();
        let Some(id) = st.transform_id.clone().filter(|id| !id.is_empty()) else {
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    "TransformState record lacks its transformId".into(),
                    st.anchor,
                    element,
                );
            }
            continue;
        };
        if st.transformer_path.as_deref().is_none_or(str::is_empty) {
            problems.push(format!("TransformState for `{id}` lacks transformerPath"));
        }
        if st
            .script_digest
            .as_deref()
            .is_none_or(|d| !digest_shaped(d))
        {
            problems.push(format!(
                "TransformState for `{id}` lacks a valid scriptDigest"
            ));
        }
        if st.sources.is_empty() {
            problems.push(format!("TransformState for `{id}` declares no sources"));
        }
        if !st.forced_valid {
            problems.push(format!(
                "TransformState for `{id}` carries a malformed forcedSchemaDrift"
            ));
        }
        let mut aliases: std::collections::HashSet<&str> = Default::default();
        for source in &st.sources {
            if source.alias.as_deref().is_none_or(str::is_empty)
                || source.source_ref.as_deref().is_none_or(str::is_empty)
            {
                problems.push(format!(
                    "TransformState for `{id}` has a source entry lacking sourceAlias/sourceRef"
                ));
            }
            if let Some(alias) = source.alias.as_deref() {
                if !aliases.insert(alias) {
                    problems.push(format!(
                        "TransformState for `{id}` repeats source alias `{alias}`"
                    ));
                }
            }
            let query = source
                .source_ref
                .as_deref()
                .is_some_and(|source_ref| source_ref.starts_with("query:"));
            let digest_valid = match (query, source.input_digest.as_deref()) {
                (true, None) => true,
                (false, Some(digest)) => digest_shaped(digest),
                _ => false,
            };
            if !digest_valid {
                problems.push(format!(
                    "TransformState for `{id}` has a source without a valid inputDigest"
                ));
            }
        }
        st.valid = problems.is_empty();
        if severity != Severity::Off {
            for detail in problems {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    detail,
                    st.anchor,
                    element.clone(),
                );
            }
        }
        if let Some(store) = st.store {
            state_by_pair.entry((store, id)).or_default().push(i);
        }
    }
    for ((_, id), indices) in state_by_pair.iter() {
        for &i in indices.iter().skip(1) {
            let st = &states[i];
            let severity = invalid_cfg.severity(resolved.element_type(st.el));
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!("duplicate TransformState records for `{id}`"),
                    st.anchor,
                    edit_target(resolved, st.el),
                );
            }
        }
    }
    // Exactly one state for the pair, with its identity intact.
    let state_for_pair =
        |state_by_pair: &std::collections::HashMap<(ElementRef, String), Vec<usize>>,
         store: ElementRef,
         id: &str|
         -> Option<usize> {
            match state_by_pair
                .get(&(store, id.to_string()))
                .map(Vec::as_slice)
            {
                Some([only]) if states[*only].valid => Some(*only),
                _ => None,
            }
        };

    // ---- pair maps + duplicate / conflict audit ----
    let mut prov_by_pair: std::collections::HashMap<(String, String), usize> = Default::default();
    let mut excl_pairs: std::collections::HashSet<(String, String)> = Default::default();
    let mut pair_counts: std::collections::HashMap<(String, String, bool), usize> =
        Default::default();
    for (i, rec) in records.iter_mut().enumerate() {
        let anchor = rec.anchor;
        let severity = invalid_cfg.severity(resolved.element_type(rec.el));
        let element = edit_target(resolved, rec.el);
        let (Some(id), Some(key)) = (rec.transform_id.clone(), rec.key.clone()) else {
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    "provenance record lacks its transformId/key identity fields".into(),
                    anchor,
                    element,
                );
            }
            continue;
        };
        if rec.exclusion {
            let mut problems = Vec::new();
            if rec.path.as_deref().is_none_or(str::is_empty) {
                problems.push(format!(
                    "TransformExclusion for ({id}, {key}) lacks transformerPath"
                ));
            }
            if rec.sources.is_empty() {
                problems.push(format!(
                    "TransformExclusion for ({id}, {key}) declares no sources"
                ));
            }
            let mut aliases: std::collections::HashSet<&str> = Default::default();
            for source in &rec.sources {
                if source.alias.as_deref().is_none_or(str::is_empty)
                    || source.source_ref.as_deref().is_none_or(str::is_empty)
                {
                    problems.push(format!(
                        "TransformExclusion for ({id}, {key}) has a source entry lacking sourceAlias/sourceRef"
                    ));
                }
                if let Some(alias) = source.alias.as_deref() {
                    if !aliases.insert(alias) {
                        problems.push(format!(
                            "TransformExclusion for ({id}, {key}) repeats source alias `{alias}`"
                        ));
                    }
                }
                let query = source
                    .source_ref
                    .as_deref()
                    .is_some_and(|source_ref| source_ref.starts_with("query:"));
                let digest_valid = match (query, source.input_digest.as_deref()) {
                    (true, None) => true,
                    (false, Some(digest)) => digest_shaped(digest),
                    _ => false,
                };
                if !digest_valid {
                    problems.push(format!(
                        "TransformExclusion for ({id}, {key}) has a source without a valid inputDigest"
                    ));
                }
            }
            rec.valid = problems.is_empty();
            if severity != Severity::Off {
                for detail in problems {
                    push(
                        out,
                        "generated-provenance-invalid",
                        severity,
                        detail,
                        anchor,
                        element.clone(),
                    );
                }
            }
        }
        let pair = (id.clone(), key.clone());
        *pair_counts
            .entry((id.clone(), key.clone(), rec.exclusion))
            .or_default() += 1;
        if rec.exclusion {
            if !excl_pairs.insert(pair.clone()) && severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!("duplicate exclusions for ({id}, {key})"),
                    anchor,
                    element.clone(),
                );
            }
        } else if let Some(prev) = prov_by_pair.insert(pair.clone(), i) {
            let _ = prev;
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!("duplicate provenance claims for ({id}, {key})"),
                    anchor,
                    element.clone(),
                );
            }
        }
    }
    for pair in prov_by_pair.keys() {
        if excl_pairs.contains(pair) {
            let rec = &records[prov_by_pair[pair]];
            let severity = invalid_cfg.severity(resolved.element_type(rec.el));
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "both a provenance record and an exclusion exist for ({}, {})",
                        pair.0, pair.1
                    ),
                    rec.anchor,
                    edit_target(resolved, rec.el),
                );
            }
        }
    }

    // A generated member has exactly one provenance owner, independent
    // of transform id. Two records with different pairs are still two
    // writers for the same bytes and therefore unsafe to guard.
    let mut owners_by_target: std::collections::HashMap<ElementRef, Vec<usize>> =
        Default::default();
    for (i, rec) in records.iter().enumerate() {
        if !rec.exclusion && rec.targets.len() == 1 {
            owners_by_target.entry(rec.targets[0]).or_default().push(i);
        }
    }
    for owners in owners_by_target.values().filter(|owners| owners.len() > 1) {
        for &i in owners.iter().skip(1) {
            let rec = &records[i];
            let severity = invalid_cfg.severity(resolved.element_type(rec.el));
            if severity != Severity::Off {
                let member = rec.targets[0];
                let member_spelled = resolved
                    .element_qualified_name(member)
                    .unwrap_or_else(|| "<member>".into());
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "generated member `{member_spelled}` is claimed by multiple provenance records"
                    ),
                    rec.anchor,
                    edit_target(resolved, rec.el),
                );
            }
        }
    }

    // ---- state ↔ managed-record correspondence (AA7h0) ----
    let mut managed_pairs: std::collections::BTreeSet<(ElementRef, String)> = Default::default();
    let mut first_managed_rec: std::collections::HashMap<(ElementRef, String), usize> =
        Default::default();
    for (i, rec) in records.iter().enumerate() {
        if rec.exclusion {
            continue;
        }
        let (Some(store), Some(id)) = (rec.store, rec.transform_id.clone()) else {
            continue;
        };
        first_managed_rec.entry((store, id.clone())).or_insert(i);
        managed_pairs.insert((store, id));
    }
    for (store, id) in &managed_pairs {
        if state_by_pair.contains_key(&(*store, id.clone())) {
            continue;
        }
        let rec = &records[first_managed_rec[&(*store, id.clone())]];
        let severity = invalid_cfg.severity(resolved.element_type(rec.el));
        if severity != Severity::Off {
            push(
                out,
                "generated-provenance-invalid",
                severity,
                format!(
                    "managed provenance for `{id}` has no TransformState record — the sidecar                      predates the state protocol or was hand-edited; delete it and rerun the                      transformer"
                ),
                rec.anchor,
                edit_target(resolved, rec.el),
            );
        }
    }
    for ((store, id), indices) in state_by_pair.iter() {
        if managed_pairs.contains(&(*store, id.clone())) {
            continue;
        }
        let st = &states[indices[0]];
        let severity = invalid_cfg.severity(resolved.element_type(st.el));
        if severity != Severity::Off {
            push(
                out,
                "generated-provenance-invalid",
                severity,
                format!("TransformState for `{id}` has no managed provenance records"),
                st.anchor,
                edit_target(resolved, st.el),
            );
        }
    }

    if let Some(inventory) = inventory {
        for rec in &records {
            let (Some(transform_id), Some(key), Some(store)) =
                (rec.transform_id.as_ref(), rec.key.as_ref(), rec.store)
            else {
                continue;
            };
            if store_ok.get(&store) != Some(&true) {
                continue;
            }
            if !rec.valid {
                continue;
            }
            let pair = (transform_id.clone(), key.clone(), rec.exclusion);
            if pair_counts.get(&pair) != Some(&1)
                || pair_counts.contains_key(&(transform_id.clone(), key.clone(), !rec.exclusion))
            {
                continue;
            }
            let target_package = store_targets.get(&store).copied();
            let malformed_digest = [
                rec.row_digest.as_deref(),
                rec.spelling_digest.as_deref(),
                rec.structure_digest.as_deref(),
                rec.policy_digest.as_deref(),
            ]
            .into_iter()
            .flatten()
            .any(|value| !digest_shaped(value));
            if malformed_digest {
                continue;
            }
            // AA7h0: a managed row's transformer-level facts resolve
            // through the pair's unique TransformState — no state, no
            // row (the correspondence audit already named why).
            let state = if rec.exclusion {
                None
            } else {
                match state_for_pair(&state_by_pair, store, transform_id) {
                    Some(i) => Some(&states[i]),
                    None => continue,
                }
            };
            let source_facts = match state {
                Some(state) => &state.sources,
                None => &rec.sources,
            };
            let sources: Vec<GeneratedStateSource> = source_facts
                .iter()
                .filter_map(|source| {
                    Some(GeneratedStateSource {
                        alias: source.alias.clone()?,
                        source_ref: source.source_ref.clone()?,
                        input_digest: source.input_digest.clone(),
                        row_count: source.row_count,
                    })
                })
                .collect();
            if rec.exclusion && rec.targets.is_empty() {
                inventory.tombstones.push(GeneratedTombstone {
                    key: key.clone(),
                    transform_id: transform_id.clone(),
                    source: sources.first().map(|source| source.source_ref.clone()),
                    sources,
                    transformer_path: rec.path.clone(),
                    record_id: resolved.element_id(rec.el).to_string(),
                });
                continue;
            }
            if rec.targets.len() != 1 {
                continue;
            }
            let member = rec.targets[0];
            if target_package.is_none()
                || resolved.owner(member) != target_package
                || (rec.exclusion && marked_members.contains(&member))
                || (!rec.exclusion && !marked_members.contains(&member))
                || (!rec.exclusion
                    && owners_by_target
                        .get(&member)
                        .is_none_or(|owners| owners.len() != 1))
                || (!rec.exclusion && resolved.element_short_name(member) != Some(key.as_str()))
            {
                continue;
            }
            let Some((unit, extent)) = resolved.member_extent(member) else {
                continue;
            };
            let (Some(text), Some(_name)) = (unit_texts.get(&unit), unit_names.get(&unit)) else {
                continue;
            };
            let Some(raw) = text.get(extent.start as usize..extent.end as usize) else {
                continue;
            };
            let row = GeneratedRange {
                unit,
                start: extent.start,
                end: extent.end,
                key: key.clone(),
                transform_id: transform_id.clone(),
                // Managed rows resolve through the state record (the
                // first source is the row-level column); exclusions
                // stay self-contained by ratified design.
                source: sources.first().map(|source| source.source_ref.clone()),
                sources,
                transformer_path: match state {
                    Some(st) => st.transformer_path.clone(),
                    None => rec.path.clone(),
                },
                member_qn: resolved.element_qualified_name(member),
                member_id: resolved.element_id(member).to_string(),
                record_id: resolved.element_id(rec.el).to_string(),
                raw: raw.to_string(),
                excluded: rec.exclusion,
                row_digest: rec.row_digest.clone(),
            };
            if rec.exclusion {
                inventory.excluded.push(row);
            } else {
                inventory.members.push(row);
            }
        }
        for ((store, id), indices) in state_by_pair.iter() {
            let [only] = indices.as_slice() else {
                continue; // duplicates already found; no surface row
            };
            if store_ok.get(store) != Some(&true) || !managed_pairs.contains(&(*store, id.clone()))
            {
                continue;
            }
            let st = &states[*only];
            if !st.valid {
                continue;
            }
            inventory.states.push(GeneratedState {
                transform_id: id.clone(),
                transformer_path: st.transformer_path.clone().unwrap_or_default(),
                script_digest: st.script_digest.clone(),
                forced_schema_drift: st.forced,
                sources: st
                    .sources
                    .iter()
                    .filter_map(|source| {
                        Some(GeneratedStateSource {
                            alias: source.alias.clone()?,
                            source_ref: source.source_ref.clone()?,
                            input_digest: source.input_digest.clone(),
                            row_count: source.row_count,
                        })
                    })
                    .collect(),
                target_qn: store_targets
                    .get(store)
                    .and_then(|t| resolved.element_qualified_name(*t)),
                record_id: resolved.element_id(st.el).to_string(),
            });
        }
        inventory.states.sort_by(|a, b| {
            a.target_qn
                .cmp(&b.target_qn)
                .then(a.transform_id.cmp(&b.transform_id))
        });
        let by_position = |a: &GeneratedRange, b: &GeneratedRange| {
            a.unit.cmp(&b.unit).then(a.start.cmp(&b.start))
        };
        inventory.members.sort_by(by_position);
        inventory.excluded.sort_by(by_position);
        inventory
            .tombstones
            .sort_by(|a, b| a.transform_id.cmp(&b.transform_id).then(a.key.cmp(&b.key)));
    }
    if inventory_only {
        return;
    }

    // ---- record → target joins, baseline audit, drift classification ----
    let policy = canonicalization_digest(config);
    let mut claimed: std::collections::HashSet<ElementRef> = Default::default();
    for rec in &records {
        let severity = invalid_cfg.severity(resolved.element_type(rec.el));
        let anchor = rec.anchor;
        let element = edit_target(resolved, rec.el);
        let spelled = resolved
            .element_qualified_name(rec.el)
            .or_else(|| rec.key.clone())
            .unwrap_or_else(|| "<record>".into());
        if rec.exclusion {
            if rec.targets.len() > 1 && severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "exclusion `{spelled}` annotates {} members — at most one adopted member is allowed",
                        rec.targets.len()
                    ),
                    anchor,
                    element.clone(),
                );
            }
            // A tombstone may be targetless; a targeted exclusion must
            // point at an *unmarked* (adopted, hand-owned) member — an
            // exclusion is never a provenance claim, so a marked member
            // it targets still reads as marker-only corruption too.
            for t in &rec.targets {
                if marked_members.contains(t) && severity != Severity::Off {
                    push(
                        out,
                        "generated-provenance-invalid",
                        severity,
                        format!(
                            "exclusion `{spelled}` targets a member still carrying the \
                             Generated marker"
                        ),
                        anchor,
                        element.clone(),
                    );
                }
                if let Some(target_package) = rec.store.and_then(|s| store_targets.get(&s)).copied()
                {
                    if resolved.owner(*t) != Some(target_package) && severity != Severity::Off {
                        let package = resolved
                            .element_qualified_name(target_package)
                            .unwrap_or_else(|| "<target>".into());
                        push(
                            out,
                            "generated-provenance-invalid",
                            severity,
                            format!(
                                "exclusion `{spelled}` targets a member outside its store package `{package}`"
                            ),
                            anchor,
                            element.clone(),
                        );
                    }
                }
            }
            continue;
        }
        if rec.targets.len() != 1 {
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "provenance record `{spelled}` annotates {} members — exactly one \
                         generated member must carry it",
                        rec.targets.len()
                    ),
                    anchor,
                    element,
                );
            }
            continue;
        }
        let member = rec.targets[0];
        claimed.insert(member);
        let member_spelled = resolved
            .element_qualified_name(member)
            .unwrap_or_else(|| "<member>".into());
        if !marked_members.contains(&member) {
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "provenance record `{spelled}` annotates `{member_spelled}`, which \
                         does not carry the Generated marker"
                    ),
                    anchor,
                    element,
                );
            }
            continue;
        }
        if let Some(target_package) = rec.store.and_then(|s| store_targets.get(&s)).copied() {
            if resolved.owner(member) != Some(target_package) {
                if severity != Severity::Off {
                    let package = resolved
                        .element_qualified_name(target_package)
                        .unwrap_or_else(|| "<target>".into());
                    push(
                        out,
                        "generated-provenance-invalid",
                        severity,
                        format!(
                            "provenance record `{spelled}` targets a member outside its store package `{package}`"
                        ),
                        anchor,
                        element.clone(),
                    );
                }
                continue;
            }
        }
        if owners_by_target
            .get(&member)
            .is_some_and(|owners| owners.len() != 1)
        {
            continue;
        }
        if let (Some(key), Some(short)) = (
            rec.key.as_deref(),
            resolved.element_short_name(member).map(str::to_string),
        ) {
            if key != short && severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "provenance record for key `{key}` annotates a member whose short \
                         name is `{short}`"
                    ),
                    anchor,
                    element.clone(),
                );
                continue;
            }
        }
        // Malformed digest fields are corruption; absent AA6 fields are
        // valid legacy provenance.
        let mut malformed = false;
        for (label, value) in [
            ("spellingDigest", rec.spelling_digest.as_deref()),
            ("structureDigest", rec.structure_digest.as_deref()),
            ("policyDigest", rec.policy_digest.as_deref()),
        ] {
            if let Some(v) = value {
                if !digest_shaped(v) {
                    malformed = true;
                    if severity != Severity::Off {
                        push(
                            out,
                            "generated-provenance-invalid",
                            severity,
                            format!("record `{spelled}` has a malformed {label}"),
                            anchor,
                            element.clone(),
                        );
                    }
                }
            }
        }
        if malformed {
            continue;
        }
        let Some(spelling_digest) = rec.spelling_digest.as_deref() else {
            continue; // shapeless prototype record — ownership already audited
        };
        let (Some(structure_digest), Some(policy_digest)) = (
            rec.structure_digest.as_deref(),
            rec.policy_digest.as_deref(),
        ) else {
            let outdated = outdated_cfg.severity(resolved.element_type(member));
            if outdated != Severity::Off {
                push(
                    out,
                    "generated-provenance-baseline-outdated",
                    outdated,
                    format!(
                        "provenance for `{member_spelled}` predates the structure/policy \
                         baseline — the next successful sync backfills it"
                    ),
                    anchor,
                    edit_target(resolved, member),
                );
            }
            continue;
        };

        // Drift classification: fingerprint first, then
        // structure, then canonical bytes, then raw spelling.
        let drift = modified_cfg.severity(resolved.element_type(member));
        let member_anchor = anchor_of(resolved, member);
        let member_element = edit_target(resolved, member);
        let Some((unit, extent)) = resolved.member_extent(member) else {
            continue;
        };
        let Some(unit_text) = unit_texts.get(&unit) else {
            continue;
        };
        let Some(raw) = unit_text.get(extent.start as usize..extent.end as usize) else {
            continue;
        };
        if policy_digest != policy {
            if drift != Severity::Off {
                push(
                    out,
                    "generated-element-modified",
                    drift,
                    format!(
                        "canonicalization policy changed since `{member_spelled}` was \
                         generated — baseline drift, not a manual edit; the next sync \
                         refreshes its record"
                    ),
                    member_anchor,
                    member_element,
                );
            }
            continue;
        }
        let current_structure = sysmlv2_model::structure::member_structure_digest(raw);
        match current_structure {
            Err(_) => {
                if drift != Severity::Off {
                    push(
                        out,
                        "generated-element-modified",
                        drift,
                        format!(
                            "generated member `{member_spelled}` was modified — it no \
                             longer parses standalone; resync to overwrite or adopt it"
                        ),
                        member_anchor,
                        member_element,
                    );
                }
                continue;
            }
            Ok(current) if current != structure_digest => {
                if drift != Severity::Off {
                    // AA7h0: the transformer-level facts live on the
                    // pair's state record, not the member record.
                    let state_facts =
                        rec.store
                            .zip(rec.transform_id.as_deref())
                            .and_then(|(store, id)| {
                                state_for_pair(&state_by_pair, store, id).map(|i| &states[i])
                            });
                    let provenance = match state_facts.and_then(|st| {
                        st.sources
                            .first()
                            .and_then(|source| source.source_ref.as_deref())
                            .zip(st.transformer_path.as_deref())
                    }) {
                        Some((s, p)) => format!(" (synced from {s} by {p})"),
                        None => String::new(),
                    };
                    push(
                        out,
                        "generated-element-modified",
                        drift,
                        format!(
                            "generated member `{member_spelled}` was modified — structure \
                             differs from its provenance baseline{provenance}; resync to \
                             overwrite or adopt it"
                        ),
                        member_anchor,
                        member_element,
                    );
                }
                continue;
            }
            Ok(_) => {}
        }
        let Ok(canonical) = canonical_member_text(raw, config) else {
            continue;
        };
        let canonical_digest = format!(
            "sha256:{}",
            sysmlv2_model::structure::sha256_hex(canonical.as_bytes())
        );
        if canonical_digest != spelling_digest {
            // Equal structure and policy with disagreeing canonical
            // bytes cannot happen against an honest baseline.
            if severity != Severity::Off {
                push(
                    out,
                    "generated-provenance-invalid",
                    severity,
                    format!(
                        "record for `{member_spelled}` has a corrupt baseline: canonical \
                         bytes disagree with textDigest while structure and policy match"
                    ),
                    anchor,
                    element.clone(),
                );
            }
            continue;
        }
        let base = line_indent_of(unit_text, extent.start as usize);
        let expected = sysmlv2_syntax::print::reindent_member_text(
            &canonical,
            base,
            sysmlv2_syntax::print::indent_unit(base, unit_text),
        );
        if raw.replace("\r\n", "\n") != expected && drift != Severity::Off {
            push(
                out,
                "generated-element-modified",
                drift,
                format!(
                    "generated member `{member_spelled}` formatting drifted from the \
                     canonical form (content unchanged); the next sync restores it"
                ),
                member_anchor,
                member_element,
            );
        }
    }

    // ---- marker-only members: corruption, never silently hand-written ----
    for member in &marked_members {
        if claimed.contains(member) {
            continue;
        }
        let severity = invalid_cfg.severity(resolved.element_type(*member));
        if severity == Severity::Off {
            continue;
        }
        let spelled = resolved
            .element_qualified_name(*member)
            .unwrap_or_else(|| "<member>".into());
        push(
            out,
            "generated-provenance-invalid",
            severity,
            format!(
                "`{spelled}` carries the Generated marker but no provenance record claims \
                 it — managed ownership is corrupt; resync, repair, or adopt explicitly"
            ),
            anchor_of(resolved, *member),
            edit_target(resolved, *member),
        );
    }
}
