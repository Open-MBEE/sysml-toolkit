//! `literal-pattern`: a string bound to a feature whose declared type
//! carries a `StringPatterns::Pattern` — on the type or a supertype, as a
//! member of its body or `about` it from another package, the ambient
//! `StringPatterns` library annotating the standard library's ISO 8601
//! date-time encoding — must match the annotation's regular expression
//! in full. The sites are feature values, constructor arguments (a
//! positional one binds the type's constructor sequence, a named one its
//! name) and calculation arguments (positional ones in parameter order).
//! A value matching the annotation's broader `accepts` form instead
//! reports at the rule's `reduced` severity. Configuration may supply or
//! override the pattern of a type by its qualified name. A lambda body
//! is not entered from the expression around it: its trailing expression
//! is a result expression of its own, read in the body's scope, where an
//! argument bound through a body parameter is undecided. Regular
//! expressions are written with their backslashes doubled inside a SysML
//! or JSON string (`\\.` for `\.`).
use crate::{Config, Finding, RuleId, Severity, edit_target, finding};
use regex_lite::Regex;
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use sysmlv2_model::eval::Value;
use sysmlv2_model::json::{ElementRef, ResolvedModel, ScopeRef};
use sysmlv2_syntax::ast::{Arg, Expr, ExprKind, TargetRef};
use sysmlv2_syntax::visit::{Visit, walk_expr};

/// The qualified name of the metadata definition the rule reads.
pub const PATTERN_METADATA: &str = "StringPatterns::Pattern";

/// A pattern as configuration or an annotation states it: the
/// expression the whole value must match, an optional broader form
/// reported at the reduced severity, and an optional spelling of the
/// format for findings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternSpec {
    pub regex: String,
    pub accepts: Option<String>,
    pub form: Option<String>,
}

impl PatternSpec {
    /// Read a configuration value: a bare regular expression, or an
    /// object with `regex` and the optional `accepts` and `form`.
    pub(crate) fn from_json(v: &serde_json::Value) -> Result<PatternSpec, String> {
        let spec = match v {
            serde_json::Value::String(regex) => PatternSpec {
                regex: regex.clone(),
                accepts: None,
                form: None,
            },
            serde_json::Value::Object(o) => {
                let text = |key: &str| -> Result<Option<String>, String> {
                    match o.get(key) {
                        None | Some(serde_json::Value::Null) => Ok(None),
                        Some(serde_json::Value::String(s)) => Ok(Some(s.clone())),
                        Some(_) => Err(format!("`{key}` must be a string")),
                    }
                };
                let Some(regex) = text("regex")? else {
                    return Err("needs a `regex`".to_string());
                };
                if let Some(key) = o
                    .keys()
                    .find(|k| !matches!(k.as_str(), "regex" | "accepts" | "form"))
                {
                    return Err(format!(
                        "has an unknown field `{key}` (expected regex, accepts, form)"
                    ));
                }
                PatternSpec {
                    regex,
                    accepts: text("accepts")?,
                    form: text("form")?,
                }
            }
            _ => return Err("must be a regular expression or an object with `regex`".to_string()),
        };
        spec.compile().map(|_| spec)
    }

    /// Compile the spec, anchoring every expression to the whole value.
    fn compile(&self) -> Result<Compiled, String> {
        let anchored = |regex: &str, what: &str| {
            Regex::new(&format!("^(?:{regex})$"))
                .map_err(|e| format!("{what} `{regex}` does not compile: {e}"))
        };
        Ok(Compiled {
            regex: anchored(&self.regex, "regex")?,
            accepts: match &self.accepts {
                Some(a) => Some(anchored(a, "accepts")?),
                None => None,
            },
            form: self.form.clone().unwrap_or_else(|| self.regex.clone()),
        })
    }
}

/// A compiled pattern: the full-match expression, the broader one, and
/// the spelling findings quote.
struct Compiled {
    regex: Regex,
    accepts: Option<Regex>,
    form: String,
}

/// How a string stands against a pattern.
enum Verdict {
    Matches,
    Accepted,
    Rejected,
}

impl Compiled {
    fn judge(&self, s: &str) -> Verdict {
        if self.regex.is_match(s) {
            Verdict::Matches
        } else if self.accepts.as_ref().is_some_and(|a| a.is_match(s)) {
            Verdict::Accepted
        } else {
            Verdict::Rejected
        }
    }
}

/// The pattern that governs a type, with the name findings call the
/// type by.
struct Governing {
    compiled: Rc<Compiled>,
    type_name: String,
}

/// One rule pass: the annotation index and the per-type memo.
struct Pass<'c> {
    config: &'c Config,
    /// Every type a `Pattern` annotation names (its `about` targets, or
    /// its owner when it names none), with the annotation.
    annotated: HashMap<ElementRef, ElementRef>,
    /// Patterns already resolved (or found absent) per declared type.
    memo: HashMap<ElementRef, Option<Rc<Governing>>>,
    /// Compiled annotations, by annotating usage.
    compiled: HashMap<ElementRef, Option<Rc<Compiled>>>,
    /// Findings on annotations themselves (a pattern that does not
    /// compile), reported after the sites.
    notes: Vec<Finding>,
}

pub(crate) fn literal_pattern(
    resolved: &mut ResolvedModel,
    config: &Config,
    out: &mut Vec<Finding>,
) {
    let cfg = config.cfg(RuleId::LiteralPattern);
    let mut pass = Pass {
        config,
        annotated: HashMap::new(),
        memo: HashMap::new(),
        compiled: HashMap::new(),
        notes: Vec::new(),
    };
    // Index the annotations once: every metadata usage typed by the
    // pattern definition, in any unit, names the types it governs.
    if let Some(def) = resolved.resolve_qualified(PATTERN_METADATA) {
        for usage in resolved.elements_of_metaclass("MetadataUsage") {
            if !resolved.typings(usage).contains(&def) {
                continue;
            }
            let mut targets = resolved.annotated_elements(usage);
            if targets.is_empty() {
                targets.extend(resolved.owner(usage));
            }
            for t in targets {
                pass.annotated.entry(t).or_insert(usage);
            }
        }
    }
    if pass.annotated.is_empty() && config.literal_patterns().is_empty() {
        return;
    }

    // Sites: user feature values, then the result expressions written in
    // the user units (calculation, constraint, requirement and invariant
    // bodies) — the value and every constructor or calculation argument
    // inside either.
    let users: BTreeSet<ElementRef> = resolved.user_elements().collect();
    let user_units: BTreeSet<usize> = users.iter().map(|&e| resolved.unit_of(e)).collect();
    let mut sources: Vec<(ElementRef, bool, usize, ScopeRef, Expr)> = Vec::new();
    for &e in &users {
        if let Some((scope, expr)) = resolved.value_expr(e) {
            sources.push((e, true, resolved.unit_of(e), scope, expr));
        }
    }
    for (owner, unit, scope, expr) in resolved.result_expression_sites(|u| user_units.contains(&u))
    {
        if users.contains(&owner) {
            sources.push((owner, false, unit, scope, expr));
        }
    }
    for (owner, is_value, unit, scope, expr) in sources {
        let severity = cfg.severity(resolved.element_type(owner));
        if severity == Severity::Off {
            continue;
        }
        let mut site = Site {
            pass: &mut pass,
            resolved,
            out,
            owner,
            unit,
            scope,
            severity,
        };
        if is_value {
            let tys = declared_types(site.resolved, owner);
            site.check(&tys, &expr);
        }
        let mut calls = Calls { out: Vec::new() };
        calls.visit_expr(&expr);
        for call in calls.out {
            match call {
                Call::Constructor(ty, args) => site.constructor(ty, args),
                Call::Invocation(ty, args) => site.invocation(ty, args),
            }
        }
    }
    out.append(&mut pass.notes);
}

/// The declared types a value bound to `e` must inhabit: its typings,
/// else those of the nearest features along its redefinition chain that
/// declare any.
fn declared_types(resolved: &mut ResolvedModel, e: ElementRef) -> Vec<ElementRef> {
    let mut frontier = vec![e];
    let mut seen = BTreeSet::new();
    while !frontier.is_empty() {
        let mut tys: Vec<ElementRef> = Vec::new();
        let mut next = Vec::new();
        for f in frontier {
            if !seen.insert(f) {
                continue;
            }
            for ty in resolved.typings(f) {
                if !tys.contains(&ty) {
                    tys.push(ty);
                }
            }
            next.extend(resolved.redefinition_targets(f));
        }
        if !tys.is_empty() {
            return tys;
        }
        frontier = next;
    }
    Vec::new()
}

enum Call<'a> {
    Constructor(&'a TargetRef, &'a [Arg]),
    Invocation(&'a TargetRef, &'a [Arg]),
}

/// Every constructor and invocation in an expression tree outside lambda
/// bodies, outermost first. A body's expressions bind through its own
/// parameters; evaluated in the site scope they would read whatever
/// those names mean outside.
struct Calls<'a> {
    out: Vec<Call<'a>>,
}

impl<'a> Visit<'a> for Calls<'a> {
    fn visit_expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Body { .. } => return,
            ExprKind::Constructor { ty, args } => self.out.push(Call::Constructor(ty, args)),
            ExprKind::Invocation { ty, args } => self.out.push(Call::Invocation(ty, args)),
            _ => {}
        }
        walk_expr(self, e);
    }
}

struct Site<'p, 'c, 'r, 'o> {
    pass: &'p mut Pass<'c>,
    resolved: &'r mut ResolvedModel,
    out: &'o mut Vec<Finding>,
    owner: ElementRef,
    unit: usize,
    scope: ScopeRef,
    severity: Severity,
}

impl Site<'_, '_, '_, '_> {
    /// Check `expr`, bound to a feature declaring `tys`, against the
    /// first governing pattern among them.
    fn check(&mut self, tys: &[ElementRef], expr: &Expr) {
        let Some(governing) = tys
            .iter()
            .find_map(|&t| self.pass.governing(self.resolved, t))
        else {
            return;
        };
        let Ok(value) = self.resolved.evaluate_in(self.scope, expr) else {
            return; // undecided, not wrong
        };
        let strings: Vec<&str> = match &value {
            Value::String(s) => vec![s.as_str()],
            Value::Sequence(items) => items
                .iter()
                .filter_map(|v| match v {
                    Value::String(s) => Some(s.as_str()),
                    _ => None,
                })
                .collect(),
            _ => return,
        };
        for s in strings {
            let (severity, message) = match governing.compiled.judge(s) {
                Verdict::Matches => continue,
                Verdict::Rejected => (
                    self.severity,
                    format!(
                        "`{s}` is not in the form of `{}`, `{}`",
                        governing.type_name, governing.compiled.form
                    ),
                ),
                Verdict::Accepted => {
                    let reduced = self.pass.config.literal_pattern_reduced();
                    if reduced == Severity::Off {
                        continue;
                    }
                    (
                        reduced,
                        format!(
                            "`{s}` is an accepted broader form of `{}`; the documented form is `{}`",
                            governing.type_name, governing.compiled.form
                        ),
                    )
                }
            };
            let mut f = finding(RuleId::LiteralPattern, severity, message);
            f.unit = Some(self.unit);
            f.span = Some(expr.span);
            f.element = edit_target(self.resolved, self.owner);
            self.out.push(f);
        }
    }

    /// A constructor's arguments, each against the feature it binds.
    fn constructor(&mut self, ty: &TargetRef, args: &[Arg]) {
        let TargetRef::Name(qn) = ty else {
            return;
        };
        let Some(elem) = self.resolved.resolve_in(self.scope, qn) else {
            return;
        };
        let sequence = self.resolved.constructor_features(elem);
        let mut positional = 0usize;
        for arg in args {
            let feature = match &arg.name {
                Some(name) => {
                    let name = name.to_display_string();
                    sequence.iter().find(|(n, _)| *n == name).map(|(_, e)| *e)
                }
                None => {
                    let at = positional;
                    positional += 1;
                    sequence.get(at).map(|(_, e)| *e)
                }
            };
            let Some(feature) = feature else {
                continue;
            };
            let tys = declared_types(self.resolved, feature);
            self.check(&tys, &arg.value);
        }
    }

    /// A calculation's arguments, each against the parameter it binds.
    fn invocation(&mut self, ty: &TargetRef, args: &[Arg]) {
        let TargetRef::Name(qn) = ty else {
            return;
        };
        let Some(callee) = self.resolved.resolve_in(self.scope, qn) else {
            return;
        };
        let Some(bindings) = self.resolved.calc_parameter_bindings(callee) else {
            return;
        };
        let mut positional = 0usize;
        for arg in args {
            let parameter = match &arg.name {
                Some(name) => {
                    let name = name.to_display_string();
                    bindings.iter().find(|p| p.name == name).map(|p| p.element)
                }
                None => {
                    let at = positional;
                    positional += 1;
                    bindings.get(at).map(|p| p.element)
                }
            };
            let Some(parameter) = parameter else {
                continue;
            };
            let tys = declared_types(self.resolved, parameter);
            self.check(&tys, &arg.value);
        }
    }
}

impl Pass<'_> {
    /// The pattern governing `ty`: configuration's entry for its
    /// qualified name, else the annotation on it, else the nearest one
    /// up its explicit supertypes (breadth-first). Memoized per type: a
    /// type the search passed through without finding anything at or
    /// above it is remembered as governed by nothing, and pruned from
    /// later searches without ending them.
    fn governing(&mut self, resolved: &mut ResolvedModel, ty: ElementRef) -> Option<Rc<Governing>> {
        if let Some(known) = self.memo.get(&ty) {
            return known.clone();
        }
        let configured = !self.config.literal_patterns().is_empty();
        let mut found = None;
        let mut queue = VecDeque::from([ty]);
        let mut seen = BTreeSet::new();
        let mut visited: Vec<ElementRef> = Vec::new();
        while let Some(t) = queue.pop_front() {
            if !seen.insert(t) {
                continue;
            }
            match self.memo.get(&t) {
                Some(Some(known)) => {
                    found = Some(Rc::clone(known));
                    break;
                }
                Some(None) => continue,
                None => {}
            }
            visited.push(t);
            let from_config = if configured {
                resolved
                    .element_qualified_name(t)
                    .and_then(|qn| self.config.literal_patterns().get(&qn))
                    .and_then(|spec| spec.compile().ok())
            } else {
                None
            };
            let compiled = match from_config {
                Some(c) => Some(Rc::new(c)),
                None => match self.annotated.get(&t).copied() {
                    Some(usage) => {
                        let type_name = type_name(resolved, t);
                        self.compiled_annotation(resolved, usage, &type_name)
                    }
                    None => None,
                },
            };
            if let Some(compiled) = compiled {
                found = Some(Rc::new(Governing {
                    compiled,
                    type_name: type_name(resolved, t),
                }));
                break;
            }
            queue.extend(resolved.explicit_supertypes(t));
        }
        if found.is_none() {
            // The whole closure was searched: nothing governs any type
            // the search passed through either.
            for t in visited {
                self.memo.insert(t, None);
            }
        }
        self.memo.insert(ty, found.clone());
        found
    }

    /// Compile the annotation `usage` once; a pattern that does not
    /// compile is noted where it is written, and governs nothing.
    fn compiled_annotation(
        &mut self,
        resolved: &mut ResolvedModel,
        usage: ElementRef,
        type_name: &str,
    ) -> Option<Rc<Compiled>> {
        if let Some(known) = self.compiled.get(&usage) {
            return known.clone();
        }
        let mut spec = PatternSpec {
            regex: String::new(),
            accepts: None,
            form: None,
        };
        let mut has_regex = false;
        for member in resolved.owned_members(usage) {
            let Some(name) = resolved.element_name(member).map(str::to_string) else {
                continue;
            };
            let Some((scope, expr)) = resolved.value_expr(member) else {
                continue;
            };
            let Ok(Value::String(text)) = resolved.evaluate_in(scope, &expr) else {
                continue;
            };
            match name.as_str() {
                "regex" => {
                    spec.regex = text;
                    has_regex = true;
                }
                "accepts" => spec.accepts = Some(text),
                "form" => spec.form = Some(text),
                _ => {}
            }
        }
        let compiled = if has_regex {
            match spec.compile() {
                Ok(c) => Some(Rc::new(c)),
                Err(e) => {
                    self.note_annotation(
                        resolved,
                        usage,
                        format!("the pattern on `{type_name}` {e}"),
                    );
                    None
                }
            }
        } else {
            self.note_annotation(
                resolved,
                usage,
                format!("the pattern on `{type_name}` names no `regex`"),
            );
            None
        };
        self.compiled.insert(usage, compiled.clone());
        compiled
    }

    /// A finding on the annotation itself, located where it is written.
    /// Library annotations are never linted: a library's own pattern that
    /// does not compile governs nothing, silently.
    fn note_annotation(
        &mut self,
        resolved: &mut ResolvedModel,
        usage: ElementRef,
        message: String,
    ) {
        if resolved.is_library_element(usage) {
            return;
        }
        let mut f = finding(RuleId::LiteralPattern, Severity::Warn, message);
        if let Some((unit, span)) = resolved.member_extent(usage) {
            f.unit = Some(unit);
            f.span = Some(span);
        }
        f.element = resolved.owner(usage).and_then(|o| edit_target(resolved, o));
        self.notes.push(f);
    }
}

/// The name findings call a type by: its declared name, else its
/// qualified name.
fn type_name(resolved: &mut ResolvedModel, t: ElementRef) -> String {
    resolved
        .element_name(t)
        .map(str::to_string)
        .or_else(|| resolved.element_qualified_name(t))
        .unwrap_or_else(|| "<anonymous>".to_string())
}
