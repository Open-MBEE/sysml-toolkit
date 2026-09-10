//! Extract / inline eligibility: the per-kind
//! usage-context → definition-context matrix, the conservative header
//! policy, and the provenance classification of a definition's incoming
//! references. Everything here answers *whether and why not* — the
//! relocation ops (extract / inline) consume these answers; nothing here plans
//! a splice.
//!
//! Two principles:
//!
//! - **Eligibility is an explicit matrix, not keyword-mechanical.** A
//!   `<keyword> def` counterpart is necessary but not sufficient: a view
//!   usage body admits `expose` while a view definition body does not,
//!   and an enumeration definition body is stricter than an enumeration
//!   usage body. V1 enables only the proven direct pairs (part, item,
//!   attribute, port); every other kind names its reason. The
//!   destination-context probe ([`probe_body_in_definition_context`])
//!   runs the real syntax checker, so the matrix cannot drift from it.
//! - **Every deferred header shape is a named refusal**, produced before
//!   any text is composed — never a late parse or semantic failure.

use std::collections::HashSet;

use sysmlv2_model::json::{ElementRef, RefSite};
use sysmlv2_syntax::ast::{Definition, FeatureSpecialization, MemberKind, Usage, UsageKind};
use sysmlv2_syntax::check;
use sysmlv2_syntax::lexer::tokenize;
use sysmlv2_syntax::parser::parse_source;
use sysmlv2_syntax::span::Span;
use sysmlv2_syntax::token::TokenKind;

use crate::Session;

/// One row of the per-kind matrix: the usage kind's textual definition
/// counterpart and whether v1 admits the pair.
#[derive(Clone, Copy, Debug)]
pub struct KindRule {
    /// The shared keyword (`part` — usages spell it alone, definitions
    /// spell `<keyword> def`).
    pub keyword: &'static str,
    /// Whether the pair is in the proven v1 set.
    pub enabled: bool,
    /// Why a disabled pair is disabled (verbatim in refusals).
    pub note: &'static str,
}

const fn enabled(keyword: &'static str) -> KindRule {
    KindRule {
        keyword,
        enabled: true,
        note: "",
    }
}

const fn gated(keyword: &'static str, note: &'static str) -> KindRule {
    KindRule {
        keyword,
        enabled: false,
        note,
    }
}

const NOT_YET_GATED: &str =
    "not in the v1 proven set (kinds are admitted as their header and body rules are gated)";

/// The matrix row for a usage kind, `None` when the kind has no textual
/// `<keyword> def` counterpart at all (bindings, successions, control
/// nodes, KerML feature kinds, …).
pub fn kind_rule(kind: UsageKind) -> Option<KindRule> {
    use UsageKind::*;
    Some(match kind {
        Part => enabled("part"),
        Item => enabled("item"),
        Attribute => enabled("attribute"),
        Port => enabled("port"),
        View => gated(
            "view",
            "a view usage body admits `expose`; a view definition body does not",
        ),
        Enum => gated(
            "enum",
            "an enumeration definition body admits only literals and annotations",
        ),
        Metadata => gated(
            "metadata",
            "metadata usage and definition bodies assign different contexts",
        ),
        Occurrence => gated("occurrence", NOT_YET_GATED),
        Connection => gated("connection", NOT_YET_GATED),
        Interface => gated("interface", NOT_YET_GATED),
        Allocation => gated("allocation", NOT_YET_GATED),
        Flow => gated("flow", NOT_YET_GATED),
        Rendering => gated("rendering", NOT_YET_GATED),
        Action => gated("action", NOT_YET_GATED),
        Calc => gated("calc", NOT_YET_GATED),
        State => gated("state", NOT_YET_GATED),
        Constraint => gated("constraint", NOT_YET_GATED),
        Requirement => gated("requirement", NOT_YET_GATED),
        Concern => gated("concern", NOT_YET_GATED),
        Viewpoint => gated("viewpoint", NOT_YET_GATED),
        Case => gated("case", NOT_YET_GATED),
        Analysis => gated("analysis", NOT_YET_GATED),
        Verification => gated("verification", NOT_YET_GATED),
        UseCase => gated("use case", NOT_YET_GATED),
        _ => return None,
    })
}

/// The matrix row keyed from the definition side (inline direction), by
/// abstract-syntax metaclass. Same rows as [`kind_rule`].
pub fn definition_kind_rule(metaclass: &str) -> Option<KindRule> {
    use UsageKind::*;
    let kind = match metaclass {
        "PartDefinition" => Part,
        "ItemDefinition" => Item,
        "AttributeDefinition" => Attribute,
        "PortDefinition" => Port,
        "ViewDefinition" => View,
        "EnumerationDefinition" => Enum,
        "MetadataDefinition" => Metadata,
        "OccurrenceDefinition" => Occurrence,
        "ConnectionDefinition" => Connection,
        "InterfaceDefinition" => Interface,
        "AllocationDefinition" => Allocation,
        "FlowDefinition" => Flow,
        "RenderingDefinition" => Rendering,
        "ActionDefinition" => Action,
        "CalculationDefinition" => Calc,
        "StateDefinition" => State,
        "ConstraintDefinition" => Constraint,
        "RequirementDefinition" => Requirement,
        "ConcernDefinition" => Concern,
        "ViewpointDefinition" => Viewpoint,
        "CaseDefinition" => Case,
        "AnalysisCaseDefinition" => Analysis,
        "VerificationCaseDefinition" => Verification,
        "UseCaseDefinition" => UseCase,
        _ => return None,
    };
    kind_rule(kind)
}

/// Why a usage cannot be extracted. Every deferred header shape is its
/// own reason, produced before any text is composed.
#[derive(Debug, Clone, PartialEq)]
pub enum ExtractRefusal {
    /// The element is not a member-declared usage.
    NotAUsage { metaclass: String },
    /// The element lives in a library unit (not editable).
    NotAUserElement,
    /// KerML units are out of v1's scope.
    UnsupportedDialect,
    /// The kind has no counterpart or its pair is not yet gated.
    UnsupportedKind {
        keyword: String,
        reason: &'static str,
    },
    /// `variation` usages and `variant` members carry membership
    /// semantics a mechanical move would change.
    VariationOrVariant,
    /// `individual` / `snapshot` / `timeslice` forms.
    OccurrenceForm,
    /// `#Meta` prefix metadata — where the annotation lands is a
    /// per-kind decision v1 does not make.
    PrefixMetadata,
    /// A `~P` typing cannot become a `:> ~P` specialization.
    ConjugatedTyping,
    /// A leading `then` is adjacency-sensitive; inserting a sibling
    /// definition immediately before it would change its succession source.
    LeadingSuccession,
    /// A generated specialization needs a resolved target expectation;
    /// an unresolved/ambiguous typing cannot supply one.
    UnresolvedTyping { spelling: String },
    /// Declared with `;` — nothing to extract.
    NoInlineBody,
    /// The body is illegal in the destination definition context (the
    /// probe's first diagnostic).
    BodyContext { first: String },
    /// The member text did not survive a standalone reparse (should not
    /// happen for resolver-recorded extents).
    Unparsable { message: String },
}

impl std::fmt::Display for ExtractRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractRefusal::NotAUsage { metaclass } => {
                write!(f, "not an extractable usage (metaclass {metaclass})")
            }
            ExtractRefusal::NotAUserElement => write!(f, "element lives in a library unit"),
            ExtractRefusal::UnsupportedDialect => {
                write!(f, "KerML units are not in the v1 extract scope")
            }
            ExtractRefusal::UnsupportedKind { keyword, reason } => {
                write!(f, "`{keyword}` usages are not extractable: {reason}")
            }
            ExtractRefusal::VariationOrVariant => {
                write!(f, "variation/variant forms are not extractable in v1")
            }
            ExtractRefusal::OccurrenceForm => write!(
                f,
                "individual/snapshot/timeslice forms are not extractable in v1"
            ),
            ExtractRefusal::PrefixMetadata => {
                write!(f, "prefix metadata placement is not decided in v1")
            }
            ExtractRefusal::ConjugatedTyping => write!(
                f,
                "a conjugated typing (`: ~P`) cannot become a definition specialization"
            ),
            ExtractRefusal::LeadingSuccession => write!(
                f,
                "a usage preceded by `then` cannot be extracted without changing succession adjacency"
            ),
            ExtractRefusal::UnresolvedTyping { spelling } => write!(
                f,
                "typing `{spelling}` does not resolve, so its generated specialization cannot be verified"
            ),
            ExtractRefusal::NoInlineBody => write!(f, "the usage has no inline body"),
            ExtractRefusal::BodyContext { first } => {
                write!(f, "the body is illegal in the definition context: {first}")
            }
            ExtractRefusal::Unparsable { message } => {
                write!(f, "member text does not reparse: {message}")
            }
        }
    }
}

/// A positive extract answer: where the moved region and the header
/// facts live. The extract composition starts from exactly this.
#[derive(Debug, Clone)]
pub struct ExtractEligibility {
    /// The shared keyword (`part` → `part def`).
    pub keyword: &'static str,
    /// Unit the usage is declared in.
    pub unit: usize,
    /// Interior of the inline body (between the braces, exclusive), in
    /// unit coordinates — the region extract moves byte-preserved.
    pub body_interior: Span,
    /// Written plain typing targets and their resolved qualified targets,
    /// in source order — the generated `:> A, B` carries one expectation
    /// per entry.
    pub plain_typings: Vec<PlainTyping>,
}

/// One extractable, non-conjugated typing and the identity its generated
/// definition specialization must resolve back to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlainTyping {
    pub spelling: String,
    pub target_qn: String,
}

/// Why a definition cannot be inlined into its usage.
#[derive(Debug, Clone, PartialEq)]
pub enum InlineRefusal {
    /// The element is not a definition of a matrix kind.
    NotADefinition { metaclass: String },
    /// The pair exists but is not yet gated.
    UnsupportedKind {
        keyword: &'static str,
        reason: &'static str,
    },
    /// The definition lives in a library unit and cannot be edited.
    NotAUserElement,
    /// KerML definitions are outside v1's relocation policy.
    UnsupportedDialect,
    /// A definition prefix/header flag has no specified inline transfer.
    UnsupportedHeader { reason: &'static str },
    /// The resolver-recorded definition extent did not reparse as a
    /// definition (an internal consistency failure).
    Unparsable { message: String },
    /// No usage is typed by the definition.
    NoTypingUsage,
    /// More than one usage is typed by the definition.
    MultipleTypingUsages { count: usize },
    /// The one typing is not a direct, non-conjugated FeatureTyping.
    NonPlainTyping { relationship: String },
    /// The typing site's owner chain does not reach a usage.
    TypingNotOnAUsage,
    /// A definition specialization target does not resolve, so the
    /// retargeted usage typing cannot carry an expectation.
    UnresolvedSpecialization { spelling: String },
    /// The definition and the usage both declare a member of the same
    /// effective name — v1 refuses rather than merge.
    MemberCollision { names: Vec<String> },
    /// References from outside the definition body and the sole usage —
    /// class (c) of the provenance rule; each entry names one site.
    OutsideReferences { sites: Vec<String> },
}

impl std::fmt::Display for InlineRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InlineRefusal::NotADefinition { metaclass } => {
                write!(f, "not an inlinable definition (metaclass {metaclass})")
            }
            InlineRefusal::UnsupportedKind { keyword, reason } => {
                write!(f, "`{keyword} def` is not inlinable: {reason}")
            }
            InlineRefusal::NotAUserElement => write!(f, "definition lives in a library unit"),
            InlineRefusal::UnsupportedDialect => {
                write!(f, "KerML units are not in the v1 inline scope")
            }
            InlineRefusal::UnsupportedHeader { reason } => {
                write!(f, "definition header is not inlinable in v1: {reason}")
            }
            InlineRefusal::Unparsable { message } => {
                write!(f, "definition text does not reparse: {message}")
            }
            InlineRefusal::NoTypingUsage => write!(f, "no usage is typed by the definition"),
            InlineRefusal::MultipleTypingUsages { count } => {
                write!(f, "{count} usages are typed by the definition")
            }
            InlineRefusal::NonPlainTyping { relationship } => {
                write!(
                    f,
                    "the typing is not a plain FeatureTyping ({relationship})"
                )
            }
            InlineRefusal::TypingNotOnAUsage => {
                write!(f, "the typing does not belong to a usage declaration")
            }
            InlineRefusal::UnresolvedSpecialization { spelling } => write!(
                f,
                "definition specialization `{spelling}` does not resolve, so the retargeted typing cannot be verified"
            ),
            InlineRefusal::MemberCollision { names } => write!(
                f,
                "the definition and the usage both declare: {}",
                names.join(", ")
            ),
            InlineRefusal::OutsideReferences { sites } => write!(
                f,
                "{} outside reference{} into the definition: {}",
                sites.len(),
                if sites.len() == 1 { "" } else { "s" },
                sites.join("; ")
            ),
        }
    }
}

/// A positive inline answer: the sole usage plus the incoming reference
/// sites classified by provenance — (a) internal to the moved body,
/// (b) reached through the usage. Class (c) refuses instead. Carries
/// the geometry and header facts the inline op composes from.
#[derive(Debug)]
pub struct InlineEligibility {
    pub definition: ElementRef,
    pub usage: ElementRef,
    /// Sites written inside the definition body — they move with it.
    pub internal_sites: Vec<RefSite>,
    /// Sites reached through the usage (`engine.mass` chains, and sites
    /// written inside the usage's own extent such as redefinitions) —
    /// they re-anchor through the correspondence map.
    pub through_usage_sites: Vec<RefSite>,
    /// Unit the definition is declared in.
    pub def_unit: usize,
    /// The definition's full member extent (the region inline deletes).
    pub def_extent: Span,
    /// Interior of the definition's body (between the braces,
    /// exclusive), in unit coordinates; `None` for a `;` declaration.
    pub body_interior: Option<Span>,
    /// The definition's plain `:>` targets — written spelling plus the
    /// resolved identity the retargeted usage typing must verify to.
    pub plain_specializations: Vec<PlainTyping>,
    /// The sole usage typing site (`: Engine` — its span is what the
    /// retarget rewrites or drops).
    pub typing_site: RefSite,
}

/// Validate a body interior in a destination definition context by
/// running the real parser + body-context checker over a probe
/// (`<keyword> def __X { <interior> }`). Returns diagnostic messages;
/// empty = legal. This is the mechanism that keeps the matrix honest —
/// `probe_body_in_definition_context("view", "expose P::*;")` fails
/// while the same body is legal on a view *usage*.
pub fn probe_body_in_definition_context(keyword: &str, interior: &str) -> Vec<String> {
    let probe = format!("{keyword} def __X {{{interior}}}");
    let parse = parse_source(&probe);
    if !parse.diagnostics.is_empty() {
        return parse
            .diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect();
    }
    check::validate(&parse.unit)
        .iter()
        .map(|d| d.message.clone())
        .collect()
}

/// Interior span of the trailing `{ … }` body of a member text, found by
/// token scan (comments and quoted names cannot fool it): the last
/// non-trivia token must be the closing brace; its matching opener is
/// found by depth counting backwards, which skips any `{ … }` inside
/// feature-value expressions. Relative to `text`.
pub(crate) fn body_interior(text: &str) -> Option<Span> {
    let (tokens, _) = tokenize(text);
    let toks: Vec<_> = tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .collect();
    let last = toks.last()?;
    if last.kind != TokenKind::RBrace {
        return None;
    }
    let mut depth = 0i32;
    for t in toks.iter().rev() {
        match t.kind {
            TokenKind::RBrace => depth += 1,
            TokenKind::LBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(Span::new(t.span.end, last.span.start));
                }
            }
            _ => {}
        }
    }
    None
}

const WRAP: &str = "package __p { ";

/// Reparse a member text in a neutral wrapper and hand back the usage
/// AST node plus its membership-level leading-succession flag (spans are
/// probe-relative; subtract [`WRAP`]'s length).
fn reparse_usage(text: &str) -> Result<(Usage, bool), ExtractRefusal> {
    let probe = format!("{WRAP}{text} }}");
    let parse = parse_source(&probe);
    if let Some(d) = parse.diagnostics.first() {
        return Err(ExtractRefusal::Unparsable {
            message: d.message.clone(),
        });
    }
    let member = match parse.unit.members.first().map(|m| &m.kind) {
        Some(MemberKind::Package(p)) => p.body.as_ref().and_then(|ms| ms.first()).cloned(),
        _ => None,
    };
    match member {
        Some(m) => match m.kind {
            MemberKind::Usage(u) => Ok((u, m.leading_then)),
            other => Err(ExtractRefusal::NotAUsage {
                metaclass: format!("{other:?}")
                    .split('(')
                    .next()
                    .unwrap_or("?")
                    .to_string(),
            }),
        },
        None => Err(ExtractRefusal::NotAUsage {
            metaclass: "<none>".to_string(),
        }),
    }
}

/// Reparse a definition member in the same neutral wrapper used by the
/// extract side. Inline needs the syntax header because not every semantic
/// flag has a dedicated navigation accessor and the source is authoritative.
fn reparse_definition(text: &str) -> Result<Definition, InlineRefusal> {
    let probe = format!("{WRAP}{text} }}");
    let parse = parse_source(&probe);
    if let Some(d) = parse.diagnostics.first() {
        return Err(InlineRefusal::Unparsable {
            message: d.message.clone(),
        });
    }
    let member = match parse.unit.members.first().map(|m| &m.kind) {
        Some(MemberKind::Package(p)) => p.body.as_ref().and_then(|ms| ms.first()).cloned(),
        _ => None,
    };
    match member.map(|m| m.kind) {
        Some(MemberKind::Definition(d)) => Ok(d),
        other => Err(InlineRefusal::NotADefinition {
            metaclass: match other {
                Some(k) => format!("{k:?}")
                    .split('(')
                    .next()
                    .unwrap_or("?")
                    .to_string(),
                None => "<none>".to_string(),
            },
        }),
    }
}

impl Session {
    /// M29a0 extract gate: may `usage` be extracted into a definition,
    /// and if so where is the moved region? Refusals are named header /
    /// kind / context policies — never a late failure downstream.
    pub fn extract_definition_eligibility(
        &mut self,
        usage: ElementRef,
    ) -> Result<ExtractEligibility, ExtractRefusal> {
        let metaclass = self.resolved.element_type(usage).to_string();
        let (unit, extent) =
            self.resolved
                .member_extent(usage)
                .ok_or_else(|| ExtractRefusal::NotAUsage {
                    metaclass: metaclass.clone(),
                })?;
        if unit < self.unit_offset {
            return Err(ExtractRefusal::NotAUserElement);
        }
        let local = unit - self.unit_offset;
        if self.sources[local].0.ends_with(".kerml") {
            return Err(ExtractRefusal::UnsupportedDialect);
        }
        if !metaclass.ends_with("Usage") {
            return Err(ExtractRefusal::NotAUsage { metaclass });
        }
        let text = crate::slice(&self.sources[local].1, extent).to_string();
        let (u, leading_then) = reparse_usage(&text)?;

        // Kind gate first: the matrix names the pair or its absence.
        let rule = kind_rule(u.kind).ok_or_else(|| ExtractRefusal::UnsupportedKind {
            keyword: format!("{:?}", u.kind).to_lowercase(),
            reason: "no textual definition counterpart",
        })?;
        if !rule.enabled {
            return Err(ExtractRefusal::UnsupportedKind {
                keyword: rule.keyword.to_string(),
                reason: rule.note,
            });
        }
        // Header policy: refuse what cannot move mechanically.
        let p = &u.prefix;
        if p.is_variation || p.is_variant {
            return Err(ExtractRefusal::VariationOrVariant);
        }
        if p.is_individual || p.portion.is_some() {
            return Err(ExtractRefusal::OccurrenceForm);
        }
        if !p.metadata.is_empty() {
            return Err(ExtractRefusal::PrefixMetadata);
        }
        if leading_then {
            return Err(ExtractRefusal::LeadingSuccession);
        }
        let reference_sites = self.resolved.reference_sites().to_vec();
        let mut plain_typings = Vec::new();
        for s in &u.declaration.specializations {
            if let FeatureSpecialization::TypedBy(entries) = s {
                for t in entries {
                    if t.is_conjugated {
                        return Err(ExtractRefusal::ConjugatedTyping);
                    }
                    let sp = t.target.span();
                    let (start, end) = (
                        (sp.start as usize).saturating_sub(WRAP.len()),
                        (sp.end as usize).saturating_sub(WRAP.len()),
                    );
                    let spelling = text.get(start..end).unwrap_or("?").to_string();
                    let absolute =
                        Span::new(extent.start + start as u32, extent.start + end as u32);
                    let target = reference_sites
                        .iter()
                        .find(|site| {
                            site.unit == unit && site.kind == "type" && site.span == absolute
                        })
                        .map(|site| site.target)
                        .ok_or_else(|| ExtractRefusal::UnresolvedTyping {
                            spelling: spelling.clone(),
                        })?;
                    let target_qn =
                        self.resolved
                            .element_qualified_name(target)
                            .ok_or_else(|| ExtractRefusal::UnresolvedTyping {
                                spelling: spelling.clone(),
                            })?;
                    plain_typings.push(PlainTyping {
                        spelling,
                        target_qn,
                    });
                }
            }
        }
        if u.body.is_none() {
            return Err(ExtractRefusal::NoInlineBody);
        }
        let interior = body_interior(&text).ok_or(ExtractRefusal::NoInlineBody)?;
        // Destination-context probe over the real checker.
        let interior_text = &text[interior.start as usize..interior.end as usize];
        if let Some(first) = probe_body_in_definition_context(rule.keyword, interior_text)
            .into_iter()
            .next()
        {
            return Err(ExtractRefusal::BodyContext { first });
        }
        Ok(ExtractEligibility {
            keyword: rule.keyword,
            unit,
            body_interior: Span::new(extent.start + interior.start, extent.start + interior.end),
            plain_typings,
        })
    }

    /// M29a0 inline gate: has `definition` exactly one direct,
    /// non-conjugated typing usage, and does every other incoming
    /// reference classify as (a) internal to the body being moved or
    /// (b) reached through that usage? Class (c) — genuine outside
    /// references through the definition — refuses, naming each site.
    pub fn inline_definition_eligibility(
        &mut self,
        definition: ElementRef,
    ) -> Result<InlineEligibility, InlineRefusal> {
        let metaclass = self.resolved.element_type(definition).to_string();
        let (def_unit, def_extent) = self.resolved.member_extent(definition).ok_or_else(|| {
            InlineRefusal::NotADefinition {
                metaclass: metaclass.clone(),
            }
        })?;
        if def_unit < self.unit_offset {
            return Err(InlineRefusal::NotAUserElement);
        }
        let def_local = def_unit - self.unit_offset;
        if self.sources[def_local].0.ends_with(".kerml") {
            return Err(InlineRefusal::UnsupportedDialect);
        }
        let rule = definition_kind_rule(&metaclass).ok_or(InlineRefusal::NotADefinition {
            metaclass: metaclass.clone(),
        })?;
        if !rule.enabled {
            return Err(InlineRefusal::UnsupportedKind {
                keyword: rule.keyword,
                reason: rule.note,
            });
        }
        let def_text = crate::slice(&self.sources[def_local].1, def_extent).to_string();
        let d = reparse_definition(&def_text)?;
        if d.prefix.is_abstract {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "`abstract` has no usage-side transfer rule",
            });
        }
        if d.prefix.is_variation {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "`variation` has no usage-side transfer rule",
            });
        }
        if d.prefix.is_individual {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "`individual` has no usage-side transfer rule",
            });
        }
        if !d.prefix.metadata.is_empty() {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "prefix metadata placement is not decided",
            });
        }
        if d.is_parallel {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "`parallel` has no usage-side transfer rule",
            });
        }
        if d.is_sufficient
            || d.multiplicity.is_some()
            || !d.conjugates.is_empty()
            || !d.disjoint_from.is_empty()
            || !d.unions.is_empty()
            || !d.intersects.is_empty()
            || !d.differences.is_empty()
        {
            return Err(InlineRefusal::UnsupportedHeader {
                reason: "KerML type relationships have no v1 transfer rule",
            });
        }

        // The definition's plain `:>` targets, each resolved to the
        // identity the retargeted usage typing must verify to.
        let all_sites = self.resolved.reference_sites().to_vec();
        let mut plain_specializations = Vec::new();
        for target in &d.specializes {
            let sp = target.span();
            let (start, end) = (
                (sp.start as usize).saturating_sub(WRAP.len()),
                (sp.end as usize).saturating_sub(WRAP.len()),
            );
            let spelling = def_text.get(start..end).unwrap_or("?").to_string();
            let absolute = Span::new(
                def_extent.start + start as u32,
                def_extent.start + end as u32,
            );
            // Qualifier sites share the full qualified-name span with
            // the site they prefix — only the real site's name_span
            // ends where the spelling ends.
            let resolved_target = all_sites
                .iter()
                .find(|site| {
                    site.unit == def_unit
                        && site.span == absolute
                        && site.kind != "qualifier"
                        && site.name_span.end == absolute.end
                })
                .map(|site| site.target)
                .ok_or_else(|| InlineRefusal::UnresolvedSpecialization {
                    spelling: spelling.clone(),
                })?;
            let target_qn = self
                .resolved
                .element_qualified_name(resolved_target)
                .ok_or_else(|| InlineRefusal::UnresolvedSpecialization {
                    spelling: spelling.clone(),
                })?;
            plain_specializations.push(PlainTyping {
                spelling,
                target_qn,
            });
        }
        // The body interior (unit coordinates), `None` for `;` forms.
        let interior = body_interior(&def_text)
            .map(|s| Span::new(def_extent.start + s.start, def_extent.start + s.end));

        // The definition subtree: every element the move carries.
        let mut subtree: HashSet<ElementRef> = HashSet::new();
        let mut stack = vec![definition];
        while let Some(e) = stack.pop() {
            if subtree.insert(e) {
                stack.extend(self.resolved.owned_members(e));
            }
        }

        let inside = |s: &RefSite, unit: usize, extent: Span| {
            s.unit == unit && s.name_span.start >= extent.start && s.name_span.end <= extent.end
        };
        let mut internal = Vec::new();
        let mut typing_sites = Vec::new();
        let mut rest = Vec::new();
        for s in all_sites.iter().cloned() {
            if !subtree.contains(&s.target) {
                continue;
            }
            if inside(&s, def_unit, def_extent) {
                internal.push(s);
            } else if s.target == definition && s.kind == "type" {
                typing_sites.push(s);
            } else {
                rest.push(s);
            }
        }
        match typing_sites.len() {
            0 => return Err(InlineRefusal::NoTypingUsage),
            1 => {}
            n => return Err(InlineRefusal::MultipleTypingUsages { count: n }),
        }
        let typing = &typing_sites[0];
        let rel = self.resolved.element_type(typing.owner);
        if rel != "FeatureTyping" {
            return Err(InlineRefusal::NonPlainTyping {
                relationship: rel.to_string(),
            });
        }
        // The sole usage: the first owner-chain element that is a usage.
        let mut usage = None;
        let mut cur = Some(typing.owner);
        while let Some(c) = cur {
            if self.resolved.element_type(c).ends_with("Usage") {
                usage = Some(c);
                break;
            }
            cur = self.resolved.owner(c);
        }
        let usage = usage.ok_or(InlineRefusal::TypingNotOnAUsage)?;

        // Only sites whose WRITTEN SPELLING traverses the definition's
        // name die with it. A reference's qualifier companions share its
        // full span, so the refused spellings are exactly the spans
        // where some site targets the definition — `Engine::mass` dies
        // (its qualifier names Engine), `Pkg::usage::member` survives
        // (the usage keeps its name; the member moves under it), and
        // simple spellings or chain steps (`engine.mass`, a subject's
        // `:>> engine`, an interface end's step) re-anchor through
        // scopes the move preserves. The commit pipeline verifies every
        // admitted site: mapped step-1 expectations, the strict
        // unresolved/validation nets, and the projection.
        let mut def_spelling_spans: HashSet<(usize, u32, u32)> = HashSet::new();
        for s in &all_sites {
            if s.target == definition {
                def_spelling_spans.insert((s.unit, s.span.start, s.span.end));
            }
        }
        let typing = &typing_sites[0];
        def_spelling_spans.remove(&(typing.unit, typing.span.start, typing.span.end));

        let mut through = Vec::new();
        let mut outside = Vec::new();
        for s in rest {
            let dies_with_the_name = s.target == definition
                || def_spelling_spans.contains(&(s.unit, s.span.start, s.span.end));
            if !dies_with_the_name {
                through.push(s);
                continue;
            }
            let local = s.unit.checked_sub(self.unit_offset);
            let spelled = local
                .and_then(|l| self.sources.get(l))
                .and_then(|(_, t)| t.get(s.span.start as usize..s.span.end as usize))
                .unwrap_or("?");
            let name = local
                .and_then(|l| self.sources.get(l))
                .map(|(n, _)| n.as_str())
                .unwrap_or("<library>");
            outside.push(format!(
                "`{spelled}` in {name} (bytes {}..{})",
                s.span.start, s.span.end
            ));
        }
        if !outside.is_empty() {
            outside.sort();
            return Err(InlineRefusal::OutsideReferences { sites: outside });
        }
        // Member-name collisions between the merged regions refuse with
        // the colliding names listed — v1 never attempts a merge policy.
        let usage_names: HashSet<String> = self
            .resolved
            .owned_members(usage)
            .into_iter()
            .filter_map(|m| self.resolved.element_effective_name(m))
            .collect();
        let mut collisions: Vec<String> = self
            .resolved
            .owned_members(definition)
            .into_iter()
            .filter_map(|m| self.resolved.element_effective_name(m))
            .filter(|n| usage_names.contains(n))
            .collect();
        if !collisions.is_empty() {
            collisions.sort();
            collisions.dedup();
            return Err(InlineRefusal::MemberCollision { names: collisions });
        }
        Ok(InlineEligibility {
            definition,
            usage,
            internal_sites: internal,
            through_usage_sites: through,
            def_unit,
            def_extent,
            body_interior: interior,
            plain_specializations,
            typing_site: typing_sites.into_iter().next().expect("checked above"),
        })
    }
}
