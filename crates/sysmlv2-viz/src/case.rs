//! Case view, the Pilot's CASE mode as a proper use-case
//! diagram: case-family definitions and usages as `usecase` nodes,
//! actor members as `actor` nodes with association edges, subject
//! members as `<<subject>>` rectangles, objectives as attached notes,
//! and `include use case` references as `«include»` edges.
//!
//! Everything else — packages, parts, non-case definitions — is a
//! transparent container: a use case def in a package or a case usage
//! inside a part is found wherever it lives. Nested case members
//! (`use case def X { use case y; }`) render flat under a composition
//! edge (`usecase` cannot nest in PlantUML).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::{
    VizOptions, escape, frame, inline_label, link_suffix, note_text, stereo_text, stereotype,
    style_header, usage_label,
};

/// Case-family node metaclasses.
const CASES: &[&str] = &[
    "UseCaseDefinition",
    "UseCaseUsage",
    "CaseDefinition",
    "CaseUsage",
    "AnalysisCaseDefinition",
    "AnalysisCaseUsage",
    "VerificationCaseDefinition",
    "VerificationCaseUsage",
    "IncludeUseCaseUsage",
];

pub(crate) fn emit(r: &mut ResolvedModel, tops: &[ElementRef], opts: &VizOptions) -> String {
    let mut em = Emitter {
        r,
        opts,
        alias: HashMap::new(),
        drawn: HashSet::new(),
        body: String::new(),
        edges: String::new(),
        notes: 0,
    };
    for &e in tops {
        em.collect(e);
    }
    let Emitter {
        r,
        alias,
        body,
        mut edges,
        ..
    } = em;
    crate::emit_notes(r, opts, &alias, &mut edges);
    let header = style_header(opts, &["usecase", "rectangle"]);
    frame(opts, &header, &body, &edges)
}

struct Emitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    alias: HashMap<ElementRef, String>,
    /// Every element whose node line is already in `body`.
    drawn: HashSet<ElementRef>,
    body: String,
    edges: String,
    /// Objective-note counter (`o1…` — disjoint from node aliases and
    /// the shared comment notes `c1…`).
    notes: usize,
}

impl Emitter<'_> {
    fn alias_for(&mut self, e: ElementRef) -> String {
        if let Some(a) = self.alias.get(&e) {
            return a.clone();
        }
        let a = format!("n{}", self.alias.len() + 1);
        self.alias.insert(e, a.clone());
        a
    }

    /// Top-down search through transparent containers.
    fn collect(&mut self, e: ElementRef) {
        if CASES.contains(&self.r.element_type(e)) {
            self.render_case(e);
            return;
        }
        for m in self.r.owned_members(e) {
            self.collect(m);
        }
    }

    fn render_case(&mut self, e: ElementRef) {
        let ty = self.r.element_type(e);
        // An `include use case` that references another case is pure
        // edge; an inline one (`include use case z { … }`) is a case of
        // its own.
        if ty == "IncludeUseCaseUsage" {
            let refs = self.r.referenced_features(e);
            if let Some(target) = refs.first().and_then(|chain| chain.last().copied()) {
                if let Some(owner_alias) = self.r.owner(e).and_then(|o| self.alias.get(&o).cloned())
                {
                    let target_alias = self.alias_for(target);
                    let _ = writeln!(self.edges, "{owner_alias} ..> {target_alias} : «include»");
                    // The target renders on its own when reached; a
                    // forward reference draws the node lazily here.
                    self.ensure_case_node(target);
                }
                return;
            }
        }

        let alias = self.alias_for(e);
        self.emit_case_node(e, &alias);

        for m in self.r.owned_members(e) {
            let mty = self.r.element_type(m);
            match self.r.owning_membership_type(m) {
                Some("ActorMembership") => self.render_actor(m, &alias),
                Some("SubjectMembership") => self.render_subject(m, &alias),
                Some("ObjectiveMembership") => self.render_objective(m, &alias),
                _ if CASES.contains(&mty) => {
                    self.render_case(m);
                    if mty != "IncludeUseCaseUsage" {
                        if let Some(child) = self.alias.get(&m).cloned() {
                            let _ = writeln!(self.edges, "{alias} *-- {child}");
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// The `usecase` node line for a case element, once — an element
    /// reached both through an `«include»` reference and through the
    /// containment walk keeps the single declaration it already has.
    fn emit_case_node(&mut self, e: ElementRef, alias: &str) {
        if !self.drawn.insert(e) {
            return;
        }
        let ty = self.r.element_type(e);
        let stereo = stereotype(ty);
        let label = if ty.ends_with("Definition") {
            self.r.element_name(e).unwrap_or("").to_string()
        } else {
            usage_label(self.r, e)
        };
        let label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };
        let stereos = stereo_text(self.r, self.opts, e, &stereo);
        let link = link_suffix(self.r, self.opts, e);
        let _ = writeln!(
            self.body,
            "usecase \"{}\" as {alias} {stereos}{link}",
            escape(&label)
        );
    }

    /// A case referenced before (or without) its own traversal still
    /// gets a node.
    fn ensure_case_node(&mut self, e: ElementRef) {
        if self.drawn.contains(&e) || !CASES.contains(&self.r.element_type(e)) {
            return;
        }
        let alias = self.alias_for(e);
        self.emit_case_node(e, &alias);
    }

    fn render_actor(&mut self, m: ElementRef, case_alias: &str) {
        let alias = self.alias_for(m);
        let label = usage_label(self.r, m);
        let label = if label.trim().is_empty() {
            "(actor)".to_string()
        } else {
            label
        };
        let link = link_suffix(self.r, self.opts, m);
        let _ = writeln!(self.body, "actor \"{}\" as {alias}{link}", escape(&label));
        let _ = writeln!(self.edges, "{alias} -- {case_alias}");
    }

    fn render_subject(&mut self, m: ElementRef, case_alias: &str) {
        let alias = self.alias_for(m);
        let label = usage_label(self.r, m);
        let label = if label.trim().is_empty() {
            "(subject)".to_string()
        } else {
            label
        };
        let link = link_suffix(self.r, self.opts, m);
        let _ = writeln!(
            self.body,
            "rectangle \"{}\" as {alias} <<subject>>{link}",
            escape(&label)
        );
        let _ = writeln!(self.edges, "{case_alias} -- {alias} : «subject»");
    }

    /// The objective requirement, as a note pinned to the case — its
    /// doc bodies say what the objective *is*, so they join the note.
    fn render_objective(&mut self, m: ElementRef, case_alias: &str) {
        let label = usage_label(self.r, m);
        let bodies: Vec<String> = self
            .r
            .annotation_bodies()
            .into_iter()
            .filter(|(t, _)| *t == m)
            .map(|(_, b)| b)
            .collect();
        self.notes += 1;
        let k = self.notes;
        let header = if label.trim().is_empty() {
            "«objective»".to_string()
        } else {
            format!("«objective» {}", inline_label(&label))
        };
        let mut text = escape(&header);
        for b in bodies {
            text.push_str("\\n");
            text.push_str(&note_text(&b));
        }
        let _ = writeln!(self.edges, "note \"{text}\" as o{k}");
        let _ = writeln!(self.edges, "o{k} .. {case_alias}");
    }
}
