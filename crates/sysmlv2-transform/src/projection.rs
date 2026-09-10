//! Effective-member projection: the authoritative
//! structural-identity gate for the relocation ops.
//!
//! Under the correspondence map, extract/inline must leave the touched
//! usage's *effective* members structurally identical — member
//! metaclasses and order, relationship targets, multiplicities,
//! visibility, value bodies, and the resolved targets referenced from
//! values. The one delta the ops intend — owned members becoming
//! inherited (or back) and the fresh/deleted definition itself — is
//! exactly what this projection is blind to: rows never say where a
//! member came from.
//!
//! Evaluated values / verify verdicts stay a valuable corpus gate, but
//! equal `unbound`/`undecided` results prove nothing; this projection
//! is the comparison made authoritative.
//!
//! The engine lives on [`Projector`], which borrows any resolved model
//! plus its sources — the commit pipeline projects the *prospective*
//! state (rebuilt but not yet swapped in) exactly like the session's
//! own; [`Session::effective_member_projection`] is the public wrapper.

use std::collections::{HashMap, HashSet};

use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::Session;

/// A projection engine over one resolved model and its source texts —
/// either a session's current state or a commit's prospective state.
pub(crate) struct Projector<'a> {
    pub resolved: &'a mut ResolvedModel,
    pub sources: &'a [(String, String)],
    pub unit_offset: usize,
}

impl Session {
    /// One normalized row per effective member of `e` — its own owned
    /// members plus members inherited through typings and explicit
    /// specializations of **user** elements (library bases contribute
    /// identically on both sides of a relocation and are skipped),
    /// breadth-first, own members first, name-shadowed once. Rows
    /// recurse into nested members with a `parent::` prefix. Qualified
    /// names in rows pass through `map_qn` — hand the commit's
    /// correspondence mapping in to compare across a relocation.
    pub fn effective_member_projection(
        &mut self,
        e: ElementRef,
        map_qn: &dyn Fn(&str) -> String,
    ) -> Vec<String> {
        Projector {
            resolved: &mut self.resolved,
            sources: &self.sources,
            unit_offset: self.unit_offset,
        }
        .project(e, map_qn)
    }
}

impl Projector<'_> {
    pub(crate) fn project(
        &mut self,
        e: ElementRef,
        map_qn: &dyn Fn(&str) -> String,
    ) -> Vec<String> {
        let mut rows = Vec::new();
        let mut path = HashSet::new();
        self.project_members(e, map_qn, "", &mut path, &mut rows);
        rows
    }

    fn project_members(
        &mut self,
        e: ElementRef,
        map_qn: &dyn Fn(&str) -> String,
        prefix: &str,
        path: &mut HashSet<ElementRef>,
        rows: &mut Vec<String>,
    ) {
        if !path.insert(e) {
            return;
        }
        // The user-element base closure: `e` first (its own members take
        // precedence), then typings and explicit specializations,
        // breadth-first.
        let mut layers = vec![e];
        let mut i = 0;
        while i < layers.len() {
            let cur = layers[i];
            i += 1;
            let bases: Vec<ElementRef> = self
                .resolved
                .typings(cur)
                .into_iter()
                .chain(self.resolved.explicit_supertypes(cur))
                .collect();
            for b in bases {
                if !self.resolved.is_library_element(b) && !layers.contains(&b) {
                    layers.push(b);
                }
            }
        }
        // Effective names shadow only like-metaclass members here. SysML
        // permits distinguishable same-named metaclasses in one namespace;
        // collapsing solely by spelling would hide one of them. Anonymous
        // members do not shadow, but must project on inherited layers too:
        // extract moves docs/comments and unnamed redefinitions from the
        // usage's own layer to its fresh definition's inherited layer.
        //
        // Row order is emission order (nearest layer first) and is NOT
        // stable across the owned↔inherited edge — a retained
        // multiplicity's anonymous member precedes body members before
        // an extract but follows inherited members after it, and inline
        // places definition members ahead of the usage's own. The
        // commit-time comparison therefore treats rows as a multiset;
        // each row's own content is the identity that matters.
        let mut seen: HashSet<(String, &'static str)> = HashSet::new();
        let mut anonymous_ordinals: HashMap<&'static str, usize> = HashMap::new();
        for base in layers {
            for m in self.resolved.owned_members(base) {
                let metaclass = self.resolved.element_type(m);
                let name = self.resolved.element_effective_name(m);
                if name
                    .as_ref()
                    .is_some_and(|n| !seen.insert((n.clone(), metaclass)))
                {
                    continue; // shadowed by a nearer member
                }
                let label = name.unwrap_or_else(|| {
                    let ordinal = anonymous_ordinals.entry(metaclass).or_default();
                    let label = format!("«{metaclass}#{ordinal}»");
                    *ordinal += 1;
                    label
                });
                rows.push(self.member_row(m, &label, map_qn, prefix));
                self.project_members(m, map_qn, &format!("{prefix}{label}::"), path, rows);
            }
        }
        path.remove(&e);
    }

    fn member_row(
        &mut self,
        m: ElementRef,
        label: &str,
        map_qn: &dyn Fn(&str) -> String,
        prefix: &str,
    ) -> String {
        let metaclass = self.resolved.element_type(m);
        let spell = |targets: Vec<ElementRef>,
                     resolved: &mut dyn FnMut(ElementRef) -> Option<String>| {
            targets
                .into_iter()
                .map(|t| resolved(t).map_or_else(|| "<anonymous>".to_string(), |qn| map_qn(&qn)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let typings = self.resolved.typings(m);
        let typs = spell(typings, &mut |t| self.resolved.element_qualified_name(t));
        let supers = self.resolved.explicit_supertypes(m);
        let sups = spell(supers, &mut |t| self.resolved.element_qualified_name(t));
        let specializations = self.resolved.explicit_specializations(m);
        let specs = specializations
            .into_iter()
            .map(|(kind, target)| {
                let target = self
                    .resolved
                    .element_qualified_name(target)
                    .map_or_else(|| "<anonymous>".to_string(), |qn| map_qn(&qn));
                format!("{kind}->{target}")
            })
            .collect::<Vec<_>>()
            .join(", ");
        let mult = match self.resolved.declared_multiplicity(m) {
            Some((lo, hi)) => format!("{lo}..{hi}"),
            None => "-".to_string(),
        };
        let vis = self
            .resolved
            .member_visibility(m)
            .unwrap_or("public")
            .to_string();
        // Value body: normalized source text plus the resolved targets
        // referenced from inside it (mapped) — "every resolved reference
        // target" without depending on spellings.
        let (val, refs) = match self.resolved.value_expr(m) {
            Some((_, expr)) => {
                let text = self
                    .resolved
                    .member_extent(m)
                    .and_then(|(unit, _)| {
                        let local = unit.checked_sub(self.unit_offset)?;
                        let src = &self.sources.get(local)?.1;
                        src.get(expr.span.start as usize..expr.span.end as usize)
                    })
                    .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
                    .unwrap_or_else(|| "?".to_string());
                let unit = self.resolved.member_extent(m).map(|(u, _)| u);
                let mut targets: Vec<String> = self
                    .resolved
                    .reference_sites()
                    .iter()
                    .filter(|s| {
                        Some(s.unit) == unit
                            && s.name_span.start >= expr.span.start
                            && s.name_span.end <= expr.span.end
                    })
                    .map(|s| s.target)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .map(|t| {
                        self.resolved
                            .element_qualified_name(t)
                            .map_or_else(|| "<anonymous>".to_string(), |qn| map_qn(&qn))
                    })
                    .collect();
                targets.sort();
                targets.dedup();
                (text, targets.join(", "))
            }
            None => ("-".to_string(), String::new()),
        };
        format!(
            "{prefix}{label} <{metaclass}> : [{typs}] :> [{sups}] specs=[{specs}] mult={mult} vis={vis} = {val} refs=[{refs}]"
        )
    }
}
