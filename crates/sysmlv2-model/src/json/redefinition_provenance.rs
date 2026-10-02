//! Read-side provenance for explicit redefinition headers.
use super::provider_completeness::ProviderCompleteness;
use super::{LookupAccess, LookupResult, RefSite, ResolvedModel, recorded_lookup};
use std::collections::HashMap;

impl ResolvedModel {
    /// Unqualified explicit redefinitions that resolve through an enclosing
    /// namespace rather than within the selected direct general's members.
    /// Each result contains the reference site and its unqualified spelling.
    ///
    /// This is an authoring heuristic, not a language validation error.
    /// Only owners with recorded explicit general contexts are considered.
    /// Qualified, unresolved, identity-spelled and incomplete contexts are
    /// omitted. Selection follows header base order and preserves imported and
    /// aliased members of the general itself. Import provenance is recomputed,
    /// so library-cache replay does not change the result. Filters, recursive
    /// imports, chained bases, cycles and exhausted proof budgets conservatively
    /// suppress findings; exact member imports do not require unrelated providers.
    pub fn redefinitions_outside_inheritance(&mut self) -> Vec<(RefSite, String)> {
        let b = &mut self.b;
        if !b.recorded_lookup_ready || b.recorded_lookup_incomplete {
            return Vec::new();
        }
        let sites: HashMap<_, _> = b
            .ref_sites
            .iter()
            .filter(|s| s.kind == "redefinedFeature" && s.plain)
            .filter_map(|s| Some(((s.exclude?.0, s.span.start, s.span.end), s.clone())))
            .collect();
        let candidates: Vec<_> = b
            .spec_targets
            .iter()
            .filter(|(e, kind, _, qn)| {
                *e >= b.lib_boundary
                    && *kind == "Redefinition"
                    && !qn.is_global
                    && qn.segments.len() == 1
            })
            .filter_map(|(e, _, _, qn)| {
                sites
                    .get(&(*e, qn.span.start, qn.span.end))
                    .map(|s| (*e, qn.clone(), s.clone()))
            })
            .collect();
        if candidates.is_empty() {
            return Vec::new();
        }
        if b.recorded_lookup_graph.is_none() {
            b.recorded_lookup_graph = Some(recorded_lookup::Graph::build(b));
        }
        // Queries may fill memo tables, but must not alter import-use or
        // caller lookup context. Do not use visibility-probing mode: it
        // deliberately widens access, which would misclassify private names.
        let saved = (
            b.exclude,
            b.declared_only,
            b.redefinition_lookup_owner,
            b.redefinition_lookup_base,
            b.recorded_lookup_suppressed,
            b.identity_origin_unit,
        );
        let used = b.used_imports.clone();
        let imports = b.query_imports.clone();
        let misses = b.current_misses.clone();
        let roots = b.root_misses.clone();
        let mut out = Vec::new();
        let mut completeness = ProviderCompleteness::default();
        let mut proof_steps = 0;
        for (feature, qn, site) in candidates {
            b.exclude = None;
            b.declared_only = false;
            b.redefinition_lookup_owner = None;
            b.redefinition_lookup_base = None;
            b.recorded_lookup_suppressed = false;
            b.identity_origin_unit = Some(site.unit);
            let Some(owner) = b.owner_elem(feature) else {
                continue;
            };
            let Some(&scope) = b.elem_scope.get(&owner) else {
                continue;
            };
            let Some(bases) = b
                .recorded_lookup_graph
                .as_ref()
                .unwrap()
                .header_bases(scope, &mut Vec::new())
            else {
                continue;
            };
            if !completeness.scope(b, scope, &mut proof_steps) {
                continue;
            }
            let inherited = b.inherited_bindings(scope, true);
            if inherited.incomplete || inherited.truncated {
                continue;
            }
            if bases.iter().any(|&base| {
                let inherited = b.inherited_bindings(base, true);
                inherited.incomplete || inherited.truncated
            }) {
                continue;
            }
            b.exclude = Some(feature);
            if b.id_spelled_target(site.scope.0, &qn).is_some() {
                continue;
            }
            for base in bases {
                let hit = b.resolve_result(base, &qn, 0, false);
                if let LookupResult::Found(target, _, _) = hit {
                    if !crate::metaclass::conforms(b.elements[target].ty, "Feature") {
                        continue;
                    }
                    // If the model no longer reproduces the stored endpoint,
                    // do not infer intent from an approximate lookup.
                    if target == site.target.0 {
                        let stamp = b.next_stamp();
                        if matches!(
                            b.lookup_at(base, &qn.segments[0].value, 0, stamp, LookupAccess::All),
                            LookupResult::Missing
                        ) {
                            let inherited = b.inherited_bindings(base, true);
                            if !inherited.incomplete && !inherited.truncated {
                                out.push((site.clone(), qn.segments[0].value.clone()));
                            }
                        }
                    }
                    break;
                }
            }
        }
        (
            b.exclude,
            b.declared_only,
            b.redefinition_lookup_owner,
            b.redefinition_lookup_base,
            b.recorded_lookup_suppressed,
            b.identity_origin_unit,
        ) = saved;
        b.used_imports = used;
        b.query_imports = imports;
        b.current_misses = misses;
        b.root_misses = roots;
        out
    }
}
