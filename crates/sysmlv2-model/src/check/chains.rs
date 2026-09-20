//! Featuring accessibility of a chain-written subsetting target: the
//! chain's root fixes the featuring context, so some owning type of the
//! subsetting feature must conform to it.
use crate::{json::ResolvedModel, model::Model};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // --- chain-target subsetting featuring accessibility (KerML
    // validateSubsettingFeaturingTypes, narrowed to chain-written
    // targets) ---
    // `part m :> a.b;` subsets a feature reached *through* `a`, so the
    // chain's root fixes the featuring context: some owning type of the
    // subsetting feature must conform to the root's featuring type, or
    // the subsetted feature is not accessible from the subsetter
    // (nesting the subsetter in a conforming type fixes it). Lenient on
    // unresolved roots, package-owned roots (featured by Base::Anything,
    // accessible anywhere), and library featuring — the connector-end
    // precedent.
    {
        let is_type = |ty: &str| {
            ty.ends_with("Definition")
                || ty.ends_with("Usage")
                || matches!(
                    ty,
                    "Classifier"
                        | "Structure"
                        | "Class"
                        | "DataType"
                        | "Behavior"
                        | "Function"
                        | "Association"
                        | "AssociationStructure"
                        | "Interaction"
                        | "Metaclass"
                        | "Feature"
                        | "Step"
                )
        };
        let owning_type = |r: &mut crate::json::ResolvedModel, e: usize| -> Option<usize> {
            let mut cur = r.owner(crate::json::ElementRef(e));
            while let Some(o) = cur {
                let ty = r.element_type(o);
                if is_type(ty) {
                    return Some(o.0);
                }
                if matches!(ty, "Package" | "LibraryPackage" | "Namespace") {
                    return None;
                }
                cur = r.owner(o);
            }
            None
        };
        let sites: Vec<_> =
            r.b.chain_subsettings
                .iter()
                .filter(|row| !model.is_library_unit(r.b.unit_of_elem(row.0)))
                .cloned()
                .collect();
        for (owner, scope, links, span) in sites {
            let unit = r.b.unit_of_elem(owner);
            if model.is_library_unit(unit) {
                continue;
            }
            let Some(root) = r.b.resolve(scope, &links[0], 0) else {
                continue;
            };
            let Some(root_type) = owning_type(r, root) else {
                continue;
            };
            if root_type < r.b.lib_boundary {
                continue;
            }
            let mut anc = owning_type(r, owner);
            let mut ok = false;
            while let Some(t) = anc {
                if r.b.conforms_upward(t, root_type) {
                    ok = true;
                    break;
                }
                anc = owning_type(r, t);
            }
            if !ok {
                let root_name = r.b.elements[root_type]
                    .props
                    .get("declaredName")
                    .and_then(|v| v.as_str())
                    .unwrap_or("<anonymous>")
                    .to_string();
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        format!(
                            "subsetted feature chain is featured in `{root_name}`, which \
                             no owner of the subsetting feature conforms to (nest the \
                             subsetting feature in a type conforming to `{root_name}`)"
                        ),
                    ),
                ));
            }
        }
    }
    out
}
