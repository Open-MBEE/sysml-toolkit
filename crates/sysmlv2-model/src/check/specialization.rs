//! Checks over the declared specialization edges of an element —
//! subclassification cycles and duplicates, the metaclass a metadata
//! feature is typed by, the conformance a redefinition owes its target,
//! and the binariness a connector inherits through one.
use super::user_rows;
use crate::{json::ResolvedModel, model::Model};
use std::collections::{HashMap, HashSet};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // --- subclassification self-reference / cycles / duplicates ---
    // Library-owned specializations can't produce findings (every check
    // below skips library owners) and can't participate in a user-visible
    // cycle (no library edge points into a user definition) — skipping
    // them keeps the semantic pass proportional to the user model.
    let specs = user_rows(&r.b, model, r.b.spec_targets.iter(), |row| row.0);
    // Resolve every recorded target once.
    let mut resolved: Vec<(
        usize,
        &'static str,
        usize,
        &sysmlv2_syntax::ast::QualifiedName,
    )> = Vec::new();
    for (owner, kind, scope, qn) in &specs {
        if let Some(t) = r.b.resolve(*scope, qn, 0) {
            resolved.push((*owner, kind, t, qn));
        }
    }
    let mut subcl_edges: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut seen_per_owner: HashSet<(usize, &'static str, usize)> = HashSet::new();
    for (owner, kind, target, qn) in &resolved {
        let unit = r.b.unit_of_elem(*owner);
        let is_lib = model.is_library_unit(unit);
        if *kind == "Subclassification" {
            if target == owner && !is_lib {
                out.push((
                    unit,
                    Diagnostic::error(
                        qn.span,
                        format!("`{}` cannot specialize itself", qn.to_display_string()),
                    ),
                ));
                continue;
            }
            subcl_edges.entry(*owner).or_default().push(*target);
        }
        if !seen_per_owner.insert((*owner, kind, *target)) && !is_lib {
            out.push((
                unit,
                Diagnostic::warning(
                    qn.span,
                    format!("duplicate specialization of `{}`", qn.to_display_string()),
                ),
            ));
        }
    }
    // Cycle detection over subclassification edges (self-edges reported above).
    for (owner, kind, _, qn) in &resolved {
        if *kind != "Subclassification" {
            continue;
        }
        let unit = r.b.unit_of_elem(*owner);
        if model.is_library_unit(unit) {
            continue;
        }
        // DFS from each of owner's supertypes back to owner.
        let mut stack: Vec<usize> = subcl_edges.get(owner).cloned().unwrap_or_default();
        let mut seen: HashSet<usize> = HashSet::new();
        let mut cyclic = false;
        while let Some(s) = stack.pop() {
            if s == *owner {
                cyclic = true;
                break;
            }
            if seen.insert(s) {
                if let Some(next) = subcl_edges.get(&s) {
                    stack.extend(next);
                }
            }
        }
        if cyclic {
            out.push((
                unit,
                Diagnostic::error(
                    qn.span,
                    "circular specialization: this definition transitively \
                     specializes itself"
                        .to_string(),
                ),
            ));
        }
    }

    // --- metadata feature typing ---
    // A metadata feature must be typed by exactly one metaclass — a
    // `metadata def` (SysML) or `metaclass` (KerML). A typing that
    // resolves to any other kind of element is provably wrong (error);
    // unresolved targets stay referential warnings, per checker policy.
    let mut metadata_typing_count: HashMap<usize, usize> = HashMap::new();
    for (owner, kind, _, _) in &specs {
        if *kind == "FeatureTyping"
            && matches!(r.b.elements[*owner].ty, "MetadataUsage" | "MetadataFeature")
        {
            *metadata_typing_count.entry(*owner).or_insert(0) += 1;
        }
    }
    let mut metadata_first_typing: HashSet<usize> = HashSet::new();
    for (owner, kind, target, qn) in &resolved {
        if *kind != "FeatureTyping"
            || !matches!(r.b.elements[*owner].ty, "MetadataUsage" | "MetadataFeature")
        {
            continue;
        }
        let unit = r.b.unit_of_elem(*owner);
        if model.is_library_unit(unit) {
            continue;
        }
        let target_ty = r.b.elements[*target].ty;
        if !matches!(target_ty, "MetadataDefinition" | "Metaclass") {
            out.push((
                unit,
                Diagnostic::error(
                    qn.span,
                    format!(
                        "metadata must be typed by a metadata definition or \
                         metaclass; `{}` is a {}",
                        qn.to_display_string(),
                        target_ty
                    ),
                ),
            ));
        } else if metadata_typing_count.get(owner).copied().unwrap_or(0) > 1
            && !metadata_first_typing.insert(*owner)
        {
            out.push((
                unit,
                Diagnostic::error(
                    qn.span,
                    "metadata must be typed by exactly one metaclass".to_string(),
                ),
            ));
        }
    }

    // Numeric bounds of a multiplicity: `[l..u]` directly, `[u]` is
    // exact (`l = u`) except `[*]`, whose missing lower is 0.
    let bounds = |r: &mut crate::json::ResolvedModel,
                  scope: usize,
                  m: &sysmlv2_syntax::ast::Multiplicity|
     -> Option<(f64, f64)> {
        let hi =
            super::scalar_f64(&crate::eval::evaluate_expr_in(&mut r.b, scope, &m.upper).ok()?)?;
        let lo = match &m.lower {
            Some(l) => super::scalar_f64(&crate::eval::evaluate_expr_in(&mut r.b, scope, l).ok()?)?,
            None if hi.is_infinite() => 0.0,
            None => hi,
        };
        Some((lo, hi))
    };

    // --- redefinition type-compatibility ---
    // A redefining feature's declared types should conform to the
    // redefined feature's declared types (KerML 8.4 redefinition
    // conformance). Checked only when both sides carry explicit typings
    // and the target's type is user-owned — the explicit closure is
    // complete between user types, while conformance to a *library*
    // type may ride implied bases this walk cannot see (those stay
    // silent). Deliberately NOT checked for `Subsetting`: KerML's
    // multiple classification lets a value be both a `Cause` and a
    // `Situation` without `Cause` specializing `Situation`, and the
    // official `Model Library Example.sysml` uses exactly that pattern
    // (`causes : Cause[*] :> situations`). Warnings, per checker policy.
    for i in 0..r.b.spec_targets.len() {
        let (owner, kind) = {
            let t = &r.b.spec_targets[i];
            (t.0, t.1)
        };
        if !matches!(kind, "Redefinition" | "Subsetting") {
            continue;
        }
        let unit = r.b.unit_of_elem(owner);
        if model.is_library_unit(unit) {
            continue;
        }
        // The builder's pending pass already resolved this target with the
        // owner excluded (`:>> x` names the *inherited* feature) — read the
        // recorded outcome instead of re-resolving, which self-hits and
        // falls through to full import scans (~0.2 ms per redefinition).
        let Some(target) = r.b.spec_resolved.get(i).copied().flatten() else {
            continue; // unresolved targets are the referential checks' job
        };
        if target == owner {
            continue;
        }
        let qn = r.b.spec_targets[i].3.clone();
        // Multiplicity conformance: when both sides declare
        // explicit numeric multiplicities, the redefining range must
        // lie within the redefined one.
        // Copied out of the table because evaluating the bounds needs
        // the builder mutably; only the two clauses in play are copied.
        let declared = |r: &mut crate::json::ResolvedModel, e: usize| {
            r.b.declared_multiplicity_of(e).map(|(s, m)| (s, m.clone()))
        };
        if let (Some((os, om)), Some((ts, tm))) = (declared(r, owner), declared(r, target)) {
            let span = om.span;
            if let (Some((olo, ohi)), Some((tlo, thi))) = (bounds(r, os, &om), bounds(r, ts, &tm)) {
                // A subset may have fewer values; only redefinition must
                // preserve the lower bound as well as the upper bound.
                if (kind == "Redefinition" && olo < tlo) || ohi > thi {
                    out.push((
                        unit,
                        Diagnostic::warning(
                            span,
                            if kind == "Redefinition" {
                                format!("redefining multiplicity [{olo}..{ohi}] is not within the redefined feature's [{tlo}..{thi}]")
                            } else {
                                format!("subsetting multiplicity upper bound {ohi} exceeds the subsetted feature's upper bound {thi}")
                            },
                        ),
                    ));
                }
            }
        }
        if kind == "Subsetting" {
            continue; // Multiple classification permits heterogeneous types.
        }
        let own_types = r.b.direct_typing_elems(owner);
        if own_types.is_empty() {
            continue;
        }
        for tt in r.b.direct_typing_elems(target) {
            if tt < r.b.lib_boundary {
                continue; // may conform via implied bases
            }
            if own_types.iter().any(|&ot| r.b.conforms_upward(ot, tt)) {
                continue;
            }
            out.push((
                unit,
                Diagnostic::warning(
                    qn.span,
                    format!(
                        "feature redefines `{}` but none of its declared types \
                         conform to the target's type `{}`",
                        qn.to_display_string(),
                        r.b.elements[tt]
                            .props
                            .get("declaredName")
                            .and_then(|v| v.as_str())
                            .unwrap_or("<anonymous>")
                    ),
                ),
            ));
        }
    }
    // --- connector binary specialization (KerML
    // checkConnectorBinarySpecialization) ---
    // A connector with more than two ends must not specialize a *binary*
    // connector: binary means a library binary-links family element, or a
    // user connector-family element with exactly two ends (the two-end
    // shape implies the binary library base). The n-ary declaration
    // itself is legal — the offending edge is the typing/subsetting/
    // redefinition that demands binariness, so the diagnostic lands on
    // that target's spelling.
    {
        let connector_family = |ty: &str| {
            matches!(
                ty,
                "ConnectionUsage"
                    | "ConnectionDefinition"
                    | "InterfaceUsage"
                    | "InterfaceDefinition"
                    | "AllocationUsage"
                    | "AllocationDefinition"
                    | "Connector"
                    | "BindingConnector"
            )
        };
        let end_count = |b: &crate::json::Builder, e: usize| {
            b.elements[e]
                .owned_relationships
                .iter()
                .filter(|&&rel| b.elements[rel].ty == "EndFeatureMembership")
                .count()
        };
        // The library binary-links family, resolved once (absent without
        // the library — the user-side two-end test still applies).
        let mut binary_lib: HashSet<usize> = HashSet::new();
        for qn in [
            "Links::binaryLinks",
            "Links::BinaryLink",
            "Connections::binaryConnections",
            "Connections::BinaryConnection",
            "Interfaces::binaryInterfaces",
            "Interfaces::BinaryInterface",
        ] {
            if let Some(t) = r.b.resolve(0, &crate::json::lib_qn(qn), 0) {
                binary_lib.insert(t);
            }
        }
        let is_binary_node = |b: &mut crate::json::Builder,
                              binary_lib: &HashSet<usize>,
                              n: usize| {
            binary_lib.contains(&n) || (connector_family(b.elements[n].ty) && end_count(b, n) == 2)
        };
        for (owner, kind, target, qn) in &resolved {
            if !matches!(*kind, "FeatureTyping" | "Subsetting" | "Redefinition") {
                continue;
            }
            if !connector_family(r.b.elements[*owner].ty) || end_count(&r.b, *owner) <= 2 {
                continue;
            }
            // Binary directly, or anywhere up the target's explicit closure.
            let mut binary = is_binary_node(&mut r.b, &binary_lib, *target);
            if !binary {
                let mut seen: HashSet<usize> = HashSet::new();
                let mut stack = vec![*target];
                while let Some(n) = stack.pop() {
                    if !seen.insert(n) {
                        continue;
                    }
                    if is_binary_node(&mut r.b, &binary_lib, n) {
                        binary = true;
                        break;
                    }
                    stack.extend(r.b.explicit_supertype_elems(n));
                }
            }
            if binary {
                let ends = end_count(&r.b, *owner);
                out.push((
                    r.b.unit_of_elem(*owner),
                    Diagnostic::warning(
                        qn.span,
                        format!(
                            "connector with {ends} ends specializes a binary connector (a binary connector cannot have more than two ends)"
                        ),
                    ),
                ));
            }
        }
    }
    out
}
