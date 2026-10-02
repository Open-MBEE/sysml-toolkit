//! Checks over the declared specialization edges of an element —
//! subclassification cycles and duplicates, the metaclass a metadata
//! feature is typed by, the conformance a redefinition owes its target,
//! and the binariness a connector inherits through one.
use super::multiplicity_domains::DomainRows;
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
    let specs: Vec<_> =
        r.b.spec_targets
            .iter()
            .enumerate()
            .filter(|(_, row)| !model.is_library_unit(r.b.unit_of_elem(row.0)))
            .map(|(i, row)| (i, row.clone()))
            .collect();
    // Pending resolution already applied source identity and header exclusions.
    // Re-resolving display spellings can select a different element.
    let mut resolved: Vec<(
        usize,
        &'static str,
        usize,
        &sysmlv2_syntax::ast::QualifiedName,
    )> = Vec::new();
    for (i, (owner, kind, _, qn)) in &specs {
        if let Some(t) = r.b.spec_resolved.get(*i).copied().flatten() {
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
    for (_, (owner, kind, _, _)) in &specs {
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

    let domains = DomainRows::new(&r.b);
    let mut reported_domains = HashSet::new();

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
        // Compare complete, explicitly constrained domains in the same receiver.
        // A named domain's source span may belong to another file; findings for
        // body/named constraints belong at this user's specialization site.
        let span =
            r.b.declared_multiplicity_of(owner)
                .map_or(qn.span, |(_, m)| m.span);
        let comparison = domains.compare(&mut r.b, owner, target);
        if let Some(scope) = r.b.owner_scope_of(owner) {
            reported_domains.extend(comparison.reported_rows.iter().map(|&row| (scope, row)));
        }
        for (general, reason) in comparison.invalid {
            let subject = if general {
                format!("multiplicity constraint from `{}`", qn.to_display_string())
            } else {
                "specializing multiplicity".into()
            };
            out.push((
                unit,
                Diagnostic::error(
                    qn.span,
                    format!("{subject} is invalid in this specializing context: {reason}"),
                ),
            ));
        }
        if let Some((own, general)) = comparison.intervals {
            if (kind == "Redefinition" && own.lower < general.lower) || own.upper > general.upper {
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        if kind == "Redefinition" {
                            format!("redefining multiplicity [{}..{}] is not within the redefined feature's [{}..{}]", own.lower, own.upper, general.lower, general.upper)
                        } else {
                            format!("subsetting multiplicity upper bound {} exceeds the subsetted feature's upper bound {}", own.upper, general.upper)
                        },
                    ),
                ));
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
    // An unchanged inherited Feature has no local specialization site. Its
    // bounds must nevertheless remain valid after receiver value redefinition.
    // Restrict this pass to non-Feature subclassifying receivers; nested
    // instance/Feature contexts need an explicit evaluation environment.
    let mut receivers = HashSet::new();
    let mut providers = crate::json::provider_completeness::ProviderCompleteness::default();
    for (receiver, kind, _, qn) in &resolved {
        if *kind != "Subclassification"
            || crate::metaclass::conforms(r.b.elements[*receiver].ty, "Feature")
            || !receivers.insert(*receiver)
        {
            continue;
        }
        let Some(&scope) = r.b.elem_scope.get(receiver) else {
            continue;
        };
        let mut steps = 0;
        if !providers.scope(&mut r.b, scope, &mut steps) {
            continue;
        }
        let Some(mut features) = r.b.cardinality_feature_candidates(*receiver, &mut steps) else {
            continue;
        };
        features.retain(|&feature| {
            r.b.owner_elem(feature) != Some(*receiver)
                && !crate::metaclass::conforms(r.b.elements[feature].ty, "Multiplicity")
        });
        for (row, feature, reason) in
            domains.inherited_invalid(&mut r.b, scope, &features, &mut steps)
        {
            if !reported_domains.insert((scope, row)) {
                continue;
            }
            let name = r.b.elements[feature]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .unwrap_or("<anonymous>");
            out.push((
                r.b.unit_of_elem(*receiver),
                Diagnostic::error(
                    qn.span,
                    format!(
                        "inherited multiplicity of `{name}` is invalid in this specializing context: {reason}"
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trailing_shorthand_metadata_rows_have_pending_outcomes() {
        for declaration in ["#M class C;", "class C { @M; }"] {
            let mut model = Model::new();
            model.add_source(
                "test.kerml",
                &format!("package P {{ metaclass M; {declaration} }}"),
            );
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let target = r.resolve_qualified("P::M").unwrap().0;
            assert_eq!(r.b.spec_targets.len(), 1);
            assert_eq!(r.b.spec_resolved.len(), 1);
            assert_eq!(r.b.spec_resolved[0], Some(target));
            assert!(validate(&mut r, &model).is_empty());
        }
    }
}
