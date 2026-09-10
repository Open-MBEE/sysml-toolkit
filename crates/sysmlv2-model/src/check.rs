//! Referential checks over a resolved multi-file model.

use sysmlv2_syntax::diag::Diagnostic;

/// Referential checks over a resolved multi-file model:
/// unresolved references, unresolvable alias targets, and circular
/// namespace imports, attributed to the unit they were written in (index
/// into [`crate::model::Model::units`]).
///
/// These are **warnings**: the resolver covers 99.9%+ of the corpus, but a
/// small long tail of legitimate spellings is still beyond it (and some
/// corpus files contain genuine reference errors) — so unresolved names
/// must not fail conforming models. Library units are skipped.
pub fn validate_model(model: &crate::model::Model) -> Vec<(usize, Diagnostic)> {
    let mut r = crate::json::ResolvedModel::build(model);
    validate_model_with(&mut r, model)
}

/// [`validate_model`] over an already-built [`crate::json::ResolvedModel`] —
/// lets one build serve both referential and semantic checks (drains the
/// builder's unresolved list; run this before [`validate_semantics_with`]).
pub fn validate_model_with(
    r: &mut crate::json::ResolvedModel,
    model: &crate::model::Model,
) -> Vec<(usize, Diagnostic)> {
    let report = crate::json::resolution_report_from(&mut r.b);
    // The alias-specific finding subsumes the generic unresolved one at the
    // same location.
    let alias_spans: std::collections::HashSet<(usize, u32)> = report
        .unresolved_aliases
        .iter()
        .map(|(unit, qn)| (*unit, qn.span.start))
        .collect();
    let mut out = Vec::new();
    for (unit, qn) in report.unresolved {
        if model.units()[unit].is_library || alias_spans.contains(&(unit, qn.span.start)) {
            continue;
        }
        out.push((
            unit,
            Diagnostic::warning(
                qn.span,
                format!("unresolved reference `{}`", qn.to_display_string()),
            ),
        ));
    }
    for (unit, qn) in report.ambiguous {
        if model.units()[unit].is_library {
            continue;
        }
        out.push((
            unit,
            Diagnostic::error(
                qn.span,
                format!(
                    "ambiguous reference `{}` resolves to multiple memberships",
                    qn.to_display_string()
                ),
            ),
        ));
    }
    for (unit, qn) in report.unresolved_aliases {
        if model.units()[unit].is_library {
            continue;
        }
        out.push((
            unit,
            Diagnostic::warning(
                qn.span,
                format!("alias target `{}` does not resolve", qn.to_display_string()),
            ),
        ));
    }
    for (unit, qn) in report.import_cycles {
        if model.units()[unit].is_library {
            continue;
        }
        out.push((
            unit,
            Diagnostic::warning(
                qn.span,
                format!(
                    "circular namespace import: `{}` transitively imports this \
                     namespace back",
                    qn.to_display_string()
                ),
            ),
        ));
    }
    // Report in source order per unit.
    out.sort_by_key(|(unit, d)| (*unit, d.span.start));
    out
}

/// KerML 8.4-style semantic constraints over the resolved graph,
/// attributed like [`validate_model`]. Checked:
///
/// - **Multiplicity sanity** (errors): bounds that *provably* evaluate to a
///   negative number or to `lower > upper`. Bounds that reference unbound
///   features or fail to evaluate are left undecided (no diagnostic).
/// - **Self / circular subclassification** (errors): a definition that
///   (transitively) specializes itself. Feature subsetting/redefinition is
///   exempt — resolving a feature's own name to an inherited feature is the
///   idiomatic shorthand there.
/// - **Duplicate specializations** (warnings): the same target named twice
///   in one element's typing / subsetting / redefinition lists.
/// - **Metadata typing** (errors): a metadata feature (`@M`, `#M` prefix,
///   `metadata m : M`) whose typing resolves to anything other than a
///   `metadata def` / `metaclass`, or that declares more than one typing.
/// - **Feature-value scalar conformance** (warnings): a feature value that
///   *evaluates* to a scalar whose `ScalarValues` partition (Boolean /
///   String / the Number tower) can never conform to the feature's
///   declared type, or a non-integral rational bound to a feature whose
///   declared type specializes `Integer`. Anything subtler than
///   kind-level disjointness stays silent — see the check body for why
///   a stricter static rule would over-reject.
pub fn validate_semantics(model: &crate::model::Model) -> Vec<(usize, Diagnostic)> {
    let mut r = crate::json::ResolvedModel::build(model);
    validate_semantics_with(&mut r, model)
}

/// [`validate_semantics`] over an already-built [`crate::json::ResolvedModel`].
pub fn validate_semantics_with(
    r: &mut crate::json::ResolvedModel,
    model: &crate::model::Model,
) -> Vec<(usize, Diagnostic)> {
    let r = &mut *r;
    let mut out = Vec::new();

    // --- multiplicity bounds ---
    for (owner, scope, mult) in r.b.multiplicities.clone() {
        if model.units()[r.b.unit_of_elem(owner)].is_library {
            continue;
        }
        let upper = crate::eval::evaluate_expr_in(&mut r.b, scope, &mult.upper).ok();
        let lower = match &mult.lower {
            Some(l) => crate::eval::evaluate_expr_in(&mut r.b, scope, l).ok(),
            None => None,
        };
        let as_num = |v: &crate::eval::Value| match v {
            crate::eval::Value::Integer(i) => Some(*i as f64),
            crate::eval::Value::Rational(f) => Some(*f),
            _ => None,
        };
        let lo = lower.as_ref().and_then(as_num);
        let hi = upper.as_ref().and_then(as_num);
        if let Some(lo) = lo {
            if lo < 0.0 {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(mult.span, "multiplicity lower bound is negative"),
                ));
                continue;
            }
        }
        if let Some(hi) = hi {
            if hi < 0.0 {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(mult.span, "multiplicity upper bound is negative"),
                ));
                continue;
            }
        }
        if let (Some(lo), Some(hi)) = (lo, hi) {
            if lo > hi {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(
                        mult.span,
                        format!("multiplicity lower bound {lo} exceeds upper bound {hi}"),
                    ),
                ));
            }
        }
    }

    // --- subclassification self-reference / cycles / duplicates ---
    use std::collections::{HashMap, HashSet};
    let specs = r.b.spec_targets.clone();
    // Resolve every recorded target once.
    let mut resolved: Vec<(
        usize,
        &'static str,
        usize,
        &sysmlv2_syntax::ast::QualifiedName,
    )> = Vec::new();
    for (owner, kind, scope, qn) in &specs {
        // Library-owned specializations can't produce findings (every check
        // below skips library owners) and can't participate in a user-visible
        // cycle (no library edge points into a user definition) — skipping
        // them keeps the semantic pass proportional to the user model.
        if model.units()[r.b.unit_of_elem(*owner)].is_library {
            continue;
        }
        if let Some(t) = r.b.resolve(*scope, qn, 0) {
            resolved.push((*owner, kind, t, qn));
        }
    }
    let mut subcl_edges: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut seen_per_owner: HashSet<(usize, &'static str, usize)> = HashSet::new();
    for (owner, kind, target, qn) in &resolved {
        let unit = r.b.unit_of_elem(*owner);
        let is_lib = model.units()[unit].is_library;
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
        if model.units()[unit].is_library {
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
        if model.units()[unit].is_library {
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

    // Explicit multiplicities by owner, for redefinition conformance.
    let mults: HashMap<usize, (usize, sysmlv2_syntax::ast::Multiplicity)> =
        r.b.multiplicities
            .iter()
            .map(|(o, s, m)| (*o, (*s, m.clone())))
            .collect();
    // Numeric bounds of a multiplicity: `[l..u]` directly, `[u]` is
    // exact (`l = u`) except `[*]`, whose missing lower is 0.
    let bounds = |r: &mut crate::json::ResolvedModel,
                  scope: usize,
                  m: &sysmlv2_syntax::ast::Multiplicity|
     -> Option<(f64, f64)> {
        let as_num = |v: crate::eval::Value| match v {
            crate::eval::Value::Integer(i) => Some(i as f64),
            crate::eval::Value::Rational(f) => Some(f),
            _ => None,
        };
        let hi = as_num(crate::eval::evaluate_expr_in(&mut r.b, scope, &m.upper).ok()?)?;
        let lo = match &m.lower {
            Some(l) => as_num(crate::eval::evaluate_expr_in(&mut r.b, scope, l).ok()?)?,
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
        if kind != "Redefinition" {
            continue;
        }
        let unit = r.b.unit_of_elem(owner);
        if model.units()[unit].is_library {
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
        if let (Some((os, om)), Some((ts, tm))) = (mults.get(&owner), mults.get(&target)) {
            let (os, om, ts, tm) = (*os, om.clone(), *ts, tm.clone());
            let span = om.span;
            if let (Some((olo, ohi)), Some((tlo, thi))) = (bounds(r, os, &om), bounds(r, ts, &tm)) {
                if olo < tlo || ohi > thi {
                    out.push((
                        unit,
                        Diagnostic::warning(
                            span,
                            format!(
                                "redefining multiplicity [{}..{}] is not within \
                                 the redefined feature's [{}..{}]",
                                olo, ohi, tlo, thi
                            ),
                        ),
                    ));
                }
            }
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

    // --- invocation arity ---
    // A user-defined calculation invoked with fewer positional arguments
    // than its declared `in`/`inout` parameters leaves the trailing
    // parameters unbound — the result can never compute unless they carry
    // defaults. Warnings, conservatively scoped: all-positional calls
    // only (named arguments bind explicitly), lambda bodies skipped,
    // zero-argument spellings skipped (type-reference idioms), and both
    // caller and callee must be outside the standard library (KFL
    // functions overload their parameter lists).
    let mut value_exprs: Vec<(usize, usize, sysmlv2_syntax::ast::Expr)> =
        r.b.values
            .iter()
            .map(|(o, (s, e))| (*o, *s, e.clone()))
            .collect();
    value_exprs.extend(r.b.result_exprs.iter().cloned());
    for (owner, scope, expr) in value_exprs {
        let unit = r.b.unit_of_elem(owner);
        if model.units()[unit].is_library {
            continue;
        }
        let mut sites = Vec::new();
        collect_invocations(&expr, &mut sites);
        for (qn, n_args, span) in sites {
            if n_args == 0 {
                continue;
            }
            let Some(callee) = r.b.resolve(scope, qn, 0) else {
                continue; // unresolved refs are the referential checks' job
            };
            let Some(params) = r.b.in_params.get(&callee).cloned() else {
                continue; // not a parameterized calculation
            };
            if model.units()[r.b.unit_of_elem(callee)].is_library {
                continue;
            }
            // Over-application: more positional arguments than declared
            // parameters can never bind (the arrow spelling passes its
            // target as the first argument — `x->f(a)` supplies two).
            if n_args > params.len() {
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        format!(
                            "invocation of `{}` supplies {n_args} arguments for {} parameter(s)",
                            qn.to_display_string(),
                            params.len(),
                        ),
                    ),
                ));
                continue;
            }
            if n_args == params.len() {
                continue;
            }
            // Unbound trailing parameters that all carry their own
            // (default) values are fine.
            let fields = r.b.ctor_fields.get(&callee);
            let all_defaulted = params[n_args..].iter().all(|p| {
                fields
                    .and_then(|fs| fs.iter().find(|(n, _)| n == p))
                    .map(|(_, e)| r.b.values.contains_key(e))
                    .unwrap_or(false)
            });
            if all_defaulted {
                continue;
            }
            out.push((
                unit,
                Diagnostic::warning(
                    span,
                    format!(
                        "invocation of `{}` binds {n_args} of its {} parameters \
                         (`{}` never bound)",
                        qn.to_display_string(),
                        params.len(),
                        params[n_args..].join("`, `")
                    ),
                ),
            ));
        }
    }

    // --- feature-value scalar conformance ---
    // Narrowed to what is provable. A stricter static rule — the value
    // expression's *declared* result type must conform to the feature's
    // declared type — would reject 15 official corpus files whose bindings
    // are legal under KerML multiple classification: a `Rational`-typed
    // literal's value may well inhabit a sibling subtype of `Real`
    // (`ScalarValues::Rational does not conform to EnumerationTest::Size`
    // is exactly the corpus's enum-restriction idiom, and the ISO-8601
    // string encodings and metadata levels follow the same shape). What
    // *is* provable is kind-level disjointness of the evaluated value:
    // `ScalarValues` partitions its scalars into Boolean, String, and the
    // Number tower, and a value of one partition is never an instance of
    // a type in another; within the tower, a non-integral rational is
    // never an instance of an `Integer`-conforming type. Declared types
    // classify by simple scalar names over the explicit supertype closure
    // (the solver's `declared_sort` discipline — works with or without
    // the standard library); an untyped redefining feature borrows the
    // redefinition target's declared types (one hop). Unclassifiable
    // declared types, unevaluable values, quantities, sequences, and
    // element values all stay silent. Warnings, per checker policy.
    let value_sites: Vec<(usize, usize, sysmlv2_syntax::ast::Expr)> =
        r.b.values
            .iter()
            .map(|(o, (s, e))| (*o, *s, e.clone()))
            .collect();
    for (owner, scope, expr) in value_sites {
        let unit = r.b.unit_of_elem(owner);
        if model.units()[unit].is_library {
            continue;
        }
        let mut tys = r.b.direct_typing_elems(owner);
        if tys.is_empty() {
            for t in r.b.redefinition_target_elems(owner) {
                for ty in r.b.direct_typing_elems(t) {
                    if !tys.contains(&ty) {
                        tys.push(ty);
                    }
                }
            }
        }
        // Every declared type must classify — a type this walk cannot
        // place may admit the value through bases it cannot see.
        let kinds: Vec<ScalarKind> = tys
            .iter()
            .filter_map(|&ty| declared_scalar_kind(&mut r.b, ty))
            .collect();
        if kinds.is_empty() || kinds.len() != tys.len() {
            continue;
        }
        let Ok(v) = crate::eval::evaluate_expr_in(&mut r.b, scope, &expr) else {
            continue; // undecided, not wrong
        };
        let value_kind = match &v {
            crate::eval::Value::Boolean(_) => ScalarKind::Boolean,
            crate::eval::Value::String(_) => ScalarKind::Str,
            crate::eval::Value::Integer(_) => ScalarKind::Number { integral: true },
            crate::eval::Value::Rational(f) => ScalarKind::Number {
                integral: f.fract() == 0.0 && f.is_finite(),
            },
            _ => continue, // quantities, sequences, instances, elements
        };
        let admits = |decl: ScalarKind| match (decl, value_kind) {
            (ScalarKind::Boolean, ScalarKind::Boolean) => true,
            (ScalarKind::Str, ScalarKind::Str) => true,
            (ScalarKind::Number { integral: need }, ScalarKind::Number { integral: have }) => {
                !need || have
            }
            _ => false, // cross-partition: provably disjoint
        };
        if kinds.iter().any(|&k| admits(k)) {
            continue;
        }
        let ty_name = r.b.elements[tys[0]]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str())
            .unwrap_or("<anonymous>")
            .to_string();
        let msg = match value_kind {
            ScalarKind::Number { integral: false }
                if matches!(kinds[0], ScalarKind::Number { .. }) =>
            {
                format!(
                    "feature value {v} is not an integer and can never conform \
                     to the declared type `{ty_name}`"
                )
            }
            _ => {
                let vdesc = match value_kind {
                    ScalarKind::Boolean => "a Boolean",
                    ScalarKind::Str => "a String",
                    ScalarKind::Number { .. } => "a number",
                };
                format!(
                    "feature value evaluates to {vdesc}, which can never \
                     conform to the declared type `{ty_name}`"
                )
            }
        };
        out.push((unit, Diagnostic::warning(expr.span, msg)));
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
        for (owner, scope, links, span) in r.b.chain_subsettings.clone() {
            let unit = r.b.unit_of_elem(owner);
            if model.units()[unit].is_library {
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

    // --- connector-end featuring accessibility (KerML canAccess /
    // checkConnectorTypeFeaturing) ---
    // A connector's related features must share a featuring context the
    // connector can be featured within. Statically: some candidate type T
    // — a lexical ancestor of the connector, or a featuring type of one of
    // the related features (or its ancestors) — must *admit* every
    // featured related feature, where T admits a feature featured in F
    // when T conforms to F or T (or a supertype) owns a member typed by /
    // referencing something conforming to F (the one-hop featuring lift:
    // a part that performs/exhibits a behavior gives access to the
    // behavior's features). Package-owned targets have no featuringTypes
    // and are accessible from anywhere — that is what makes the corpus's
    // sibling-namespace binds legal. Lenient by construction: unresolved
    // targets, library featuring, explicit `featured by`, and unresolved
    // chain roots all pass silently.
    {
        let n = r.b.elements.len();
        let mut rel_owner: Vec<Option<usize>> = vec![None; n];
        for (i, e) in r.b.elements.iter().enumerate() {
            for &rel in &e.owned_relationships {
                rel_owner[rel] = Some(i);
            }
        }
        let mut owned_of_rel: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, e) in r.b.elements.iter().enumerate() {
            if let Some(rel) = e.owning_relationship {
                owned_of_rel[rel].push(i);
            }
        }
        let by_id: HashMap<uuid::Uuid, usize> = (0..n).map(|i| (r.b.elem_id(i), i)).collect();
        let is_featuring_membership = |ty: &str| {
            ty.ends_with("Membership")
                && !matches!(ty, "OwningMembership" | "Membership" | "VariantMembership")
        };
        let deref = |b: &crate::json::Builder, v: &serde_json::Value| {
            v.get("@id")
                .and_then(|v| v.as_str())
                .and_then(|s| uuid::Uuid::parse_str(s).ok())
                .and_then(|id| by_id.get(&id).copied())
                .map(|i| (i, b.elements[i].ty))
        };
        let _ = &deref;
        let rel_target = |b: &crate::json::Builder, e: usize, rel_ty: &str, key: &str| {
            b.elements[e]
                .owned_relationships
                .iter()
                .find(|&&rel| b.elements[rel].ty == rel_ty)
                .and_then(|&rel| b.elements[rel].props.get(key))
                .and_then(|v| v.get("@id"))
                .and_then(|v| v.as_str())
                .and_then(|s| uuid::Uuid::parse_str(s).ok())
                .and_then(|id| by_id.get(&id).copied())
        };
        let has_type_featuring = |b: &crate::json::Builder, e: usize| {
            b.elements[e]
                .owned_relationships
                .iter()
                .any(|&rel| b.elements[rel].ty == "TypeFeaturing")
        };
        // Group ends by connector.
        let mut per_connector: HashMap<usize, Vec<(usize, sysmlv2_syntax::span::Span)>> =
            HashMap::new();
        let mut order: Vec<usize> = Vec::new();
        for (connector, end_elem, span) in r.b.connector_ends.clone() {
            per_connector
                .entry(connector)
                .or_insert_with(|| {
                    order.push(connector);
                    Vec::new()
                })
                .push((end_elem, span));
        }
        for connector in order {
            let unit = r.b.unit_of_elem(connector);
            if model.units()[unit].is_library {
                continue;
            }
            let ends = &per_connector[&connector];
            // Featured related features: (target, its featuring type, span).
            let mut featured: Vec<(usize, usize, sysmlv2_syntax::span::Span)> = Vec::new();
            let mut lenient = false;
            for &(end_elem, span) in ends {
                let Some(mut target) =
                    rel_target(&r.b, end_elem, "ReferenceSubsetting", "referencedFeature")
                else {
                    continue; // empty or unresolved end
                };
                // A chain end's featuring is the first link's.
                if let Some(link_v) = r.b.elements[target]
                    .owned_relationships
                    .iter()
                    .find(|&&rel| r.b.elements[rel].ty == "FeatureChaining")
                    .and_then(|&rel| r.b.elements[rel].props.get("chainingFeature"))
                    .cloned()
                {
                    let Some(link) = link_v
                        .get("@id")
                        .and_then(|v| v.as_str())
                        .and_then(|s| uuid::Uuid::parse_str(s).ok())
                        .and_then(|id| by_id.get(&id).copied())
                    else {
                        lenient = true;
                        break;
                    };
                    target = link;
                }
                if model.units()[r.b.unit_of_elem(target)].is_library {
                    continue;
                }
                if has_type_featuring(&r.b, target) {
                    lenient = true;
                    break;
                }
                let f = match r.b.elements[target].owning_relationship {
                    Some(rel) if is_featuring_membership(r.b.elements[rel].ty) => rel_owner[rel],
                    _ => None, // namespace-owned: featured by Anything
                };
                let Some(f) = f else { continue };
                if model.units()[r.b.unit_of_elem(f)].is_library {
                    continue;
                }
                featured.push((target, f, span));
            }
            if lenient || featured.is_empty() {
                continue;
            }
            // Candidate contexts: lexical ancestors of the connector
            // (through any membership) plus each featuring type and its
            // lexical ancestors.
            let mut candidates: Vec<usize> = Vec::new();
            let push_chain = |b: &crate::json::Builder, start: usize, out: &mut Vec<usize>| {
                let mut cur = start;
                for _ in 0..64 {
                    if !out.contains(&cur) {
                        out.push(cur);
                    }
                    let Some(rel) = b.elements[cur].owning_relationship else {
                        break;
                    };
                    let Some(owner) = rel_owner[rel] else { break };
                    cur = owner;
                }
            };
            push_chain(&r.b, connector, &mut candidates);
            for &(_, f, _) in &featured {
                push_chain(&r.b, f, &mut candidates);
            }
            // T admits a feature featured in F when T conforms to F, or a
            // member of T (or of a type T explicitly specializes) is typed
            // by / references something conforming to F.
            let mut admits_cache: HashMap<(usize, usize), bool> = HashMap::new();
            let mut admits = |r: &mut crate::json::ResolvedModel, t: usize, f: usize| -> bool {
                if let Some(&hit) = admits_cache.get(&(t, f)) {
                    return hit;
                }
                let mut ok = t == f || r.b.conforms_upward(t, f);
                if !ok {
                    // One-hop featuring lift over T's own supertype closure.
                    let mut types: Vec<usize> = vec![t];
                    let mut qi = 0;
                    while qi < types.len() && types.len() <= 64 {
                        let cur = types[qi];
                        qi += 1;
                        for s in r.b.explicit_supertype_elems(cur) {
                            if !types.contains(&s) {
                                types.push(s);
                            }
                        }
                    }
                    'outer: for &ty_el in &types {
                        for &rel in &r.b.elements[ty_el].owned_relationships.clone() {
                            for &m in &owned_of_rel[rel].clone() {
                                for key in ["type", "referencedFeature"] {
                                    let rel_ty = if key == "type" {
                                        "FeatureTyping"
                                    } else {
                                        "ReferenceSubsetting"
                                    };
                                    if let Some(g) = rel_target(&r.b, m, rel_ty, key) {
                                        if g == f || r.b.conforms_upward(g, f) {
                                            ok = true;
                                            break 'outer;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                admits_cache.insert((t, f), ok);
                ok
            };
            // Pick the candidate that admits the most related features;
            // the finding names the first feature it cannot reach.
            let mut best: Option<(usize, usize)> = None; // (admitted, cand idx)
            for (i, &t) in candidates.iter().enumerate() {
                let admitted = featured
                    .iter()
                    .filter(|&&(_, f, _)| admits(r, t, f))
                    .count();
                if best.is_none_or(|(b, _)| admitted > b) {
                    best = Some((admitted, i));
                }
            }
            let accessible = best.is_some_and(|(a, _)| a == featured.len());
            if !accessible {
                let best_t = candidates[best.map_or(0, |(_, i)| i)];
                let (target, f, span) = *featured
                    .iter()
                    .find(|&&(_, f, _)| !admits(r, best_t, f))
                    .unwrap_or(&featured[0]);
                let name = |e: usize| {
                    r.b.elements[e]
                        .props
                        .get("declaredName")
                        .and_then(|v| v.as_str())
                        .unwrap_or("<unnamed>")
                        .to_string()
                };
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        format!(
                            "connector end references `{}`, which is featured in \
                             `{}` — no featuring context of the connector reaches \
                             it",
                            name(target),
                            name(f),
                        ),
                    ),
                ));
            }
        }
    }

    out.sort_by_key(|(unit, d)| (*unit, d.span.start));
    out.dedup_by(|a, b| a.0 == b.0 && a.1.span == b.1.span && a.1.message == b.1.message);
    out
}

/// The provably-disjoint `ScalarValues` partitions: Boolean, String, and
/// the Number tower (with `Integer`-and-below tracked for integrality).
#[derive(Clone, Copy, PartialEq)]
enum ScalarKind {
    Boolean,
    Str,
    Number { integral: bool },
}

/// Classify a declared type into its scalar partition by walking the
/// explicit typing/specialization closure and matching the `ScalarValues`
/// simple names — the same name-based discipline as the solver's
/// `declared_sort`, so it works with or without the standard library.
/// Breadth-first, first match wins: the nearest scalar ancestor decides
/// integrality (`Size :> Real` classifies non-integral even though `Real`
/// has integral subtypes). `None` = not provably a scalar type.
fn declared_scalar_kind(b: &mut crate::json::Builder, ty: usize) -> Option<ScalarKind> {
    use std::collections::{HashSet, VecDeque};
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(ty);
    let mut seen: HashSet<usize> = HashSet::new();
    let mut steps = 0;
    while let Some(t) = queue.pop_front() {
        if !seen.insert(t) {
            continue;
        }
        steps += 1;
        if steps > 64 {
            break;
        }
        let name = b.elements[t]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str());
        match name {
            Some("Boolean") => return Some(ScalarKind::Boolean),
            Some("String") => return Some(ScalarKind::Str),
            Some("Integer" | "Natural" | "Positive") => {
                return Some(ScalarKind::Number { integral: true });
            }
            Some("NumericalValue" | "Number" | "Complex" | "Real" | "Rational") => {
                return Some(ScalarKind::Number { integral: false });
            }
            _ => {}
        }
        for s in b.explicit_supertype_elems(t) {
            queue.push_back(s);
        }
    }
    None
}

/// Collect every all-positional invocation site in an expression:
/// `(callee, positional-argument count, span)`. Lambda bodies (`Body`,
/// arrow/collect/select bodies) are not entered — their invocations
/// bind through runtime parameters this static pass cannot see.
fn collect_invocations<'a>(
    e: &'a sysmlv2_syntax::ast::Expr,
    out: &mut Vec<(
        &'a sysmlv2_syntax::ast::QualifiedName,
        usize,
        sysmlv2_syntax::Span,
    )>,
) {
    use sysmlv2_syntax::ast::{ArrowArgs, ExprKind, TargetRef};
    match &e.kind {
        ExprKind::Literal(_)
        | ExprKind::Null
        | ExprKind::Ref(_)
        | ExprKind::Extent { .. }
        | ExprKind::MetadataAccess { .. }
        | ExprKind::Body { .. }
        | ExprKind::BodyTerminator => {}
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_invocations(cond, out);
            collect_invocations(then_branch, out);
            collect_invocations(else_branch, out);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_invocations(lhs, out);
            collect_invocations(rhs, out);
        }
        ExprKind::Unary { operand, .. } => collect_invocations(operand, out),
        ExprKind::Classification { operand, .. } => {
            if let Some(o) = operand {
                collect_invocations(o, out);
            }
        }
        ExprKind::ChainStep { target, .. } => collect_invocations(target, out),
        ExprKind::Index { target, index } => {
            collect_invocations(target, out);
            collect_invocations(index, out);
        }
        ExprKind::Bracket { target, arg } => {
            collect_invocations(target, out);
            collect_invocations(arg, out);
        }
        ExprKind::Arrow { target, args, .. } => {
            collect_invocations(target, out);
            if let ArrowArgs::List(list) = args {
                for a in list {
                    collect_invocations(&a.value, out);
                }
            }
        }
        ExprKind::Collect { target, .. } | ExprKind::Select { target, .. } => {
            collect_invocations(target, out)
        }
        ExprKind::Invocation { ty, args } => {
            if let (TargetRef::Name(qn), true) = (ty, args.iter().all(|a| a.name.is_none())) {
                out.push((qn, args.len(), e.span));
            }
            for a in args {
                collect_invocations(&a.value, out);
            }
        }
        ExprKind::Constructor { args, .. } => {
            for a in args {
                collect_invocations(&a.value, out);
            }
        }
        ExprKind::Sequence(items) => {
            for i in items {
                collect_invocations(i, out);
            }
        }
    }
}

/// Collect every feature reference of an expression, in source order:
/// the `Ref` leaves. Lambda bodies are not entered (their references
/// bind through runtime parameters), and a bracket's unit expression is
/// skipped (`[m]` names a measurement unit, not a model feature a
/// diagnostic should evaluate).
fn collect_feature_refs<'a>(
    e: &'a sysmlv2_syntax::ast::Expr,
    out: &mut Vec<&'a sysmlv2_syntax::ast::QualifiedName>,
) {
    use sysmlv2_syntax::ast::{ArrowArgs, ExprKind};
    match &e.kind {
        ExprKind::Ref(qn) => out.push(qn),
        ExprKind::Literal(_)
        | ExprKind::Null
        | ExprKind::Extent { .. }
        | ExprKind::MetadataAccess { .. }
        | ExprKind::Body { .. }
        | ExprKind::BodyTerminator => {}
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_feature_refs(cond, out);
            collect_feature_refs(then_branch, out);
            collect_feature_refs(else_branch, out);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_feature_refs(lhs, out);
            collect_feature_refs(rhs, out);
        }
        ExprKind::Unary { operand, .. } => collect_feature_refs(operand, out),
        ExprKind::Classification { operand, .. } => {
            if let Some(o) = operand {
                collect_feature_refs(o, out);
            }
        }
        ExprKind::ChainStep { target, .. } => collect_feature_refs(target, out),
        ExprKind::Index { target, index } => {
            collect_feature_refs(target, out);
            collect_feature_refs(index, out);
        }
        ExprKind::Bracket { target, .. } => collect_feature_refs(target, out),
        ExprKind::Arrow { target, args, .. } => {
            collect_feature_refs(target, out);
            if let ArrowArgs::List(list) = args {
                for a in list {
                    collect_feature_refs(&a.value, out);
                }
            }
        }
        ExprKind::Collect { target, .. } | ExprKind::Select { target, .. } => {
            collect_feature_refs(target, out)
        }
        ExprKind::Invocation { args, .. } | ExprKind::Constructor { args, .. } => {
            for a in args {
                collect_feature_refs(&a.value, out);
            }
        }
        ExprKind::Sequence(items) => {
            for i in items {
                collect_feature_refs(i, out);
            }
        }
    }
}

/// One feature reference of a constraint's result expression with its
/// own evaluation — the auxiliary "why" behind a verdict (`reserveKg =
/// 0.10` under a violated `reserveKg >= 0.15`; an unbound reference
/// under an undecided one).
#[derive(Clone, Debug)]
pub struct ConstraintBinding {
    /// The reference's source spelling (`reserveKg`, `Pkg::limit`).
    pub feature: String,
    /// Rendered evaluated value; `None` when the reference does not
    /// evaluate on its own (an unbound feature).
    pub value: Option<String>,
    /// Declaration site of the referenced feature's name: (unit index,
    /// span of the name token). `None` when the reference does not
    /// resolve or the element is synthesized.
    pub site: Option<(usize, sysmlv2_syntax::span::Span)>,
}

/// The feature references of `c`'s result expression, each evaluated on
/// its own in the constraint's scope — first occurrence per spelling.
/// Complements [`constraint_verdict`]: the pair is what a diagnostic
/// needs to say *why* (every binding of a decided verdict carries a
/// value; an undecided verdict's unbound references carry `None`).
pub fn constraint_bindings(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
) -> Vec<ConstraintBinding> {
    let mut refs = Vec::new();
    collect_feature_refs(&c.expr, &mut refs);
    let mut out: Vec<ConstraintBinding> = Vec::new();
    for qn in refs {
        let feature = qn.to_display_string();
        if out.iter().any(|b| b.feature == feature) {
            continue;
        }
        let site = r
            .resolve_in(c.scope, qn)
            .and_then(|e| r.declaration_site(e));
        let probe = sysmlv2_syntax::ast::Expr {
            kind: sysmlv2_syntax::ast::ExprKind::Ref(qn.clone()),
            span: qn.span,
        };
        // An unvalued feature evaluates to itself as a bare element,
        // which renders opaquely (`<element>`) — that is the unbound
        // case for diagnostic purposes, not a value worth showing.
        let value = match r.evaluate_in(c.scope, &probe) {
            Ok(crate::eval::Value::Element(_) | crate::eval::Value::Unbound(_)) | Err(_) => None,
            Ok(v) => Some(v.to_string()),
        };
        out.push(ConstraintBinding {
            feature,
            value,
            site,
        });
    }
    out
}

/// Verdict of one constraint-family element's trailing result expression
/// (checking only — no solving).
#[derive(Clone, Debug, PartialEq)]
pub enum ConstraintVerdict {
    /// The result expression evaluated to the asserted truth value.
    Satisfied,
    /// The result expression evaluated against the asserted truth value.
    Violated,
    /// Not decidable by evaluation — unbound features, unsupported
    /// constructs, or a non-boolean result. Carries the reason.
    Undecided(String),
}

/// One checked constraint.
#[derive(Clone, Debug)]
pub struct ConstraintCheck {
    /// Index into [`crate::model::Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element (e.g. `AssertConstraintUsage`).
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold (assert usages and KerML
    /// invariants; `assert not` / `inv false` invert the expected value).
    pub asserted: bool,
    pub verdict: ConstraintVerdict,
    /// Feature bindings of the result expression — the "why" behind a
    /// non-satisfied verdict. Empty for satisfied constraints (nothing
    /// to explain).
    pub bindings: Vec<ConstraintBinding>,
    /// For verdicts produced by a satisfaction claim: the qualified name
    /// of the satisfied requirement the constraint was evaluated under
    /// (subjects bound to the satisfaction target). `None` for ordinary
    /// constraint verdicts.
    pub context: Option<String>,
}

/// Evaluate every constraint/requirement/invariant body with its own
/// trailing result expression to a verdict (library units skipped).
/// Inherited bodies (`assert constraint c : Def;` where only `Def` carries
/// the expression) are not yet checked — a featuring-context increment.
pub fn check_constraints(model: &crate::model::Model) -> Vec<ConstraintCheck> {
    let mut r = crate::json::ResolvedModel::build(model);
    let mut out = Vec::new();
    for c in r.constraints() {
        if model.units()[c.unit].is_library {
            continue;
        }
        let verdict = constraint_verdict(&mut r, &c);
        let bindings = match verdict {
            ConstraintVerdict::Satisfied => Vec::new(),
            _ => constraint_bindings(&mut r, &c),
        };
        out.push(ConstraintCheck {
            unit: c.unit,
            span: c.span,
            name: c.name,
            element_type: c.element_type,
            asserted: c.asserted,
            verdict,
            bindings,
            context: None,
        });
    }
    out.extend(satisfaction_checks(model, &mut r));
    out
}

/// Satisfaction claims (`satisfy R by x;`) expanded to bound constraint
/// verdicts: every constraint reachable through the satisfied
/// requirement's composition evaluates with the requirement's subjects
/// bound to the satisfaction target (see
/// [`crate::json::ResolvedModel::satisfactions`]). The same constraints
/// may also carry ordinary (unbound, usually undecided) verdicts from
/// [`check_constraints`]'s main pass — the `context` field tells the two
/// apart.
pub fn satisfaction_checks(
    model: &crate::model::Model,
    r: &mut crate::json::ResolvedModel,
) -> Vec<ConstraintCheck> {
    let mut out = Vec::new();
    for s in r.satisfactions() {
        for c in &s.constraints {
            if model.units()[c.unit].is_library {
                continue;
            }
            let verdict = match r.evaluate_in_with(c.scope, &c.expr, &s.overrides) {
                Ok(crate::eval::Value::Boolean(b)) => {
                    if b != c.negated {
                        ConstraintVerdict::Satisfied
                    } else {
                        ConstraintVerdict::Violated
                    }
                }
                Ok(crate::eval::Value::Indeterminate) => ConstraintVerdict::Undecided(
                    "result is indeterminate over unbound features".to_string(),
                ),
                Ok(other) => {
                    ConstraintVerdict::Undecided(format!("result is not a boolean: {other}"))
                }
                Err(e) => ConstraintVerdict::Undecided(e.to_string()),
            };
            out.push(ConstraintCheck {
                unit: c.unit,
                span: c.span,
                name: c.name.clone(),
                element_type: c.element_type,
                asserted: true,
                verdict,
                bindings: Vec::new(),
                context: s.context.clone(),
            });
        }
    }
    out
}

/// Evaluate one enumerated constraint to its verdict (shared by
/// [`check_constraints`] and the `sysmlv2-solve` crate, which solves the
/// undecided ones).
pub fn constraint_verdict(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
) -> ConstraintVerdict {
    match r.evaluate_in(c.scope, &c.expr) {
        Ok(crate::eval::Value::Boolean(b)) => {
            if b != c.negated {
                ConstraintVerdict::Satisfied
            } else {
                ConstraintVerdict::Violated
            }
        }
        Ok(crate::eval::Value::Indeterminate) => ConstraintVerdict::Undecided(
            "result is indeterminate over unbound features".to_string(),
        ),
        Ok(other) => ConstraintVerdict::Undecided(format!("result is not a boolean: {other}")),
        Err(e) => ConstraintVerdict::Undecided(e.to_string()),
    }
}
