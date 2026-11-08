//! Valuation and metadata contracts. Missing types remain undecided.
use super::facts::Facts;
use crate::metaclass::is_a;
use crate::{
    json::{ElementRef, ResolvedModel},
    model::Model,
};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    g: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    for claim in r.self_bound_satisfactions() {
        if !model.is_library_unit(claim.unit) {
            if let Some(reason) = claim.self_bound {
                out.push((
                    claim.unit,
                    Diagnostic::warning(claim.span, reason).with_code("selfBoundSatisfaction"),
                ));
            }
        }
    }
    // End features that a connector claims, indexed once for the walk.
    let connected: std::collections::HashSet<usize> =
        r.b.connector_ends.iter().map(|(_, end, _)| *end).collect();
    // The effective members of a metadata feature's types, by type: the
    // features typed by the same definition offer the same members.
    let mut members_of: crate::layered::IdMap<usize, std::sync::Arc<Vec<usize>>> =
        Default::default();
    let mut effective_members_of = |r: &ResolvedModel, t: usize| -> std::sync::Arc<Vec<usize>> {
        match members_of.get(&t) {
            Some(members) => std::sync::Arc::clone(members),
            None => {
                let members = std::sync::Arc::new(g.effective_members(&r.b, t));
                members_of.insert(t, std::sync::Arc::clone(&members));
                members
            }
        }
    };
    for e in r.b.lib_boundary..r.b.explicit_len() {
        let unit = r.b.unit_of_elem(e);
        if model.is_library_unit(unit) {
            continue;
        }
        let span = g.span(&r.b, e);
        if let Some(value_span) = r.b.values.get(&e).map(|(_, value)| value.span) {
            // What `e` redefines, a redefined chain's last link (and what
            // that redefines) included: `:>> chassis.mass = 2` overrides
            // `mass` as `part :>> chassis { :>> mass = 2; }` does.
            let mut redefined = g.redefined(&r.b, e);
            for links in r.redefined_chains(ElementRef(e)) {
                if let Some(&last) = links.last() {
                    redefined.push(last.0);
                    redefined.extend(g.redefined(&r.b, last.0));
                }
            }
            // And a redefinition the owner inherits that binds the same
            // path (`part def M2 :> M { :>> chassis.mass = 1; }` under
            // `part m : M2 { :>> chassis.mass = 5; }`, or either in the
            // nested form) — paths compared by the features their links
            // stand for, so a link a type in between redefines in a block
            // of its own, or a named block (`part ch2 :>> chassis { … }`),
            // still matches.
            if let Some((owner, path)) = redefinition_path(r, ElementRef(e)) {
                if path.len() >= 2 {
                    let path: Vec<ElementRef> =
                        path.into_iter().map(|l| r.redefinition_root(l)).collect();
                    for f in r.inherited_features(owner, false) {
                        inherited_bindings(r, f, &[], &path, 0, &mut redefined);
                    }
                }
            }
            if let Some(target) = redefined
                .into_iter()
                .find(|t| r.b.values.contains_key(t) && !r.b.default_values.contains(t))
            {
                let name = chain_display_name(r, ElementRef(target))
                    .or_else(|| r.element_qualified_name(ElementRef(target)))
                    .or_else(|| effective_display_name(r, ElementRef(target)))
                    .unwrap_or_else(|| format!("@{}", r.element_id(ElementRef(target))));
                let target_unit = r.b.unit_of_elem(target);
                let binding_span = r.b.values.get(&target).unwrap().1.span;
                // The unit's name and line index alone: a library unit's
                // syntax is not reconstructed for them.
                let (source_name, lines) = model.unit_meta(target_unit);
                let position = lines.line_col(binding_span.start);
                out.push((unit, super::rule_error(value_span, "validateFeatureValueOverriding",
                    format!("Cannot override the non-default value of `{name}`, bound at {}:{}:{}; the inherited value must be default to allow a new value", source_name, position.line, position.col))));
            }
        }
        if is_a!(r.b.elements[e], "EnumerationUsage") {
            if let Some((_, expr)) = r.b.values.get(&e) {
                if matches!(expr.kind, sysmlv2_syntax::ast::ExprKind::Body { .. }) {
                    out.push((
                        unit,
                        super::rule_error(
                            expr.span,
                            "validateEnumerationUsageType",
                            "An expression body is not a value of the owning enumeration",
                        ),
                    ));
                }
            }
        }
        if super::facts::flag(&r.b, e, "isEnd") && !connected.contains(&e) {
            if let Some((lo, hi)) = r.declared_multiplicity(ElementRef(e)) {
                if lo != 1.0 || hi != 1.0 {
                    out.push((
                        unit,
                        super::rule_warning(
                            span,
                            "validateFeatureEndFeatureMultiplicity",
                            "An end feature should have multiplicity 1..1",
                        ),
                    ));
                }
            }
        }
        if !is_a!(r.b.elements[e], "MetadataFeature") || g.typed(&r.b, e).is_empty() {
            continue;
        }
        let offered = g
            .typed(&r.b, e)
            .into_iter()
            .flat_map(|t| effective_members_of(r, t).to_vec())
            .collect::<Vec<_>>();
        let mut stack = vec![(e, offered)];
        while let Some((owner, offered)) = stack.pop() {
            for &m in &g.members[owner] {
                if !is_a!(r.b.elements[m], "Feature")
                    || is_a!(r.b.elements[m], "MetadataFeature")
                    || !r.b.elements[m]
                        .owning_relationship
                        .is_some_and(|rel| is_a!(r.b.elements[rel], "FeatureMembership"))
                {
                    continue;
                }
                let targets = g.relations(&r.b, m, "Redefinition", "redefinedFeature");
                let name = r.b.elements[m].props.get("declaredName");
                let implicit: Vec<_> = offered
                    .iter()
                    .copied()
                    .filter(|&t| {
                        name.is_some_and(|n| n.is_string())
                            && name == r.b.elements[t].props.get("declaredName")
                    })
                    .collect();
                let target = if targets.is_empty() {
                    (implicit.len() == 1).then(|| implicit[0])
                } else {
                    (targets.len() == 1 && offered.contains(&targets[0])).then(|| targets[0])
                };
                if let Some(t) = target {
                    stack.push((m, effective_members_of(r, t).to_vec()));
                } else {
                    out.push((unit, super::rule_error(g.span(&r.b, m), "validateMetadataFeatureBody",
                        "A metadata body feature must redefine one feature of its metadata type")));
                }
                if let Some((scope, expr)) = r.b.values.get(&m).cloned() {
                    let origin = r.b.set_identity_origin(m);
                    let evaluable = super::expressions::model_level(&mut r.b, g, scope, &expr, 0);
                    r.b.identity_origin_unit = origin;
                    if evaluable == Some(false) {
                        out.push((
                            unit,
                            super::rule_error(
                                expr.span,
                                "validateMetadataFeatureBody",
                                "A metadata body value must be model-level evaluable",
                            ),
                        ));
                    }
                }
            }
        }
    }
    for (e, scope, mult) in super::user_rows(&r.b, model, r.b.multiplicities.iter(), |row| row.0) {
        let unit = r.b.unit_of_elem(e);
        for expr in mult.lower.iter().chain(std::iter::once(&mult.upper)) {
            let origin = r.b.set_identity_origin(e);
            let ts = super::expressions::types(&mut r.b, g, scope, expr, 0);
            r.b.identity_origin_unit = origin;
            if !ts.is_empty() && ts.iter().all(|&t| !is_a!(r.b.elements[t], "DataType")) {
                out.push((
                    unit,
                    super::rule_error(
                        expr.span,
                        "validateMultiplicityRangeResultTypes",
                        "A multiplicity bound must have a Natural result",
                    ),
                ));
            }
        }
    }
    let associations: Vec<_> = r
        .b
        .metadata_of
        .iter()
        .flat_map(|(&annotated, metas)| metas.iter().copied().map(move |meta| (annotated, meta)))
        .filter(|&(_, meta)| super::user_owned(&r.b, model, meta))
        .collect();
    // The library's `annotatedElement` feature, resolved once: a candidate
    // is a member whose closure reaches it. Without the library, or with
    // the name ambiguous, each closure is read by name as before.
    let annotated_element = (!associations.is_empty())
        .then(|| {
            r.b.resolve(
                0,
                &crate::json::lib_qn("Metaobjects::Metaobject::annotatedElement"),
                0,
            )
        })
        .flatten();
    for (annotated, meta) in associations {
        let unit = r.b.unit_of_elem(meta);
        let candidates: Vec<_> = g
            .effective_members(&r.b, meta)
            .into_iter()
            .filter(|&member| {
                let closure = g.closure_shared(member);
                match annotated_element {
                    Some(feature) => closure.contains(&feature),
                    None => closure
                        .iter()
                        .any(|&f| g.named(&r.b, f, "Metaobjects::Metaobject::annotatedElement")),
                }
            })
            .collect();
        // Separate subsetting features specify alternative permitted
        // metaclasses; a single feature's multiple types are conjunctive.
        let specific: Vec<_> = candidates
            .iter()
            .copied()
            .filter(|t| {
                !candidates
                    .iter()
                    .any(|other| other != t && g.closure(*other).contains(t))
            })
            .collect();
        if let Some(reflection) = r.b.reflection_metaclass(r.b.elements[annotated].ty) {
            let actual = g.context(reflection);
            let allowed: Vec<_> = specific.iter().map(|&m| g.typed(&r.b, m)).collect();
            if !allowed.is_empty()
                && allowed.iter().all(|ts| !ts.is_empty())
                && !allowed
                    .iter()
                    .any(|ts| ts.iter().all(|t| actual.contains(t)))
            {
                out.push((unit, super::rule_error(g.span(&r.b, meta), "validateMetadataFeatureAnnotatedElement",
                        "The annotated element's metaclass does not conform to annotatedElement's type")));
            }
        }
    }
    out
}

/// What `e`'s first written redefinition names — a chain's links, or a
/// named target — in source order, as an edit replacing the target
/// reads it; `None` when `e` redefines nothing.
fn redefinition_step(r: &mut ResolvedModel, e: ElementRef) -> Option<Vec<ElementRef>> {
    r.redefinition_steps(e).into_iter().next()
}

/// The feature `e` redefines as a path of features from the nearest
/// owner that redefines nothing: `e`'s own step, prefixed by the step of
/// each enclosing owner that is itself a redefinition — a nameless block
/// (`part :>> chassis { attribute :>> mass; }`) or a named one (`part
/// ch2 :>> chassis { … }`) — so both give `[chassis, mass]` from the
/// block's owner, as `attribute :>> chassis.mass` does.
fn redefinition_path(
    r: &mut ResolvedModel,
    e: ElementRef,
) -> Option<(ElementRef, Vec<ElementRef>)> {
    let mut path = redefinition_step(r, e)?;
    let mut cur = e;
    for _ in 0..8 {
        let owner = r.owner(cur)?;
        match redefinition_step(r, owner) {
            Some(step) => path.splice(0..0, step),
            None => return Some((owner, path)),
        };
        cur = owner;
    }
    None
}

/// Pushes onto `out` the inherited feature `f`, and the redefining
/// members nested in it (three levels down), whose redefinition path
/// from the inheriting type — `prefix` plus their own steps, each link
/// reduced to the feature it stands for — equals `path`.
fn inherited_bindings(
    r: &mut ResolvedModel,
    f: ElementRef,
    prefix: &[ElementRef],
    path: &[ElementRef],
    depth: usize,
    out: &mut Vec<usize>,
) {
    // (most inherited features redefine nothing: the cheap test first)
    if r.b.elements[f.0]
        .owned_relationships
        .iter()
        .all(|&rel| r.b.elements[rel].ty != "Redefinition")
    {
        return;
    }
    let Some(step) = redefinition_step(r, f) else {
        return;
    };
    let mut own: Vec<ElementRef> = prefix.to_vec();
    own.extend(step.into_iter().map(|l| r.redefinition_root(l)));
    if own == path {
        out.push(f.0);
    }
    // the members of a block, through its path (a block whose path is
    // no prefix of the one sought has none that can match)
    if depth < 3 && own.len() < path.len() && path.starts_with(&own) {
        for m in r.owned_members(f) {
            inherited_bindings(r, m, &own, path, depth + 1, out);
        }
    }
}

/// A nameless chain redefinition by its owner and chain
/// (`P::M2::chassis.mass`), for a message.
/// A nameless redefinition under its owner's qualified name, by the name
/// it takes from what it redefines: `P::Mid::x` for `attribute :>> x = 2;`
/// in `Mid`, which declares no name and so has no qualified name of its
/// own.
fn effective_display_name(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    let name = r.element_effective_name(e)?;
    let owner = r.owner(e)?;
    let owner = r.element_qualified_name(owner)?;
    Some(format!(
        "{owner}::{}",
        sysmlv2_syntax::ast::escape_name(&name)
    ))
}

fn chain_display_name(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    if r.element_name(e).is_some() {
        return None;
    }
    let links = r.redefined_chains(e).into_iter().next()?;
    let names: Vec<String> = links
        .iter()
        .map(|&l| r.element_name(l).map(str::to_string))
        .collect::<Option<_>>()?;
    let owner = r.owner(e)?;
    let owner = r.element_qualified_name(owner)?;
    Some(format!("{owner}::{}", names.join(".")))
}
