//! Namespace distinguishability over inherited members — KerML
//! `validateNamespaceDistinguishibility` (the rule name as the pinned XMI
//! spells it): every membership of a namespace must be distinguishable
//! from every other, inherited memberships included. The syntax stage
//! already checks a namespace's *owned* members against each other; this
//! pass adds the two inherited shapes for user types:
//!
//! - an owned member reusing an inherited member's name (or short name)
//!   without redefining or subsetting it — `part def Leaf :> Mid { part
//!   portions; }` against `Mid`'s `portions`;
//! - a type inheriting one name from two places at once — a usage typed by
//!   `Leaf` above inherits both `portions`, or two unrelated bases each
//!   supply a same-named feature neither redefines.
//!
//! The candidate set is the resolver's own inherited-member enumeration
//! (`Builder::inherited_bindings`, implied library bases included), whose
//! removal pass already applies KerML `removeRedefinedFeatures`. The one
//! removal that is *not* normative — a same-named usage-family member
//! shadowing an inherited one because its owner conforms — is recorded by
//! that pass as an implicit redefinition; lookup keeps honoring it (it is
//! what makes `downlinkPort` resolve unambiguously inside the subclass),
//! and this check reports it as the collision the reference validator
//! reports. Both shapes are warnings, the reference validator's severity
//! for inherited collisions (the owned-member collision the syntax stage
//! reports is an error there too).
//!
//! Equal names are legal when the two member elements' metaclasses do not
//! conform either way (KerML `Membership::isDistinguishableFrom`); the
//! check reads that from the generated metaclass hierarchy. Names are the
//! members' declared names and short names, or the effective name of an
//! unnamed redefinition (`attribute :>> x` binds `x`). Alias memberships
//! are not enumerated on either side: an owned `alias` against an
//! inherited name stays unreported here. The enumerations this pass asks
//! for stay memoized on the builder, so a long-lived host pays for them
//! once and its later inherited-member queries reuse them.
use std::{
    borrow::Cow,
    collections::{BTreeMap, HashSet},
};

use crate::{
    json::{Builder, ElementRef, ResolvedModel},
    metaclass::conforms,
    model::Model,
};
use sysmlv2_syntax::{Span, diag::Diagnostic};

const RULE: &str = "validateNamespaceDistinguishibility";

/// One inherited-name collision — the semantic check's finding, exposed
/// for repairs that spell the missing redefinition.
#[derive(Clone, Debug)]
pub struct InheritedNameCollision {
    /// The owned member reusing an inherited name, or (when `hidden` is
    /// `None`) the type inheriting one name from two members.
    pub element: ElementRef,
    /// The inherited member the owned `element` hides — the redefinition
    /// target a repair would spell.
    pub hidden: Option<ElementRef>,
    /// The colliding name (a declared name or short name).
    pub name: String,
    /// Index into [`crate::model::Model::units`] of `element`'s unit.
    pub unit: usize,
    /// The declared name of `element` as written.
    pub span: Span,
    /// The finding's text, without the rule tag.
    pub message: String,
    /// The `:>>` target spelling — `hidden`'s simple name when it alone
    /// binds the name in `element`'s namespace, its qualified name
    /// otherwise — when `element` may redefine `hidden` without tripping
    /// a checker rule a spelled redefinition is subject to: both are
    /// features and `hidden` is no variant; an end is redefined by an end
    /// (`validateRedefinitionEndConformance`); spelled directions agree or
    /// `hidden`'s is `inout` (`validateRedefinitionDirectionConformance`);
    /// `element` binds no value over a bound (non-default) value of
    /// `hidden` or its redefinition chain (`validateFeatureValueOverriding`);
    /// each user type `hidden` declares admits some type `element`
    /// declares (redefinition type-compatibility); explicit multiplicities
    /// nest (redefinition multiplicity conformance). `None` when any of
    /// these would reject the repair, when `element` hides members from
    /// unrelated bases (redefining one leaves the others), or when the
    /// target has no spelling. Hidden members along one specialization
    /// chain get the nearest as target, by qualified name: once the
    /// chain's own collisions are repaired that redefinition covers them.
    pub redefinition_target: Option<String>,
}

fn prop_str<'a>(b: &'a Builder, e: usize, key: &str) -> Option<&'a str> {
    b.elements[e].props.get(key).and_then(|a| a.as_str())
}

/// The lookup names an element binds: its declared name — or, unnamed,
/// the effective name it takes from its first redefinition or reference
/// target — and, when it differs, its declared short name (both bind in
/// the same name space).
fn declared_keys(b: &Builder, e: usize) -> impl Iterator<Item = Cow<'_, str>> {
    let name: Option<Cow<str>> = match prop_str(b, e, "declaredName") {
        Some(n) => Some(Cow::Borrowed(n)),
        None => b.effective_name(e).map(Cow::Owned),
    };
    let short = prop_str(b, e, "declaredShortName")
        .filter(|s| name.as_deref() != Some(*s))
        .map(Cow::Borrowed);
    name.into_iter().chain(short)
}

fn display_name(b: &Builder, e: usize) -> String {
    prop_str(b, e, "declaredName")
        .or_else(|| prop_str(b, e, "declaredShortName"))
        .map_or_else(|| "<unnamed>".to_string(), str::to_string)
}

/// Whether the two elements' metaclasses conform one way or the other —
/// the metaclass half of KerML `Membership::isDistinguishableFrom`.
fn overlapping(b: &Builder, x: usize, y: usize) -> bool {
    let (tx, ty) = (b.elements[x].ty, b.elements[y].ty);
    conforms(tx, ty) || conforms(ty, tx)
}

/// Whether `e` reuses an inherited name through a redefinition the
/// specification implies rather than one the modeller spells — the
/// normative implicit redefinitions the resolver's specialization index
/// does not record as `Redefinition` relationships:
/// - a parameter of a behavior or step redefines the general's parameter
///   at the same position (KerML `checkFeatureParameterRedefinition`), a
///   result parameter the general's result (`checkFeatureResultRedefinition`);
/// - an end feature redefines the general's end at the same position
///   (`checkFeatureEndRedefinition`), so `end source : P;` in an interface
///   definition legally reuses `BinaryInterface`'s end names;
/// - a case objective (SysML `checkRequirementUsageObjectiveRedefinition`),
///   a state's entry/do/exit action (`checkActionUsageStateActionRedefinition`),
///   a view rendering (`checkRenderingUsageRedefinition`) and a result
///   expression redefine the inherited member of their role;
/// - a metadata body usage `text = "…"` is an `OwnedRedefinition` of the
///   metadata definition's feature by the grammar (`MetadataBodyUsage`),
///   which the lowering spells as a same-named usage.
fn implicitly_redefines(b: &Builder, e: usize) -> bool {
    let elem = &b.elements[e];
    let owner_ty = b.owner_elem(e).map(|o| b.elements[o].ty);
    let in_behavior = owner_ty.is_some_and(|t| conforms(t, "Behavior") || conforms(t, "Step"));
    if in_behavior && elem.props.get("direction").is_some_and(|d| d.is_string()) {
        return true;
    }
    if elem.props.get("isEnd").and_then(|v| v.as_bool()) == Some(true) {
        return true;
    }
    if elem.owning_relationship.is_some_and(|r| {
        matches!(
            b.elements[r].ty,
            "ReturnParameterMembership"
                | "ObjectiveMembership"
                | "StateSubactionMembership"
                | "ViewRenderingMembership"
                | "ResultExpressionMembership"
        )
    }) {
        return true;
    }
    owner_ty.is_some_and(|t| conforms(t, "MetadataFeature"))
}

/// Whether `reuser` spells a redefinition or subsetting of `hidden` —
/// the legal ways to carry its name (lookup already removed the
/// redefined ones; the subsetting escape is the reference validator's
/// leniency). A typing (`feature f : A::f`) is neither.
fn explicitly_specializes(b: &mut Builder, reuser: usize, hidden: usize) -> bool {
    b.indexed_specialization_targets(reuser, &["Subsetting", "Redefinition"])
        .contains(&hidden)
}

/// Everything `e` transitively redefines (KerML `allRedefinedFeaturesOf`
/// without `e` itself).
fn redefinition_closure(b: &mut Builder, e: usize) -> HashSet<usize> {
    let mut closure = HashSet::new();
    let mut stack = b.indexed_redefinition_targets(e);
    while let Some(t) = stack.pop() {
        if closure.insert(t) {
            stack.extend(b.indexed_redefinition_targets(t));
        }
    }
    closure
}

/// Whether the type whose body is `scope` owns a feature directly
/// redefining something in `closure` — such a type does not inherit any
/// member whose redefinition closure meets that feature (KerML
/// `removeRedefinedFeatures`, second condition), so nothing below it does
/// either.
fn removes_at(b: &mut Builder, scope: usize, closure: &HashSet<usize>) -> bool {
    let Some(owner) = b.scope_owner(scope) else {
        return false;
    };
    b.owned_member_elems(owner, true).into_iter().any(|f| {
        b.indexed_redefinition_targets(f)
            .iter()
            .any(|t| closure.contains(t))
    })
}

/// Whether some heritage path from `scope` reaches `target` without
/// passing through a type that removes a member of `closure` on the way
/// — implied bases included; cycles end at the visited set.
fn heritage_reaches(
    b: &mut Builder,
    scope: usize,
    target: usize,
    closure: &HashSet<usize>,
) -> bool {
    let mut seen: HashSet<usize> = HashSet::from([scope]);
    let mut stack = vec![scope];
    while let Some(s) = stack.pop() {
        for base in b.base_scopes_split(s).0 {
            if base == target {
                return true;
            }
            if seen.insert(base) && !removes_at(b, base, closure) {
                stack.push(base);
            }
        }
    }
    false
}

/// Whether `dropped` never reaches `scope`'s type the normative way: KerML
/// `inheritedMemberships` is computed type by type, and a type whose owned
/// feature directly redefines a feature in an inherited member's
/// redefinition closure does not inherit that member — so a member both
/// the nearer `other` and `dropped` derive from one feature (sibling
/// redefinitions, `attribute h redefines header;` at two levels of a
/// redefinition chain) is gone at the level that spells the nearer one,
/// and at every other level that spells a sibling. Two unrelated bases
/// each redefining `Anything::self` are not that shape, and neither is a
/// diamond that also reaches `dropped`'s declaring type around every
/// removing level.
fn removed_at_nearer_level(b: &mut Builder, scope: usize, dropped: usize, other: usize) -> bool {
    let direct = b.indexed_redefinition_targets(other);
    if direct.is_empty() {
        return false;
    }
    let closure = redefinition_closure(b, dropped);
    if !direct.iter().any(|t| closure.contains(t)) {
        return false;
    }
    let Some(target) = b
        .owner_elem(dropped)
        .and_then(|o| b.elem_scope.get(&o).copied())
    else {
        return false;
    };
    !heritage_reaches(b, scope, target, &closure)
}

/// Among same-named inherited members hiding one owned member, the one
/// declared nearest — whose owner conforms to every other's — names the
/// finding; the first otherwise.
fn nearest(b: &mut Builder, candidates: &[usize]) -> usize {
    let owners: Vec<Option<usize>> = candidates.iter().map(|&c| b.owner_elem(c)).collect();
    for (i, &c) in candidates.iter().enumerate() {
        let Some(oc) = owners[i] else { continue };
        if owners
            .iter()
            .flatten()
            .all(|&o| o == oc || b.indexed_conforms(oc, o))
        {
            return c;
        }
    }
    candidates[0]
}

/// The declaring namespaces of two members, qualified when their plain
/// names coincide (`Q1::N` and `Q2::N`).
fn declaring_pair(r: &mut ResolvedModel, a: usize, b2: usize) -> (String, String) {
    let (oa, ob) = (r.b.owner_elem(a), r.b.owner_elem(b2));
    let plain = |r: &ResolvedModel, o: Option<usize>| {
        o.map_or_else(|| "<unknown>".to_string(), |o| display_name(&r.b, o))
    };
    let (mut na, mut nb) = (plain(r, oa), plain(r, ob));
    if na == nb {
        if let (Some(oa), Some(ob)) = (oa, ob) {
            if let (Some(qa), Some(qb)) = (
                r.element_qualified_name(ElementRef(oa)),
                r.element_qualified_name(ElementRef(ob)),
            ) {
                (na, nb) = (qa, qb);
            }
        }
    }
    (na, nb)
}

/// See [`InheritedNameCollision::redefinition_target`]. `simple` says the
/// hidden member's own name resolves to it alone from `element`'s
/// namespace, so the short spelling is safe.
fn redefinition_target(
    r: &mut ResolvedModel,
    element: usize,
    hidden: usize,
    simple: bool,
) -> Option<String> {
    let b = &r.b;
    if !conforms(b.elements[element].ty, "Feature") || !conforms(b.elements[hidden].ty, "Feature") {
        return None;
    }
    if b.elements[hidden]
        .owning_relationship
        .is_some_and(|rel| b.elements[rel].ty == "VariantMembership")
    {
        return None;
    }
    let flag =
        |e: usize, key: &str| b.elements[e].props.get(key).and_then(|v| v.as_bool()) == Some(true);
    if flag(hidden, "isEnd") && !flag(element, "isEnd") {
        return None;
    }
    let (from, to) = (
        prop_str(b, element, "direction"),
        prop_str(b, hidden, "direction"),
    );
    if from.is_some() && to.is_some() && from != to && to != Some("inout") {
        return None;
    }
    if b.values.contains_key(&element) {
        let mut chain = redefinition_closure(&mut r.b, hidden);
        chain.insert(hidden);
        if chain
            .iter()
            .any(|&h| r.b.values.contains_key(&h) && !r.b.default_values.contains(&h))
        {
            return None;
        }
    }
    let lib_boundary = r.b.lib_boundary;
    let mine = r.typings(ElementRef(element));
    let theirs = r.typings(ElementRef(hidden));
    for &h in &theirs {
        // Conformance to a library type may ride implied bases the
        // explicit closure cannot see; the checker skips those too.
        if h.0 < lib_boundary || mine.is_empty() {
            continue;
        }
        if !mine.iter().any(|&t| r.conforms(t, h)) {
            return None;
        }
    }
    if r.b.declares_multiplicity(element) && r.b.declares_multiplicity(hidden) {
        let (Some((lo, hi)), Some((tlo, thi))) = (
            r.declared_multiplicity(ElementRef(element)),
            r.declared_multiplicity(ElementRef(hidden)),
        ) else {
            return None;
        };
        if lo < tlo || hi > thi {
            return None;
        }
    }
    if simple {
        r.element_name(ElementRef(hidden))
            .map(sysmlv2_syntax::ast::escape_name)
            .or_else(|| r.element_qualified_name(ElementRef(hidden)))
    } else {
        r.element_qualified_name(ElementRef(hidden))
    }
}

fn span_of(b: &Builder, e: usize) -> Option<Span> {
    b.decl_spans
        .get(&e)
        .or_else(|| b.member_spans.get(&e))
        .copied()
}

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    collisions(r)
        .into_iter()
        .filter(|c| !model.is_library_unit(c.unit))
        .map(|c| (c.unit, super::rule_warning(c.span, RULE, &c.message)))
        .collect()
}

/// Every inherited-name collision among the user elements, in element
/// order — owned-member collisions of a type first, then the names it
/// inherits twice, each in name order.
pub fn collisions(r: &mut ResolvedModel) -> Vec<InheritedNameCollision> {
    let mut out = Vec::new();
    let lib_boundary = r.b.lib_boundary;
    for e in lib_boundary..r.b.explicit_len() {
        let unit = r.b.unit_of_elem(e);
        if !conforms(r.b.elements[e].ty, "Type") {
            continue;
        }
        let Some(&scope) = r.b.elem_scope.get(&e) else {
            continue;
        };
        let bindings = r.b.inherited_bindings(scope, true);
        if bindings.members.is_empty() && bindings.implicit_redefinitions.is_empty() {
            continue;
        }
        let owned = r.b.owned_member_elems(e, false);
        let owned_set: HashSet<usize> = owned.iter().copied().collect();

        // Candidate pairs, gathered under one immutable borrow of the
        // builder. Only names some *user* element declares can collide
        // reportably (a pair of library members is left alone below), so
        // library members are indexed only under those names.
        // Shape 1: `(hidden inherited member, owned member, key, whether
        // the key names nothing else in the namespace — one owned member
        // and the hidden one — so the hidden one's simple name resolves
        // to it once the redefining feature is set aside)`.
        let mut hidden: Vec<(usize, usize, Cow<str>, bool)> = Vec::new();
        // Shape 2: `(member, member, key, from the implicit-redefinition
        // record)` — both inherited; a recorded pair is oriented
        // `(dropped, shadowing)`, a by-name pair is not oriented.
        let mut pairs: Vec<(usize, usize, Cow<str>, bool)> = Vec::new();
        {
            let b = &r.b;
            let mut user_names: HashSet<Cow<str>> = HashSet::new();
            for &o in &owned {
                user_names.extend(declared_keys(b, o));
            }
            for &(m, _) in &bindings.members {
                if m >= lib_boundary {
                    user_names.extend(declared_keys(b, m));
                }
            }
            let mut by_name: BTreeMap<Cow<str>, Vec<usize>> = BTreeMap::new();
            for &(m, _) in &bindings.members {
                for key in declared_keys(b, m) {
                    if m >= lib_boundary || user_names.contains(&key) {
                        by_name.entry(key).or_default().push(m);
                    }
                }
            }
            let simple = |key: &Cow<str>, hidden: usize| {
                by_name
                    .get(key)
                    .is_none_or(|ms| ms.iter().all(|&x| x == hidden || owned_set.contains(&x)))
                    && owned
                        .iter()
                        .filter(|&&x| declared_keys(b, x).any(|k| k == *key))
                        .count()
                        == 1
            };
            for &(dropped, shadowing) in &bindings.implicit_redefinitions {
                if !overlapping(b, dropped, shadowing) {
                    continue;
                }
                let key = declared_keys(b, shadowing)
                    .find(|k| declared_keys(b, dropped).any(|d| d == *k));
                let Some(key) = key else { continue };
                if owned_set.contains(&shadowing) {
                    let simple = simple(&key, dropped);
                    hidden.push((dropped, shadowing, key, simple));
                } else if !owned_set.contains(&dropped)
                    && shadowing >= lib_boundary
                    && !implicitly_redefines(b, shadowing)
                {
                    // A library-written same-name usage is one of the
                    // implied redefinitions (result parameters, ends),
                    // spelled in units the reference validator accepts.
                    pairs.push((dropped, shadowing, key, true));
                }
            }
            for &o in &owned {
                for key in declared_keys(b, o) {
                    let Some(ms) = by_name.get(&key) else {
                        continue;
                    };
                    for &m in ms {
                        if m != o && !owned_set.contains(&m) && overlapping(b, o, m) {
                            let simple = simple(&key, m);
                            hidden.push((m, o, key.clone(), simple));
                        }
                    }
                }
            }
            for (key, ms) in &by_name {
                for (i, &a) in ms.iter().enumerate() {
                    for &b2 in &ms[i + 1..] {
                        // Two inherited ends (or parameters) of one name from
                        // unrelated bases are both positionally redefined by
                        // the type's own ends (parameters) — `interface : I
                        // connect a to b` inherits `source` from
                        // `BinaryInterface` and from `I`, and its two spelled
                        // ends redefine both. A pair of library members is not
                        // reported either: a conforming model inherits none
                        // (the library's own redefinitions see to that), and a
                        // non-conforming one (`individual def X :> anAttributeDef`,
                        // whose `self` then arrives from both `DataValue` and
                        // `Occurrence`) already carries the specialization or
                        // typing error the pair would only echo.
                        if a != b2
                            && (a >= lib_boundary || b2 >= lib_boundary)
                            && !owned_set.contains(&a)
                            && !owned_set.contains(&b2)
                            && overlapping(b, a, b2)
                            && !(implicitly_redefines(b, a) && implicitly_redefines(b, b2))
                        {
                            pairs.push((a, b2, key.clone(), false));
                        }
                    }
                }
            }
        }
        if hidden.is_empty() && pairs.is_empty() {
            continue;
        }
        let hidden: Vec<(usize, usize, String, bool)> = hidden
            .into_iter()
            .map(|(m, o, k, simple)| (m, o, k.into_owned(), simple))
            .collect();
        let mut pairs: Vec<(usize, usize, String, bool)> = pairs
            .into_iter()
            .map(|(a, b2, k, oriented)| (a, b2, k.into_owned(), oriented))
            .collect();
        pairs.sort_by(|x, y| x.2.cmp(&y.2));
        // One report per (namespace, name): the owned shape first, then
        // the inherited one, both in name order.
        let mut reported: HashSet<String> = HashSet::new();

        let mut by_owned: BTreeMap<(String, usize), (Vec<usize>, bool)> = BTreeMap::new();
        for (m, o, key, simple) in hidden {
            if !implicitly_redefines(&r.b, o) && !explicitly_specializes(&mut r.b, o, m) {
                let entry = by_owned.entry((key, o)).or_insert((Vec::new(), simple));
                entry.0.push(m);
                entry.1 &= simple;
            }
        }
        // A member colliding under two of its names (`<a> b` against both
        // `a` and `b`) would need two redefinitions in one fix; none is
        // offered, the findings stand.
        let mut keys_per_owned: BTreeMap<usize, usize> = BTreeMap::new();
        for (_, o) in by_owned.keys() {
            *keys_per_owned.entry(*o).or_default() += 1;
        }
        for ((name, o), (ms, simple)) in by_owned {
            if reported.contains(&name) {
                continue;
            }
            let Some(span) = span_of(&r.b, o) else {
                continue;
            };
            reported.insert(name.clone());
            let near = nearest(&mut r.b, &ms);
            let from = r.b.owner_elem(near).map_or_else(
                || "<unknown>".to_string(),
                |owner| display_name(&r.b, owner),
            );
            let one_chain = keys_per_owned[&o] == 1
                && ms.iter().all(|&m| {
                    m == near
                        || match (r.b.owner_elem(near), r.b.owner_elem(m)) {
                            (Some(a), Some(b)) => r.conforms(ElementRef(a), ElementRef(b)),
                            _ => false,
                        }
                });
            let redefinition_target = one_chain
                .then(|| redefinition_target(r, o, near, simple && ms.len() == 1))
                .flatten();
            let hint = if !conforms(r.b.elements[o].ty, "Feature") {
                "rename it"
            } else if redefinition_target.is_some() {
                "redefine it (`:>>`) or rename it"
            } else {
                "rename it, or redefine it (`:>>`) with a conforming declaration"
            };
            out.push(InheritedNameCollision {
                element: ElementRef(o),
                hidden: Some(ElementRef(near)),
                name: name.clone(),
                unit,
                span,
                message: format!(
                    "`{name}` duplicates the inherited member name from `{from}` — {hint}"
                ),
                redefinition_target,
            });
        }

        let Some(span) = span_of(&r.b, e) else {
            continue;
        };
        for (a, b2, name, oriented) in pairs {
            if reported.contains(&name) {
                continue;
            }
            // A recorded pair is `(dropped, shadowing)`; a by-name pair
            // may be either way round, so both orientations are tried.
            let cleared = explicitly_specializes(&mut r.b, b2, a)
                || removed_at_nearer_level(&mut r.b, scope, a, b2)
                || (!oriented
                    && (explicitly_specializes(&mut r.b, a, b2)
                        || removed_at_nearer_level(&mut r.b, scope, b2, a)));
            if cleared {
                continue;
            }
            reported.insert(name.clone());
            let (mut na, mut nb) = declaring_pair(r, a, b2);
            if na > nb {
                std::mem::swap(&mut na, &mut nb);
            }
            out.push(InheritedNameCollision {
                element: ElementRef(e),
                hidden: None,
                name: name.clone(),
                unit,
                span,
                message: format!(
                    "`{name}` is inherited from both `{na}` and `{nb}` — the two member \
                     names are indistinguishable"
                ),
                redefinition_target: None,
            });
        }
    }
    out
}
