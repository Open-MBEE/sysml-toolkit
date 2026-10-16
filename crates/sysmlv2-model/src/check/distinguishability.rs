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
use crate::metaclass::is_a;
use std::{borrow::Cow, collections::BTreeMap, sync::Arc};

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
    /// the inherited direction is `inout` and this feature is directed.
    /// Conjugation is included; incomplete direction evidence omits the repair;
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
    let (declared, short) = b.elements[e].props.declared_names();
    let name = declared.or(short).map(Cow::Borrowed);
    let short = short
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
/// specification implies rather than one the modeller spells:
/// - a parameter, result or end redefines the general's by position
///   (`Builder::redefines_by_position`) — which inherited member that is
///   depends on the position, not the name: [`implicitly_redefines_member`]
///   tells whether a given one is it;
/// - a case objective (SysML `checkRequirementUsageObjectiveRedefinition`),
///   a state's entry/do/exit action (`checkActionUsageStateActionRedefinition`),
///   a view rendering (`checkRenderingUsageRedefinition`) and a result
///   expression redefine the inherited member of their role;
/// - a metadata body usage `text = "…"` is an `OwnedRedefinition` of the
///   metadata definition's feature by the grammar (`MetadataBodyUsage`),
///   which the lowering spells as a same-named usage.
fn implicitly_redefines(b: &Builder, e: usize) -> bool {
    if b.redefines_by_position(e) {
        return true;
    }
    let elem = &b.elements[e];
    if elem.owning_relationship.is_some_and(|r| {
        matches!(
            b.elements[r].ty,
            "ObjectiveMembership"
                | "StateSubactionMembership"
                | "ViewRenderingMembership"
                | "ResultExpressionMembership"
        )
    }) {
        return true;
    }
    b.owner_elem(e)
        .is_some_and(|o| is_a!(b.elements[o], "MetadataFeature"))
}

/// [`implicitly_redefines`] with a memo across one check: the question is
/// asked about the same inherited members for every type that inherits them.
fn implicitly_redefines_memo(
    b: &Builder,
    e: usize,
    memo: &mut crate::layered::IdMap<usize, bool>,
) -> bool {
    if let Some(&answer) = memo.get(&e) {
        return answer;
    }
    let answer = implicitly_redefines(b, e);
    memo.insert(e, answer);
    answer
}

/// Whether `e`, an owned member of `owner`, redefines the inherited member
/// `hidden` by implication. A parameter, result or end redefines what its position
/// pairs it with, directly or through what that redefines: `in b;` as the
/// only parameter under `Partial :> Diff { in a; in b; }` redefines `a`,
/// and its reuse of the name `b` is the collision the rule reports. The
/// other implied kinds ([`implicitly_redefines`]) carry their role's one
/// inherited member.
fn implicitly_redefines_member(
    b: &mut Builder,
    owner: usize,
    e: usize,
    hidden: usize,
    memo: &mut crate::layered::IdMap<usize, bool>,
) -> bool {
    if !b.redefines_by_position(e) {
        return implicitly_redefines_memo(b, e, memo);
    }
    let mut closure: crate::layered::IdSet<usize> = Default::default();
    let mut stack = b.indexed_redefinition_targets_shared(e).to_vec();
    stack.extend(b.positional_redefinition_targets(e, owner));
    while let Some(t) = stack.pop() {
        if t == hidden {
            return true;
        }
        if closure.insert(t) {
            stack.extend(b.indexed_redefinition_targets_shared(t).iter().copied());
            if let Some(o) = b.owner_elem(t) {
                stack.extend(b.positional_redefinition_targets(t, o));
            }
        }
    }
    false
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
fn redefinition_closure(b: &mut Builder, e: usize) -> crate::layered::IdSet<usize> {
    let mut closure = crate::layered::IdSet::default();
    let mut stack = b.indexed_redefinition_targets_shared(e).to_vec();
    while let Some(t) = stack.pop() {
        if closure.insert(t) {
            stack.extend(b.indexed_redefinition_targets_shared(t).iter().copied());
        }
    }
    closure
}

/// Whether the type whose body is `scope` owns a feature directly
/// redefining something in `closure` — such a type does not inherit any
/// member whose redefinition closure meets that feature (KerML
/// `removeRedefinedFeatures`, second condition), so nothing below it does
/// either.
fn removes_at(b: &mut Builder, scope: usize, closure: &crate::layered::IdSet<usize>) -> bool {
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
    closure: &crate::layered::IdSet<usize>,
) -> bool {
    let mut seen: crate::layered::IdSet<usize> = Default::default();
    seen.insert(scope);
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
    facts: &super::facts::Facts,
    directions: &mut super::directions::RedefinitionDirections,
) -> Option<String> {
    let b = &r.b;
    if !is_a!(b.elements[element], "Feature") || !is_a!(b.elements[hidden], "Feature") {
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
    if directions.conformance(&mut r.b, facts, element, hidden) != Some(true) {
        return None;
    }
    let b = &r.b;
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
    let all = r.b.lib_boundary..r.b.explicit_len();
    validate_in(r, model, all)
}

/// [`validate`] for the user elements in `rows`.
pub(super) fn validate_in(
    r: &mut ResolvedModel,
    model: &Model,
    rows: std::ops::Range<usize>,
) -> Vec<(usize, Diagnostic)> {
    collisions_in(r, rows)
        .into_iter()
        .filter(|c| !model.is_library_unit(c.unit))
        .map(|c| (c.unit, super::rule_warning(c.span, RULE, &c.message)))
        .collect()
}

/// Whether an inherited pair under one name is no collision: the one
/// explicitly specializes the other, or a nearer level removed one of them.
/// A recorded pair is `(dropped, shadowing)`; a by-name pair may be either
/// way round, so both orientations are tried.
fn cleared_pair(r: &mut ResolvedModel, scope: usize, a: usize, b2: usize, oriented: bool) -> bool {
    explicitly_specializes(&mut r.b, b2, a)
        || removed_at_nearer_level(&mut r.b, scope, a, b2)
        || (!oriented
            && (explicitly_specializes(&mut r.b, a, b2)
                || removed_at_nearer_level(&mut r.b, scope, b2, a)))
}

/// Every inherited-name collision among the user elements, in element
/// order — owned-member collisions of a type first, then the names it
/// inherits twice, each in name order.
/// The inherited-twice collisions of one reduction of inherited members
/// (one `Arc` of them, shared by every type with the same heritage whose
/// own features leave it alone): the names of the inherited members, hashed,
/// and the pairs the scan reports, in report order with their declaring
/// pair's names. A type whose owned members' names meet none of the
/// inherited names reports the same pairs, at its own span.
struct SharedScan {
    names: crate::layered::IdSet<u64>,
    pairs: Vec<(String, usize, usize, String, String)>,
}

/// FNV-1a over a name, for [`SharedScan::names`]; a chance collision only
/// makes a type scan for itself.
fn name_hash(name: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in name.bytes() {
        h ^= u64::from(byte);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

pub fn collisions(r: &mut ResolvedModel) -> Vec<InheritedNameCollision> {
    let all = r.b.lib_boundary..r.b.explicit_len();
    collisions_in(r, all)
}

/// [`collisions`] among the user elements in `rows`.
fn collisions_in(
    r: &mut ResolvedModel,
    rows: std::ops::Range<usize>,
) -> Vec<InheritedNameCollision> {
    let mut out = Vec::new();
    // `None` while one type with the reduction has been seen: hashing the
    // inherited names pays only when a second type with it comes.
    let mut shared: crate::layered::IdMap<usize, Option<Arc<SharedScan>>> = Default::default();
    let mut direction_facts = None;
    let mut directions = super::directions::RedefinitionDirections::default();
    // Whether a member redefines by implication is a property of the member
    // alone, asked for every type that inherits it.
    let mut implicit: crate::layered::IdMap<usize, bool> = Default::default();
    let lib_boundary = r.b.lib_boundary;
    for e in rows {
        let unit = r.b.unit_of_elem(e);
        if !is_a!(r.b.elements[e], "Type") {
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
        // The reduction's scan, when another type with it scanned already
        // and this type's owned names meet none of the inherited ones.
        let shared_key = Arc::as_ptr(&bindings) as usize;
        let seen = shared.get(&shared_key).cloned();
        let scan = seen.clone().flatten();
        // The owned names matter only once a second type with the reduction
        // is seen (the first only marks the reduction seen).
        let owned_hashes: Vec<u64> = if seen.is_some() {
            owned
                .iter()
                .flat_map(|&o| {
                    declared_keys(&r.b, o)
                        .map(|k| name_hash(&k))
                        .collect::<Vec<_>>()
                })
                .collect()
        } else {
            Vec::new()
        };
        let disjoint_from =
            |scan: &SharedScan| owned_hashes.iter().all(|h| !scan.names.contains(h));
        if let Some(scan) = scan.as_deref().filter(|scan| disjoint_from(scan)) {
            if let Some(span) = span_of(&r.b, e) {
                for (name, _, _, na, nb) in &scan.pairs {
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
            continue;
        }
        if seen.is_none() {
            shared.insert(shared_key, None);
        }
        // Whether this type's scan can be kept for the others with its
        // reduction: its owned names meet no inherited name (so nothing it
        // owns hides or shadows one), and the reduction is a kept one.
        let inherited_hashes: Option<crate::layered::IdSet<u64>> =
            (seen.is_some() && scan.is_none() && Arc::strong_count(&bindings) > 1).then(|| {
                bindings
                    .members
                    .iter()
                    .flat_map(|&(m, _)| {
                        declared_keys(&r.b, m)
                            .map(|k| name_hash(&k))
                            .collect::<Vec<_>>()
                    })
                    .collect()
            });
        let keep_scan = inherited_hashes
            .as_ref()
            .is_some_and(|names| owned_hashes.iter().all(|h| !names.contains(h)));
        let mut found_pairs: Vec<(String, usize, usize, String, String)> = Vec::new();
        let owned_set: crate::layered::IdSet<usize> = owned.iter().copied().collect();

        // Candidate pairs, gathered under one immutable borrow of the
        // builder. Only names some *user* element declares can collide
        // reportably (a pair of library members is left alone below), so
        // library members are indexed only under those names.
        // Shape 1: `(hidden inherited member, owned member, key, whether
        // the key names nothing else in the namespace — one owned member
        // and the hidden one — so the hidden one's simple name resolves
        // to it once the redefining feature is set aside)`.
        let mut hidden: Vec<(usize, usize, Cow<str>, bool)> = Vec::new();
        // Shape 2: `(member, member)` under a key — both inherited. A
        // recorded pair is oriented `(dropped, shadowing)`; a by-name pair
        // is not, and is found below, lazily, in the order the report
        // reads them: a key's candidates in the members' order, owned
        // members left out (a pair never includes one), and only keys
        // that can yield a pair at all (one with a user member and one
        // that does not redefine by implication) — a view exposing
        // thousands of metadata bodies inherits as many same-named
        // features that all redefine by implication, and pairing them
        // would cost millions of tests for no report.
        let mut recorded: BTreeMap<Cow<str>, Vec<(usize, usize)>> = BTreeMap::new();
        let mut candidates: BTreeMap<Cow<str>, Vec<usize>> = BTreeMap::new();
        {
            let b = &r.b;
            let mut user_names: crate::layered::IdSet<Cow<str>> = Default::default();
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
                    && !implicitly_redefines_memo(b, shadowing, &mut implicit)
                {
                    // A library-written same-name usage is one of the
                    // implied redefinitions (result parameters, ends),
                    // spelled in units the reference validator accepts.
                    recorded.entry(key).or_default().push((dropped, shadowing));
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
                let members: Vec<usize> = ms
                    .iter()
                    .copied()
                    .filter(|m| !owned_set.contains(m))
                    .collect();
                if members.len() < 2
                    || !members.iter().any(|&m| m >= lib_boundary)
                    || members
                        .iter()
                        .all(|&m| implicitly_redefines_memo(b, m, &mut implicit))
                {
                    continue;
                }
                candidates.insert(key.clone(), members);
            }
        }
        if hidden.is_empty() && recorded.is_empty() && candidates.is_empty() {
            if keep_scan {
                shared.insert(
                    shared_key,
                    Some(Arc::new(SharedScan {
                        names: inherited_hashes.unwrap_or_default(),
                        pairs: Vec::new(),
                    })),
                );
            }
            continue;
        }
        let hidden: Vec<(usize, usize, String, bool)> = hidden
            .into_iter()
            .map(|(m, o, k, simple)| (m, o, k.into_owned(), simple))
            .collect();
        let recorded: BTreeMap<String, Vec<(usize, usize)>> = recorded
            .into_iter()
            .map(|(k, pairs)| (k.into_owned(), pairs))
            .collect();
        let candidates: BTreeMap<String, Vec<usize>> = candidates
            .into_iter()
            .map(|(k, members)| (k.into_owned(), members))
            .collect();
        // One report per (namespace, name): the owned shape first, then
        // the inherited one, both in name order.
        let mut reported: crate::layered::IdSet<String> = Default::default();

        let mut by_owned: BTreeMap<(String, usize), (Vec<usize>, bool)> = BTreeMap::new();
        for (m, o, key, simple) in hidden {
            if !implicitly_redefines_member(&mut r.b, e, o, m, &mut implicit)
                && !explicitly_specializes(&mut r.b, o, m)
            {
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
            let redefinition_target = if one_chain {
                let facts = Arc::clone(direction_facts.get_or_insert_with(|| r.b.facts()));
                redefinition_target(r, o, near, simple && ms.len() == 1, &facts, &mut directions)
            } else {
                None
            };
            let hint = if !is_a!(r.b.elements[o], "Feature") {
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
        let keys: std::collections::BTreeSet<&String> =
            recorded.keys().chain(candidates.keys()).collect();
        for name in keys {
            if reported.contains(name) {
                continue;
            }
            // The first pair the report keeps: a recorded one first, then
            // the by-name candidates in order, each tried as the report
            // reads it.
            let mut found = None;
            for &(a, b2) in recorded.get(name).into_iter().flatten() {
                if !cleared_pair(r, scope, a, b2, true) {
                    found = Some((a, b2));
                    break;
                }
            }
            if found.is_none() {
                if let Some(members) = candidates.get(name) {
                    'search: for (i, &a) in members.iter().enumerate() {
                        for &b2 in &members[i + 1..] {
                            let qualifies = {
                                let b = &r.b;
                                a != b2
                                    && (a >= lib_boundary || b2 >= lib_boundary)
                                    && overlapping(b, a, b2)
                                    && !(implicitly_redefines_memo(b, a, &mut implicit)
                                        && implicitly_redefines_memo(b, b2, &mut implicit))
                            };
                            if qualifies && !cleared_pair(r, scope, a, b2, false) {
                                found = Some((a, b2));
                                break 'search;
                            }
                        }
                    }
                }
            }
            let Some((a, b2)) = found else {
                continue;
            };
            let name = name.clone();
            reported.insert(name.clone());
            let (mut na, mut nb) = declaring_pair(r, a, b2);
            if na > nb {
                std::mem::swap(&mut na, &mut nb);
            }
            if keep_scan {
                found_pairs.push((name.clone(), a, b2, na.clone(), nb.clone()));
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
        if keep_scan {
            shared.insert(
                shared_key,
                Some(Arc::new(SharedScan {
                    names: inherited_hashes.unwrap_or_default(),
                    pairs: found_pairs,
                })),
            );
        }
    }
    out
}
