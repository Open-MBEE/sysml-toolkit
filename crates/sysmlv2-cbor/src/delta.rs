//! **Delta payloads** — element-granular change sets over the
//! compact form, matching the Systems Modeling API's commit model
//! (identity + whole payload per change; null payload = delete; no
//! property-level diffing).
//!
//! A delta names its base by **claims + proof**: an optional map of
//! spec-canonical version identifiers (project/commit UUIDs — opaque
//! routing hints), and a mandatory content digest the receiver
//! recomputes from the base it holds. Digests and diffs operate on the
//! **delta-canonical element order** (ownership preorder,
//! [`delta_canonical`]), so they are independent of emission order:
//! the same model state digests identically no matter who produced the
//! payload.
//!
//! Two identity modes (header flag):
//! - **strict/indexed** — change targets and base references are
//!   indices into the digest-pinned canonical base order. Smallest
//!   bytes; the digest gate is *hard* (an index into a different base
//!   would silently edit the wrong element).
//! - **portable/id-keyed** — change targets are raw element ids and
//!   base references travel as externals; best-effort application to a
//!   divergent base is possible via [`apply_delta_cbor_lenient`],
//!   which reports no-op deletes, upserted updates, and replaced
//!   creates instead of failing.
//!
//! Wire layout: `array(6 + 1 per section flag)` of header, base
//! section (`[base digest, result digest, claims]`), base element
//! count, external table, created-element id table (or, elided, its
//! count + exception map + id digest), change records `[identity,
//! payload]` (identity: base index / id bytes / null for create;
//! payload: element record, `map` field patch against the base
//! element (strict only), or null for delete), the
//! owner-exception section (flag 0x20: change-record ordinal
//! → absent-key bits — shipped element records elide backpointers
//! matching derivation over the canonical target, and the applier
//! re-derives them over the canonicalized applied state; patches
//! replay owner changes as explicit ops and base copies are never
//! touched), and the units section (flag 0x10).

use crate::cbor::{Head, Reader, Writer};
use crate::decode::{Tables, gate_flags, read_element_body, read_units, read_uuid_table};
use crate::encode::{Interner, elems_of, table_set, write_element};
use crate::{Error, ErrorKind};
use serde_json::Value;
use std::collections::{HashMap, HashSet};
use uuid::Uuid;

/// Header flag marking a delta payload.
pub const FLAG_DELTA: u8 = 4;
/// Header flag selecting the portable (id-keyed) identity mode.
pub const FLAG_DELTA_PORTABLE: u8 = 8;
/// Patch opcodes: field present with a value / field absent /
/// list splice (`[at, del, [items…]]`).
pub(crate) const OP_SET: u64 = 0;
pub(crate) const OP_UNSET: u64 = 1;
pub(crate) const OP_SPLICE: u64 = 2;

/// A spec-canonical version identifier carried as an opaque claim
/// (e.g. key 0 = project id, 1 = commit id, 2 = a service URI).
///
/// Non-exhaustive: the wire may learn further claim shapes.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Claim {
    Id(Uuid),
    Text(String),
}

/// Delta encoding options. Build one from [`DeltaOptions::new`] (or
/// [`Default`]) and the `with_*` setters; the fields stay readable and
/// assignable, but the struct is non-exhaustive, so later options
/// never break a caller that spelled its own literal.
#[derive(Default)]
#[non_exhaustive]
pub struct DeltaOptions {
    /// Id-keyed identities and external base references — larger, but
    /// applicable best-effort to a divergent base.
    pub portable: bool,
    /// Version-name claims, routing hints only (the digest is the
    /// proof). Keys must be unique.
    pub claims: Vec<(u64, Claim)>,
    /// The **target's** unit structure — (index into the target array
    /// as passed, source path), the same shape
    /// [`to_compact_cbor_with_units`](crate::to_compact_cbor_with_units)
    /// takes. Non-empty ⇒ the payload carries a units section
    /// (`FLAG_UNIT_PATHS`) spelled in result-canonical indices, so
    /// file adds/renames/deletes travel with the delta (a rename-only
    /// change is a legal delta: empty change list, new units). Strict
    /// identity only — result indices are exact under the digest gate,
    /// which a divergent portable apply cannot promise.
    pub units: Vec<(usize, String)>,
}

impl DeltaOptions {
    /// Strict identities, no claims, no units.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set [`Self::portable`].
    #[must_use]
    pub fn with_portable(mut self, portable: bool) -> Self {
        self.portable = portable;
        self
    }

    /// Set [`Self::claims`].
    #[must_use]
    pub fn with_claims(mut self, claims: Vec<(u64, Claim)>) -> Self {
        self.claims = claims;
        self
    }

    /// Set [`Self::units`].
    #[must_use]
    pub fn with_units(mut self, units: Vec<(usize, String)>) -> Self {
        self.units = units;
        self
    }
}

fn delta_ns() -> Uuid {
    Uuid::new_v5(&Uuid::NAMESPACE_URL, b"sysmlv2-cbor:delta-base")
}

/// External-name resolver for id derivation (`IDS.md`).
type Resolver<'a> = &'a dyn Fn(&str) -> Option<String>;

/// Elision plan for the created ids: the exception map (created
/// ordinal → id) and the recovered-id integrity digest.
type Elision = (Vec<(u64, Uuid)>, Uuid);

fn parse_uuid(s: &str) -> Result<Uuid, Error> {
    Uuid::try_parse(s).map_err(|_| Error::new(format!("invalid UUID `{s}`")))
}

/// Reference-list property → in-payload target indices, in order.
fn targets(index: &HashMap<&str, usize>, e: &Value, key: &str) -> Vec<usize> {
    match e.get(key) {
        Some(Value::Array(a)) => a
            .iter()
            .filter_map(|v| v.get("@id").and_then(Value::as_str))
            .filter_map(|s| index.get(s).copied())
            .collect(),
        _ => Vec::new(),
    }
}

/// The delta-canonical element order: ownership preorder from each
/// root (roots in payload order; a relationship's owned elements come
/// before its own owned relationships), elements unreachable from any
/// root appended in payload order. Emission-order-independent — the
/// footing for [`state_digest`] and every delta index space.
pub fn delta_canonical(compact: &Value) -> Result<Value, Error> {
    Ok(Value::Array(
        canonical_views(compact)?.into_iter().cloned().collect(),
    ))
}

/// The payload's elements in delta-canonical order, borrowed. Digests,
/// diffs and applies all walk these views, so canonicalizing a model
/// costs a vector of pointers rather than a copy of it.
pub(crate) fn canonical_views(compact: &Value) -> Result<Vec<&Value>, Error> {
    let arr = compact
        .as_array()
        .ok_or_else(|| Error::new("compact payload is a flat element array"))?;
    Ok(canonical_order(arr)?.into_iter().map(|i| &arr[i]).collect())
}

/// [`delta_canonical`] for a payload we already own: the elements move
/// into canonical order instead of being copied into it.
fn canonical_owned(applied: Value) -> Result<Value, Error> {
    let Value::Array(arr) = applied else {
        return Err(Error::new("compact payload is a flat element array"));
    };
    let order = canonical_order(&arr)?;
    let mut slots: Vec<Option<Value>> = arr.into_iter().map(Some).collect();
    Ok(Value::Array(
        order
            .into_iter()
            .map(|i| {
                slots[i]
                    .take()
                    .expect("the canonical order lists each element once")
            })
            .collect(),
    ))
}

/// Borrowed views over an array that is already in canonical order.
fn views(arr: &[Value]) -> Vec<&Value> {
    arr.iter().collect()
}

/// The delta-canonical order as a permutation of the payload's own
/// positions — the shape [`delta_canonical`] materializes.
fn canonical_order(arr: &[Value]) -> Result<Vec<usize>, Error> {
    let n = arr.len();
    let mut index: HashMap<&str, usize> = HashMap::with_capacity(n);
    for (i, e) in arr.iter().enumerate() {
        let id = e
            .get("@id")
            .and_then(Value::as_str)
            .ok_or_else(|| Error::new(format!("element {i} has a string @id")))?;
        index.insert(id, i);
    }
    let mut owned = vec![false; n];
    for e in arr {
        for k in ["ownedRelationship", "ownedRelatedElement"] {
            for t in targets(&index, e, k) {
                owned[t] = true;
            }
        }
    }
    let mut order: Vec<usize> = Vec::with_capacity(n);
    let mut visited = vec![false; n];
    let mut stack: Vec<usize> = (0..n).rev().filter(|&i| !owned[i]).collect();
    while let Some(i) = stack.pop() {
        if visited[i] {
            continue;
        }
        visited[i] = true;
        order.push(i);
        let kids = targets(&index, &arr[i], "ownedRelatedElement");
        let rels = targets(&index, &arr[i], "ownedRelationship");
        // Preorder: kids before the relationship's own relationships;
        // reversed pushes pop in declaration order.
        for &c in rels.iter().rev().chain(kids.iter().rev()) {
            if !visited[c] {
                stack.push(c);
            }
        }
    }
    for (i, seen) in visited.iter().enumerate() {
        if !seen {
            order.push(i);
        }
    }
    Ok(order)
}

/// Content digest of a model state: `uuid5` over the canonical compact
/// CBOR bytes of the delta-canonical order. Emission-order- and
/// transport-independent; [`empty_base_digest`] is its fixed point for
/// the empty model (the API's "first commit" base).
pub fn state_digest(compact: &Value) -> Result<Uuid, Error> {
    digest_of_canonical(&canonical_views(compact)?)
}

fn digest_of_canonical(canon: &[&Value]) -> Result<Uuid, Error> {
    // The digest space canonicalizes with owners spelled — pinned
    // independently of wire-format elision, so digests recorded
    // before the owner-elision flag existed stay valid forever.
    Ok(Uuid::new_v5(
        &delta_ns(),
        &crate::encode::to_compact_cbor_canonical(canon)?,
    ))
}

/// The recognizable digest of the empty base.
///
/// # Panics
/// Never in practice: the empty element array always encodes.
#[must_use]
pub fn empty_base_digest() -> Uuid {
    state_digest(&Value::Array(Vec::new())).expect("empty model encodes")
}

/// Rebase `target`'s element ids onto `base` before diffing: a target
/// element whose ownership path (the IDS.md segment chain,
/// `sysmlv2_model::ids::segment_paths`) matches a base element's
/// adopts that element's id, so unchanged elements coincide by
/// identity even when the two payloads assigned ids independently
/// (different unit names, single- vs multi-unit builds, foreign
/// producers — the id scheme seeds every chain at the unit root, so
/// separately derived payloads can share *zero* ids while agreeing on
/// all structure). A second pass order-aligns the children the exact
/// pass left unpaired under each paired parent (metaclass-gated,
/// recursing through aligned subtrees), so an inserted or deleted
/// sibling does not churn every ordinal-chained sibling after it.
/// Unmatched elements keep their ids; every in-payload reference is
/// rewritten. Documents (roots) pair by first member name,
/// positionally where unnamed or ambiguous.
///
/// Not for same-session diffs: session identity survives moves, which
/// path matching cannot see — diff those payloads as they are.
///
/// # Panics
/// If an element of either payload has no string `@id`. Id derivation
/// runs first and refuses such a payload, so a `Value` that reached
/// this point already carries them.
pub fn rebase_ids(base: &Value, target: &Value) -> Result<Value, Error> {
    fn array(v: &Value) -> Result<&Vec<Value>, Error> {
        v.as_array()
            .ok_or_else(|| Error::new("compact payload is a flat element array"))
    }
    let base_arr = array(base)?;
    let mut out = array(target)?.clone();
    let none = |_: &str| None;
    let base_paths = sysmlv2_model::ids::segment_paths(base, &none).map_err(Error::new)?;
    let target_paths = sysmlv2_model::ids::segment_paths(target, &none).map_err(Error::new)?;

    // Roots pair by their first member name — the payload index means
    // nothing across producers — and leftovers pair in payload order.
    let roots = |paths: &[Option<(usize, String)>]| -> Vec<usize> {
        paths
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p {
                Some((r, s)) if *r == i && s.is_empty() => Some(i),
                _ => None,
            })
            .collect()
    };
    let first_member_name = |arr: &[Value], root: usize| -> Option<String> {
        let index: HashMap<&str, usize> = arr
            .iter()
            .enumerate()
            .filter_map(|(i, e)| e["@id"].as_str().map(|s| (s, i)))
            .collect();
        for rel in targets(&index, &arr[root], "ownedRelationship") {
            let named = |e: &Value, keys: [&str; 2]| {
                keys.iter()
                    .find_map(|k| e.get(k).and_then(Value::as_str))
                    .map(str::to_owned)
            };
            if let Some(n) = named(&arr[rel], ["memberName", "memberShortName"]) {
                return Some(n);
            }
            for kid in targets(&index, &arr[rel], "ownedRelatedElement") {
                if let Some(n) = named(&arr[kid], ["declaredName", "declaredShortName"]) {
                    return Some(n);
                }
            }
        }
        None
    };
    let keyed = |arr: &[Value], roots: &[usize]| -> HashMap<String, usize> {
        let mut counts: HashMap<String, usize> = HashMap::new();
        let keys: Vec<Option<String>> = roots.iter().map(|&r| first_member_name(arr, r)).collect();
        for k in keys.iter().flatten() {
            *counts.entry(k.clone()).or_default() += 1;
        }
        roots
            .iter()
            .zip(keys)
            .filter_map(|(&r, k)| k.filter(|k| counts[k] == 1).map(|k| (k, r)))
            .collect()
    };
    let (base_roots, target_roots) = (roots(&base_paths), roots(&target_paths));
    let base_keys = keyed(base_arr, &base_roots);
    let target_keys = keyed(&out, &target_roots);
    let mut pair: HashMap<usize, usize> = HashMap::new();
    let mut base_used: HashSet<usize> = HashSet::new();
    for (k, &t) in &target_keys {
        if let Some(&b) = base_keys.get(k) {
            pair.insert(t, b);
            base_used.insert(b);
        }
    }
    let mut base_free = base_roots.iter().filter(|b| !base_used.contains(b));
    for &t in &target_roots {
        if let std::collections::hash_map::Entry::Vacant(slot) = pair.entry(t) {
            if let Some(&b) = base_free.next() {
                slot.insert(b);
            }
        }
    }

    let base_at: HashMap<(usize, &str), usize> = base_paths
        .iter()
        .enumerate()
        .filter_map(|(i, p)| p.as_ref().map(|(r, s)| ((*r, s.as_str()), i)))
        .collect();
    let mut remap: HashMap<String, String> = HashMap::new();
    let mut pair_elem: HashMap<usize, usize> = HashMap::new();
    let mut base_paired: HashSet<usize> = HashSet::new();
    let adopt = |t: usize,
                 b: usize,
                 out: &[Value],
                 remap: &mut HashMap<String, String>,
                 pair_elem: &mut HashMap<usize, usize>,
                 base_paired: &mut HashSet<usize>| {
        pair_elem.insert(t, b);
        base_paired.insert(b);
        let (old, new) = (
            out[t]["@id"].as_str().unwrap(),
            base_arr[b]["@id"].as_str().unwrap(),
        );
        if old != new {
            remap.insert(old.to_owned(), new.to_owned());
        }
    };
    for (i, p) in target_paths.iter().enumerate() {
        let Some((r, s)) = p else { continue };
        let Some(&br) = pair.get(r) else { continue };
        let Some(&b) = base_at.get(&(br, s.as_str())) else {
            continue;
        };
        adopt(i, b, &out, &mut remap, &mut pair_elem, &mut base_paired);
    }

    // Ordinal-shift alignment: the id chain includes the membership
    // ordinal for unnamed members, so deleting or inserting one
    // sibling re-derives every later unnamed sibling in that body —
    // structurally unchanged elements the exact pass cannot pair,
    // which then churn as delete + create. Within each paired parent,
    // the children both passes left unpaired align in order, and every
    // aligned pair recurses, so a shifted run pairs wholesale. A pair
    // must agree on metaclass, own name, and — for relationships — the
    // first owned member's metaclass and name: renames and
    // replacements stay distinct elements (their delete + create says
    // what happened), only genuinely same-shaped shifted siblings
    // re-coincide. Identity pairing only decides the
    // update-vs-delete/create shape of the delta — the result state is
    // digest-gated regardless.
    let base_index: HashMap<&str, usize> = base_arr
        .iter()
        .enumerate()
        .filter_map(|(i, e)| e["@id"].as_str().map(|s| (s, i)))
        .collect();
    let target_index: HashMap<&str, usize> = out
        .iter()
        .enumerate()
        .filter_map(|(i, e)| e["@id"].as_str().map(|s| (s, i)))
        .collect();
    let children = |arr: &[Value], index: &HashMap<&str, usize>, i: usize| -> Vec<usize> {
        let mut c = targets(index, &arr[i], "ownedRelationship");
        c.extend(targets(index, &arr[i], "ownedRelatedElement"));
        c
    };
    fn element_name(e: &Value) -> Option<&str> {
        [
            "declaredName",
            "declaredShortName",
            "memberName",
            "memberShortName",
        ]
        .iter()
        .find_map(|k| e.get(*k).and_then(Value::as_str))
    }
    type AlignKey = (String, Option<String>, Option<(String, Option<String>)>);
    let align_key = |arr: &[Value], index: &HashMap<&str, usize>, i: usize| -> AlignKey {
        let e = &arr[i];
        let member = targets(index, e, "ownedRelatedElement").first().map(|&m| {
            (
                arr[m]["@type"].as_str().unwrap_or("").to_owned(),
                element_name(&arr[m]).map(str::to_owned),
            )
        });
        (
            e["@type"].as_str().unwrap_or("").to_owned(),
            element_name(e).map(str::to_owned),
            member,
        )
    };
    let mut queue: Vec<(usize, usize)> = pair_elem.iter().map(|(&t, &b)| (t, b)).collect();
    let mut processed: HashSet<(usize, usize)> = HashSet::new();
    while let Some((t, b)) = queue.pop() {
        if !processed.insert((t, b)) {
            continue;
        }
        let unt: Vec<usize> = children(&out, &target_index, t)
            .into_iter()
            .filter(|c| !pair_elem.contains_key(c))
            .collect();
        let unb: Vec<usize> = children(base_arr, &base_index, b)
            .into_iter()
            .filter(|c| !base_paired.contains(c))
            .collect();
        let (mut i, mut j) = (0usize, 0usize);
        while i < unt.len() && j < unb.len() {
            let (tc, bc) = (unt[i], unb[j]);
            if align_key(&out, &target_index, tc) == align_key(base_arr, &base_index, bc) {
                adopt(tc, bc, &out, &mut remap, &mut pair_elem, &mut base_paired);
                queue.push((tc, bc));
                i += 1;
                j += 1;
            } else if unb.len() - j > unt.len() - i {
                // More base children left — a deletion; skip its slot.
                j += 1;
            } else if unt.len() - i > unb.len() - j {
                // More target children left — an insertion.
                i += 1;
            } else {
                i += 1;
                j += 1;
            }
        }
    }
    // `@id` occurrences plus the `elementId` self-mirror, like the
    // elided-decode rewrite.
    fn patch(v: &mut Value, remap: &HashMap<String, String>) {
        match v {
            Value::Object(m) => {
                for (k, w) in m.iter_mut() {
                    match w {
                        Value::String(s) if k == "@id" || k == "elementId" => {
                            if let Some(n) = remap.get(s.as_str()) {
                                *s = n.clone();
                            }
                        }
                        _ => patch(w, remap),
                    }
                }
            }
            Value::Array(a) => a.iter_mut().for_each(|w| patch(w, remap)),
            _ => {}
        }
    }
    let mut seen: HashSet<&str> = HashSet::with_capacity(out.len());
    for e in &mut out {
        patch(e, &remap);
    }
    for e in &out {
        let id = e["@id"].as_str().unwrap();
        if !seen.insert(id) {
            return Err(Error::new(format!("id rebase collides on `{id}`")));
        }
    }
    Ok(Value::Array(out))
}

/// Compute and encode the delta from `base` to `target` (both compact
/// element arrays; order-insensitive — both canonicalize first).
pub fn delta_compact_cbor(
    base: &Value,
    target: &Value,
    opts: &DeltaOptions,
) -> Result<Vec<u8>, Error> {
    delta_encode(base, target, opts, None)
}

/// [`delta_compact_cbor`] with **id elision**:
/// created ids the receiver can re-derive from the applied graph
/// (IDS.md) are not shipped — the created-id table becomes a count,
/// a per-create exception map (foreign or underivable ids), and a
/// mandatory integrity digest the applier verifies against its
/// recovered ids. Strict identity only: the portable mode exists to
/// carry explicit ids to divergent bases, which elision contradicts.
/// `external_name` names reference targets outside the payload
/// (library elements) for the effective-name chains; apply against
/// the **same library version** ([`apply_delta_cbor_with`]).
pub fn delta_compact_cbor_elided(
    base: &Value,
    target: &Value,
    opts: &DeltaOptions,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<u8>, Error> {
    if opts.portable {
        return Err(Error::new(
            "id elision applies to strict deltas only (portable identities are \
             explicit ids by design)",
        ));
    }
    delta_encode(base, target, opts, Some(&external_name))
}

/// One field-level operation of a patch update record.
enum FieldOp {
    /// The field is present in the target with this value.
    Set(Value),
    /// The field is absent from the target element.
    Unset,
    /// List edit: remove `del` items at `at`, insert `items`.
    Splice {
        at: usize,
        del: usize,
        items: Vec<Value>,
    },
}

/// Field-level diff of two same-id compact elements, or `None` where a
/// patch cannot express the change (type changed, or the replay
/// self-check fails). List fields diff to their single contiguous
/// splice; everything else to set/unset.
fn plan_patch(base: &Value, target: &Value) -> Option<Vec<(u8, FieldOp)>> {
    use crate::tables::{K_REF_LIST, K_STR_LIST};
    let b = base.as_object()?;
    let t = target.as_object()?;
    if b.get("@type") != t.get("@type") {
        return None;
    }
    let ty = t.get("@type")?.as_str()?;
    let fields = crate::fields_of(crate::type_code(ty)?)?;
    let mut ops = Vec::new();
    for (ord, field) in fields.iter().enumerate() {
        let key = field.0;
        let op = match (b.get(key), t.get(key)) {
            (bv, tv) if bv == tv => continue,
            (Some(Value::Array(ba)), Some(Value::Array(ta)))
                if matches!(field.1, K_REF_LIST | K_STR_LIST) =>
            {
                let p = ba.iter().zip(ta.iter()).take_while(|(x, y)| x == y).count();
                let s = ba
                    .iter()
                    .rev()
                    .zip(ta.iter().rev())
                    .take_while(|(x, y)| x == y)
                    .count()
                    .min(ba.len().min(ta.len()) - p);
                FieldOp::Splice {
                    at: p,
                    del: ba.len() - p - s,
                    items: ta[p..ta.len() - s].to_vec(),
                }
            }
            (_, Some(tv)) => FieldOp::Set(tv.clone()),
            (Some(_), None) => FieldOp::Unset,
            (None, None) => continue,
        };
        ops.push((u8::try_from(ord).ok()?, op));
    }
    // Self-check: replaying the ops over the base must reproduce the
    // target exactly — this guards keys outside the field table and
    // any planner blind spot; a failed replay falls back to the whole
    // element rather than risking a divergent applied state.
    (!ops.is_empty() && replay_ops(base, &ops).as_ref() == Some(target)).then_some(ops)
}

/// Value-level replay of patch ops (the planner's self-check twin of
/// the wire-side [`read_patch`]).
fn replay_ops(base: &Value, ops: &[(u8, FieldOp)]) -> Option<Value> {
    let mut obj = base.as_object()?.clone();
    let ty = obj.get("@type")?.as_str()?;
    let fields = crate::fields_of(crate::type_code(ty)?)?;
    for (ord, op) in ops {
        let key = fields.get(*ord as usize)?.0;
        match op {
            FieldOp::Set(v) => {
                obj.insert(key.to_owned(), v.clone());
            }
            FieldOp::Unset => {
                obj.remove(key);
            }
            FieldOp::Splice { at, del, items } => {
                let Some(Value::Array(a)) = obj.get_mut(key) else {
                    return None;
                };
                if at.checked_add(*del)? > a.len() {
                    return None;
                }
                a.splice(*at..*at + *del, items.iter().cloned());
            }
        }
    }
    Some(Value::Object(obj))
}

fn write_list_item(
    w: &mut Writer,
    interner: &Interner,
    field: &crate::tables::CborField,
    item: &Value,
) -> Result<(), Error> {
    use crate::tables::K_STR_LIST;
    match (field.1, item) {
        (K_STR_LIST, Value::String(s)) => w.tstr(s),
        (K_STR_LIST, _) => {
            return Err(Error::new(format!(
                "{}: string list holds strings",
                field.0
            )));
        }
        (_, v) => crate::encode::write_ref(w, interner, v)?,
    }
    Ok(())
}

fn write_patch(
    w: &mut Writer,
    interner: &Interner,
    ty: &str,
    fields: &'static [crate::tables::CborField],
    ops: &[(u8, FieldOp)],
) -> Result<(), Error> {
    w.map(ops.len());
    for (ord, op) in ops {
        let field = &fields[*ord as usize];
        w.uint(*ord as u64);
        w.array(2);
        match op {
            FieldOp::Set(v) => {
                w.uint(OP_SET);
                crate::encode::write_value(w, interner, ty, field, v)?;
            }
            FieldOp::Unset => {
                w.uint(OP_UNSET);
                w.null();
            }
            FieldOp::Splice { at, del, items } => {
                w.uint(OP_SPLICE);
                w.array(3);
                w.uint(*at as u64);
                w.uint(*del as u64);
                w.array(items.len());
                for item in items {
                    write_list_item(w, interner, field, item)?;
                }
            }
        }
    }
    Ok(())
}

/// Wire-side patch application: read a `map(n)` patch payload and
/// replay it over the held base element.
fn read_patch(r: &mut Reader, t: &Tables, n: usize, base_elem: &Value) -> Result<Value, Error> {
    use crate::tables::{K_REF_LIST, K_STR_LIST};
    let mut obj = base_elem
        .as_object()
        .cloned()
        .ok_or_else(|| Error::new("base element is an object"))?;
    let ty = obj
        .get("@type")
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new("base element has a string @type"))?
        .to_owned();
    let fields = crate::type_code(&ty)
        .and_then(crate::fields_of)
        .ok_or_else(|| Error::new(format!("unknown @type `{ty}`")))?;
    if n > r.remaining() / 2 {
        return Err(Error::new("patch longer than payload"));
    }
    let mut prev: Option<u64> = None;
    for _ in 0..n {
        let ord = r.uint()?;
        if prev.is_some_and(|p| ord <= p) {
            return Err(Error::new(format!("{ty}: patch ordinals not ascending")));
        }
        prev = Some(ord);
        let field = usize::try_from(ord)
            .ok()
            .and_then(|ord| fields.get(ord))
            .ok_or_else(|| Error::new(format!("{ty}: field ordinal {ord} out of range")))?;
        if r.array()? != 2 {
            return Err(Error::new("patch op is array(2)"));
        }
        match r.uint()? {
            OP_SET => {
                let v = crate::decode::read_value(r, t, field)?;
                obj.insert(field.0.to_owned(), v);
            }
            OP_UNSET => {
                if r.head()? != Head::Null {
                    return Err(Error::new("unset op carries null"));
                }
                obj.remove(field.0);
            }
            OP_SPLICE => {
                if r.array()? != 3 {
                    return Err(Error::new("splice op is array(3)"));
                }
                let at = r.index()?;
                let del = r.index()?;
                let len = r.array()?;
                if len > r.remaining() {
                    return Err(Error::new("splice items longer than payload"));
                }
                let mut items = Vec::with_capacity(len);
                for _ in 0..len {
                    items.push(match (field.1, r.head()?) {
                        (K_REF_LIST, Head::Uint(i)) => t.reference(i)?,
                        (K_REF_LIST, Head::Tstr(m)) => {
                            serde_json::json!({ "@ref": r.tstr_body(m)? })
                        }
                        (K_STR_LIST, Head::Tstr(m)) => Value::String(r.tstr_body(m)?.to_owned()),
                        _ => return Err(Error::new(format!("{}: bad splice item", field.0))),
                    });
                }
                let Some(Value::Array(a)) = obj.get_mut(field.0) else {
                    return Err(Error::new(format!(
                        "{}.{}: splice on an absent or non-list field",
                        ty, field.0
                    )));
                };
                if at.checked_add(del).is_none_or(|end| end > a.len()) {
                    return Err(Error::new(format!(
                        "{}.{}: splice out of range",
                        ty, field.0
                    )));
                }
                a.splice(at..at + del, items);
            }
            op => return Err(Error::new(format!("unknown patch opcode {op}"))),
        }
    }
    Ok(Value::Object(obj))
}

fn delta_encode(
    base: &Value,
    target: &Value,
    opts: &DeltaOptions,
    elide: Option<Resolver>,
) -> Result<Vec<u8>, Error> {
    let base_arr = canonical_views(base)?;
    let target_arr = canonical_views(target)?;
    let base_digest = digest_of_canonical(&base_arr)?;
    let result_digest = digest_of_canonical(&target_arr)?;

    // Ownership backpointers on shipped element records elide
    // against derivation over the **canonical target** — the identical
    // array, in the identical order, that the applier reconstructs and
    // canonicalizes (the result digest proves it), so both sides run
    // the first-claimant rule over the same input.
    let canon_pos: HashMap<&str, usize> = target_arr
        .iter()
        .enumerate()
        .map(|(i, e)| (e["@id"].as_str().expect("canonicalized"), i))
        .collect();
    let target_owners = crate::encode::derive_owners(target_arr.iter().copied());
    let derived_pair = |e: &Value| -> [Option<&str>; 2] {
        let ti = canon_pos[e["@id"].as_str().unwrap()];
        target_owners[ti].map(|s| s.map(|j| target_arr[j]["@id"].as_str().unwrap()))
    };

    // Unit structure: the caller indexes the target as passed; the
    // wire spells result-canonical indices (= indices into the applied
    // state, which the result digest proves reproduces target-canon).
    if !opts.units.is_empty() && opts.portable {
        return Err(Error::new(
            "unit paths ride strict deltas only (portable result indices are \
             not exact against a divergent base)",
        ));
    }
    let units: Vec<(usize, String)> = if opts.units.is_empty() {
        Vec::new()
    } else {
        let passed = target
            .as_array()
            .ok_or_else(|| Error::new("target is a compact element array"))?;
        let mut mapped = Vec::with_capacity(opts.units.len());
        for (i, path) in &opts.units {
            if path.is_empty() {
                return Err(Error::new("empty unit path"));
            }
            let e = passed
                .get(*i)
                .ok_or_else(|| Error::new(format!("unit root index {i} out of range")))?;
            let id = e["@id"]
                .as_str()
                .ok_or_else(|| Error::new(format!("unit root {i} has no @id")))?;
            mapped.push((canon_pos[id], path.clone()));
        }
        mapped.sort_by_key(|&(i, _)| i);
        if mapped.windows(2).any(|w| w[0].0 == w[1].0) {
            return Err(Error::new("duplicate unit root"));
        }
        mapped
    };

    let base_ids: Vec<&str> = base_arr
        .iter()
        .map(|e| e["@id"].as_str().expect("canonicalized"))
        .collect();
    let base_by_id: HashMap<&str, usize> =
        base_ids.iter().enumerate().map(|(i, &s)| (s, i)).collect();
    let mut target_ids: HashSet<&str> = HashSet::with_capacity(target_arr.len());
    for &e in &target_arr {
        if !target_ids.insert(e["@id"].as_str().expect("canonicalized")) {
            return Err(Error::new(format!("duplicate element @id `{}`", e["@id"])));
        }
    }

    // updates/deletes ascending by base position, creates in target order.
    let mut touched: Vec<(usize, Option<&Value>)> = Vec::new();
    for &e in &target_arr {
        if let Some(&i) = base_by_id.get(e["@id"].as_str().unwrap()) {
            if base_arr[i] != e {
                touched.push((i, Some(e)));
            }
        }
    }
    for (i, &id) in base_ids.iter().enumerate() {
        if !target_ids.contains(id) {
            touched.push((i, None));
        }
    }
    touched.sort_by_key(|&(i, _)| i);
    // Creates in target-canonical order, keeping that order's index —
    // elision derives ids over the canonical target, which the applied
    // state reproduces (the result digest proves it).
    let creates: Vec<(usize, &Value)> = target_arr
        .iter()
        .enumerate()
        .filter(|(_, e)| !base_by_id.contains_key(e["@id"].as_str().unwrap()))
        .map(|(i, &e)| (i, e))
        .collect();

    // Element records for external collection + writing — views, so
    // the records are read where they already are.
    let payload: Vec<&Value> = touched
        .iter()
        .filter_map(|&(_, v)| v)
        .chain(creates.iter().map(|&(_, v)| v))
        .collect();
    let payload_elems = elems_of(&payload, table_set(false))?;
    let created_ids: Vec<Uuid> = creates
        .iter()
        .map(|(_, e)| parse_uuid(e["@id"].as_str().unwrap()))
        .collect::<Result<_, _>>()?;

    // Elision: a created id that re-derives from the target graph is
    // not shipped — the applier recomputes it after patching, chaining
    // through base ids it already holds. Underivable or foreign ids
    // ride the exception map (created ordinal → id); the digest lets
    // the applier prove its recovered ids are exactly these.
    let elision: Option<Elision> = match elide {
        Some(external_name) => {
            let target_canon = Value::Array(target_arr.iter().copied().cloned().collect());
            let derived =
                sysmlv2_model::ids::derive_ids(&target_canon, external_name).map_err(Error::new)?;
            let exceptions = creates
                .iter()
                .zip(&created_ids)
                .enumerate()
                .filter(|&(_, (&(ti, _), &u))| derived[ti] != Some(u))
                .map(|(c, (_, &u))| (c as u64, u))
                .collect();
            Some((
                exceptions,
                crate::encode::id_digest(created_ids.iter().copied()),
            ))
        }
        None => None,
    };

    // Local index space: strict = base ++ created; portable = created.
    let mut local: HashMap<Uuid, usize> = HashMap::new();
    let b = if opts.portable { 0 } else { base_ids.len() };
    if !opts.portable {
        for (i, id) in base_ids.iter().enumerate() {
            local.insert(parse_uuid(id)?, i);
        }
    }
    for (i, &u) in created_ids.iter().enumerate() {
        if local.insert(u, b + i).is_some() {
            return Err(Error::new(format!("created id `{u}` collides")));
        }
    }
    let interner = Interner::with_locals(local, &payload_elems)?;

    let mut claims = opts.claims.clone();
    claims.sort_by_key(|&(k, _)| k);
    if claims.windows(2).any(|w| w[0].0 == w[1].0) {
        return Err(Error::new("duplicate claim key"));
    }

    // Update records encode up front (the patched flag lives in the
    // header, written before them): for each strict-mode update, plan
    // the field-level diff against the base element, encode
    // both the whole-element record and the patch, and ship the
    // smaller — a pure function of the inputs. Patches turn the
    // dominant real edit (one entry spliced into a big owner's
    // relationship list) from O(members) to O(1) bytes.
    let mut payload_iter = payload_elems.iter();
    let mut update_bytes: Vec<Option<Vec<u8>>> = Vec::with_capacity(touched.len());
    // Owner exceptions: change-record ordinal → absent-key bits, for
    // whole-element records only — patches replay literally (an owner
    // change or removal travels as an explicit op) and base copies are
    // never touched, so neither participates in owner re-derivation.
    let mut owner_exceptions: Vec<(u64, u64)> = Vec::new();
    for (ordinal, &(i, v)) in touched.iter().enumerate() {
        let Some(target_elem) = v else {
            update_bytes.push(None);
            continue;
        };
        let elem = payload_iter.next().unwrap();
        let mut whole = Writer::default();
        write_element(
            &mut whole,
            &interner,
            elem,
            Some(&derived_pair(target_elem)),
        )?;
        let whole = whole.into_bytes();
        let plan = if opts.portable {
            None
        } else {
            plan_patch(base_arr[i], target_elem)
        };
        let mut chose_whole = true;
        let bytes = match plan {
            Some(ops) => {
                let mut pw = Writer::default();
                write_patch(&mut pw, &interner, elem.ty, elem.fields, &ops)?;
                let patch = pw.into_bytes();
                if patch.len() < whole.len() {
                    chose_whole = false;
                    patch
                } else {
                    whole
                }
            }
            None => whole,
        };
        if chose_whole {
            let bits = crate::encode::owner_absent_bits(elem);
            if bits != 0 {
                owner_exceptions.push((ordinal as u64, bits));
            }
        }
        update_bytes.push(Some(bytes));
    }
    let n_update_elems = payload_elems.len() - creates.len();
    for (k, elem) in payload_elems[n_update_elems..].iter().enumerate() {
        let bits = crate::encode::owner_absent_bits(elem);
        if bits != 0 {
            owner_exceptions.push(((touched.len() + k) as u64, bits));
        }
    }

    let mut w = Writer::with_magic_for(payload_elems.len());
    w.array(7 + usize::from(!units.is_empty()));
    let flags = FLAG_DELTA
        | crate::encode::FLAG_IMPLIED_OWNERS
        | if opts.portable {
            FLAG_DELTA_PORTABLE
        } else {
            0
        }
        | if elision.is_some() {
            crate::encode::FLAG_ELIDE_IDS
        } else {
            0
        }
        | if units.is_empty() {
            0
        } else {
            crate::encode::FLAG_UNIT_PATHS
        };
    w.uint(crate::encode::header_word(flags));
    w.array(3);
    w.bstr(base_digest.as_bytes());
    w.bstr(result_digest.as_bytes());
    w.map(claims.len());
    for (k, c) in &claims {
        w.uint(*k);
        match c {
            Claim::Id(u) => w.bstr(u.as_bytes()),
            Claim::Text(s) => w.tstr(s),
        }
    }
    w.uint(b as u64);
    w.array(interner.ext.len());
    for u in &interner.ext {
        w.bstr(u.as_bytes());
    }
    match &elision {
        // In place of the created-id table: the count, the exception
        // map, and the recovered-id integrity digest.
        Some((exceptions, digest)) => {
            w.array(3);
            w.uint(created_ids.len() as u64);
            w.map(exceptions.len());
            for (c, u) in exceptions {
                w.uint(*c);
                w.bstr(u.as_bytes());
            }
            w.bstr(digest.as_bytes());
        }
        None => {
            w.array(created_ids.len());
            for u in &created_ids {
                w.bstr(u.as_bytes());
            }
        }
    }

    w.array(touched.len() + creates.len());
    for (&(i, _), bytes) in touched.iter().zip(&update_bytes) {
        w.array(2);
        if opts.portable {
            w.bstr(parse_uuid(base_ids[i])?.as_bytes());
        } else {
            w.uint(i as u64);
        }
        match bytes {
            Some(record) => w.raw(record),
            None => w.null(),
        }
    }
    for &(_, e) in &creates {
        w.array(2);
        w.null();
        write_element(
            &mut w,
            &interner,
            payload_iter.next().unwrap(),
            Some(&derived_pair(e)),
        )?;
    }
    // Owner exceptions — change-record ordinal → absent-key
    // bits, ascending (updates in base order, then creates).
    w.map(owner_exceptions.len());
    for (k, bits) in &owner_exceptions {
        w.uint(*k);
        w.uint(*bits);
    }
    if !units.is_empty() {
        // Same wire shape as the snapshot units section: result
        // element index → source path, ascending.
        w.map(units.len());
        for (i, path) in &units {
            w.uint(*i as u64);
            w.tstr(path);
        }
    }
    Ok(w.into_bytes())
}

/// What a best-effort application did beyond a clean apply.
#[derive(Debug, Default, PartialEq)]
pub struct ApplyReport {
    /// The held base matched the payload's base digest.
    pub base_matched: bool,
    /// Deletes whose target was not in the base.
    pub noop_deletes: usize,
    /// Updates whose target was absent and became creates.
    pub upserted_updates: usize,
    /// Creates whose id already existed and replaced it.
    pub replaced_creates: usize,
    /// The result's unit structure — (index into the returned array,
    /// source path) — when the delta carries one. Empty for
    /// unit-less payloads.
    pub units: Vec<(usize, String)>,
}

/// Apply a delta to `base` (order-insensitive) and return the
/// resulting compact element array in delta-canonical order. The base
/// digest is a **hard gate** — a mismatch refuses the delta — and the
/// result digest is verified after application. Id-elided deltas need
/// a resolver — [`apply_delta_cbor_with`].
pub fn apply_delta_cbor(bytes: &[u8], base: &Value) -> Result<Value, Error> {
    apply(bytes, base, false, None).map(|(v, _)| v)
}

/// [`apply_delta_cbor`] accepting **id-elided** deltas too: elided created ids re-derive from the applied graph,
/// exceptions override, and the payload digest must match the
/// recovered id sequence — a mismatch is a hard error. `external_name`
/// names reference targets outside the payload (library elements) for
/// the effective-name chains; pass `&|_| None` for payloads not typed
/// against a library.
pub fn apply_delta_cbor_with(
    bytes: &[u8],
    base: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Value, Error> {
    apply(bytes, base, false, Some(&external_name)).map(|(v, _)| v)
}

/// [`apply_delta_cbor`] for **portable** deltas against a possibly
/// divergent base: on digest mismatch, application proceeds
/// best-effort with the documented no-op/upsert/replace semantics and
/// the report says what happened. Strict-identity deltas refuse —
/// their indices are meaningless off their base.
pub fn apply_delta_cbor_lenient(bytes: &[u8], base: &Value) -> Result<(Value, ApplyReport), Error> {
    apply(bytes, base, true, None)
}

/// Strict application returning the [`ApplyReport`] too — the report
/// carries the delta's unit structure when the payload has one.
/// Explicit-id deltas only; elided deltas take the resolver variant.
pub fn apply_delta_cbor_report(bytes: &[u8], base: &Value) -> Result<(Value, ApplyReport), Error> {
    apply(bytes, base, false, None)
}

/// [`apply_delta_cbor_report`] accepting **id-elided** deltas too:
/// `external_name` names reference targets outside the payload for the
/// effective-name chains (pass `&|_| None` for payloads not typed
/// against a library).
pub fn apply_delta_cbor_report_with(
    bytes: &[u8],
    base: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<(Value, ApplyReport), Error> {
    apply(bytes, base, false, Some(&external_name))
}

fn apply(
    bytes: &[u8],
    base: &Value,
    lenient: bool,
    resolver: Option<Resolver>,
) -> Result<(Value, ApplyReport), Error> {
    // Read the arity and header before judging shape, so a snapshot
    // payload gets its pointed message instead of an arity complaint.
    let mut r = Reader::new(crate::strip_magic(bytes)?);
    let arity = r.array()?;
    // The scheme axis gates only elided deltas: explicit-id records
    // (created table + identities) apply regardless of it.
    let (scheme, flags) = crate::decode::parse_header(r.uint()?)?;
    if flags & FLAG_DELTA == 0 {
        return Err(Error::of(
            ErrorKind::WrongForm,
            "not a delta payload; decode with from_cbor",
        ));
    }
    let portable = flags & FLAG_DELTA_PORTABLE != 0;
    let elided = flags & crate::encode::FLAG_ELIDE_IDS != 0;
    let with_units = flags & crate::encode::FLAG_UNIT_PATHS != 0;
    let implied = flags & crate::encode::FLAG_IMPLIED_OWNERS != 0;
    gate_flags(
        flags,
        FLAG_DELTA
            | FLAG_DELTA_PORTABLE
            | crate::encode::FLAG_ELIDE_IDS
            | crate::encode::FLAG_UNIT_PATHS
            | crate::encode::FLAG_IMPLIED_OWNERS,
    )?;
    let expect_arity = 6 + usize::from(implied) + usize::from(with_units);
    if arity != expect_arity {
        return Err(Error::new(format!(
            "delta payload is array({expect_arity}) for these header flags"
        )));
    }
    if with_units && portable {
        return Err(Error::new("unit paths ride strict deltas only"));
    }
    if elided && portable {
        return Err(Error::new("id elision applies to strict deltas only"));
    }
    if elided && scheme != crate::ID_SCHEME_VERSION {
        return Err(Error::of(
            ErrorKind::UnsupportedVersion,
            format!(
                "id-derivation scheme {scheme} unsupported (decoder carries {}); \
                 the delta's created ids cannot be recovered here",
                crate::ID_SCHEME_VERSION
            ),
        ));
    }
    if lenient && !portable {
        return Err(Error::new(
            "strict-identity delta cannot apply leniently: its indices are only \
             meaningful against the exact base (re-encode portable for cherry-picks)",
        ));
    }
    let resolver = if elided {
        Some(resolver.ok_or_else(|| {
            Error::of(
                ErrorKind::NeedsResolver,
                "id-elided delta; apply with apply_delta_cbor_with and, for \
                 library-typed models, the library name resolver",
            )
        })?)
    } else {
        None
    };

    if r.array()? != 3 {
        return Err(Error::new("base section is array(3)"));
    }
    let base_digest = Uuid::from_bytes(r.bstr(16)?.try_into().unwrap());
    let result_digest = Uuid::from_bytes(r.bstr(16)?.try_into().unwrap());
    let n_claims = match r.head()? {
        Head::Map(m) if m <= r.remaining() / 2 => m,
        Head::Map(_) => return Err(Error::new("claims map longer than payload")),
        _ => return Err(Error::new("claims are a map")),
    };
    for _ in 0..n_claims {
        r.uint()?;
        match r.head()? {
            Head::Bstr(16) => {
                r.take(16)?;
            }
            Head::Tstr(n) => {
                r.tstr_body(n)?;
            }
            _ => return Err(Error::new("claim is bstr(16) or text")),
        }
    }

    let base_arr = canonical_views(base)?;
    let held_digest = digest_of_canonical(&base_arr)?;
    let base_matched = held_digest == base_digest;
    if !base_matched && !lenient {
        return Err(Error::of(
            ErrorKind::BaseDigestMismatch,
            "held base does not match the delta's base digest — fetch the declared \
             base (see the payload's claims) or, for a portable delta, apply \
             leniently and review the report",
        ));
    }

    let declared_b = r.index()?;
    if portable {
        if declared_b != 0 {
            return Err(Error::new("portable delta declares no base index space"));
        }
    } else if declared_b != base_arr.len() {
        return Err(Error::of(
            ErrorKind::BaseDigestMismatch,
            "base element count differs from the held base",
        ));
    }
    let n_ext = r.array()?;
    let exts = read_uuid_table(&mut r, n_ext)?;
    // Created ids: the id table, or (elided) the count + the exception
    // map (created ordinal → id) + the recovered-id digest — creates
    // then decode under placeholder ids until derivation replaces them.
    let mut created_exceptions: HashMap<usize, Uuid> = HashMap::new();
    let mut created_digest: Option<Uuid> = None;
    let created: Vec<String> = if elided {
        if r.array()? != 3 {
            return Err(Error::new("elided created-id section is array(3)"));
        }
        let n_created = r.index()?;
        if n_created > r.remaining() {
            return Err(Error::new("created count longer than payload"));
        }
        let entries = r.ascending_map("exception map", 18, |r| {
            let b: [u8; 16] = r.bstr(16)?.try_into().unwrap();
            Ok(Uuid::from_bytes(b))
        })?;
        if entries.last().is_some_and(|&(k, _)| k >= n_created) {
            return Err(Error::new("exception index out of range"));
        }
        created_exceptions = entries.into_iter().collect();
        let d: [u8; 16] = r.bstr(16)?.try_into().unwrap();
        created_digest = Some(Uuid::from_bytes(d));
        (0..n_created).map(crate::decode::placeholder).collect()
    } else {
        let n_created = r.array()?;
        read_uuid_table(&mut r, n_created)?
    };

    // Reference space for decoding payload records.
    let base_ids: Vec<String> = base_arr
        .iter()
        .map(|e| e["@id"].as_str().unwrap().to_owned())
        .collect();
    // Strict identities index the base then the created ids; portable
    // ones carry base references as externals, so the base table is
    // not part of that space.
    let tables = Tables {
        ids: if portable { &[] } else { &base_ids },
        created: &created,
        exts: &exts,
    };
    let field_tables = table_set(false);

    let n_changes = match r.head()? {
        Head::Array(k) if k <= r.remaining() => k,
        Head::Array(_) => return Err(Error::new("change list longer than payload")),
        _ => return Err(Error::new("changes are an array")),
    };

    let mut report = ApplyReport {
        base_matched,
        ..Default::default()
    };
    let by_id: HashMap<&str, usize> = base_ids
        .iter()
        .enumerate()
        .map(|(i, s)| (s.as_str(), i))
        .collect();
    let mut replaced: HashMap<usize, Value> = HashMap::new();
    let mut deleted: HashSet<usize> = HashSet::new();
    let mut appended: Vec<Value> = Vec::new();
    let mut appended_by_id: HashMap<String, usize> = HashMap::new();
    let mut touched_targets: HashSet<usize> = HashSet::new();
    let mut next_created = 0usize;
    // Which change records shipped whole elements (by the
    // element's current id) — the records whose elided backpointers
    // re-derive after canonicalization. Patches replay literally and
    // base copies are untouched, so neither is tracked.
    let mut record_elem_ids: Vec<Option<String>> = Vec::with_capacity(n_changes);

    /// A change record's resolved target.
    enum Ident {
        /// Null identity: a create.
        Create,
        /// A base element (index into the held canonical base).
        Base(usize),
        /// A portable identity absent from the held base.
        Absent(Uuid),
    }

    for _ in 0..n_changes {
        if r.array()? != 2 {
            return Err(Error::new("change record is array(2)"));
        }
        // Identity: base index (strict), id bytes (portable), null (create).
        let identity = match r.head()? {
            Head::Null => Ident::Create,
            Head::Uint(i) if !portable => {
                let at = usize::try_from(i)
                    .ok()
                    .filter(|&at| at < base_arr.len())
                    .ok_or_else(|| Error::new(format!("change target {i} out of range")))?;
                Ident::Base(at)
            }
            Head::Bstr(16) if portable => {
                let u = Uuid::from_bytes(r.take(16)?.try_into().unwrap());
                match by_id.get(u.to_string().as_str()) {
                    Some(&i) => Ident::Base(i),
                    None => Ident::Absent(u),
                }
            }
            _ => return Err(Error::new("change identity is an index, id bytes, or null")),
        };
        if let Ident::Base(i) = identity {
            if !touched_targets.insert(i) {
                return Err(Error::new(format!("change target {i} touched twice")));
            }
        }
        // Payload: element record or null (delete).
        let mut shipped_id: Option<String> = None;
        match r.head()? {
            Head::Null => match identity {
                Ident::Base(i) => {
                    deleted.insert(i);
                }
                Ident::Absent(_) => report.noop_deletes += 1,
                Ident::Create => return Err(Error::new("create record carries no delete")),
            },
            // Field-patch update: replay the ops over the held base
            // element. Strict identity only — a divergent-base upsert
            // has no base element to patch.
            Head::Map(m) => {
                if portable {
                    return Err(Error::new(
                        "field-patch records apply to strict deltas only",
                    ));
                }
                let Ident::Base(i) = identity else {
                    return Err(Error::new("patch record targets a base element"));
                };
                let element = read_patch(&mut r, &tables, m, base_arr[i])?;
                replaced.insert(i, element);
            }
            Head::Array(3) => {
                let id: String = match &identity {
                    Ident::Create => {
                        let id = created
                            .get(next_created)
                            .cloned()
                            .ok_or_else(|| Error::new("created id table exhausted"))?;
                        next_created += 1;
                        id
                    }
                    Ident::Absent(u) => u.to_string(),
                    Ident::Base(i) => base_ids[*i].clone(),
                };
                let element = read_element_body(&mut r, &tables, field_tables, &id)?;
                shipped_id = Some(id.clone());
                match identity {
                    Ident::Base(i) => {
                        replaced.insert(i, element);
                    }
                    Ident::Absent(_) => {
                        // Portable update of an absent target: upsert.
                        report.upserted_updates += 1;
                        if let Some(&k) = appended_by_id.get(&id) {
                            appended[k] = element;
                        } else {
                            appended_by_id.insert(id, appended.len());
                            appended.push(element);
                        }
                    }
                    Ident::Create => {
                        if let Some(&i) = by_id.get(id.as_str()) {
                            // Collision with an existing element.
                            if !portable {
                                return Err(Error::new(format!(
                                    "created id `{id}` already in base"
                                )));
                            }
                            report.replaced_creates += 1;
                            replaced.insert(i, element);
                        } else if let Some(&k) = appended_by_id.get(&id) {
                            report.replaced_creates += 1;
                            appended[k] = element;
                        } else {
                            appended_by_id.insert(id, appended.len());
                            appended.push(element);
                        }
                    }
                }
            }
            _ => {
                return Err(Error::new(
                    "change payload is an element, a patch map, or null",
                ));
            }
        }
        record_elem_ids.push(shipped_id);
    }
    if next_created != created.len() {
        return Err(Error::new("created id table not fully consumed"));
    }

    // Owner exceptions — change-record ordinal → absent-key
    // bits, only meaningful on records that shipped whole elements.
    let mut owner_bits_by_id: HashMap<String, u64> = HashMap::new();
    if implied {
        let entries = r.ascending_map("owner-exception map", 2, |r| match r.uint()? {
            bits @ 1..=3 => Ok(bits),
            _ => Err(Error::new("owner-exception bits out of range")),
        })?;
        for &(k, _) in &entries {
            if record_elem_ids.get(k).is_none() {
                return Err(Error::new("owner-exception index out of range"));
            }
            if record_elem_ids[k].is_none() {
                return Err(Error::new("owner-exception record did not ship an element"));
            }
        }
        let bits_by_ordinal: HashMap<usize, u64> = entries.into_iter().collect();
        // Later records win an id (portable replaces): iterate in
        // record order so the surviving record's bits apply.
        for (k, id) in record_elem_ids.iter().enumerate() {
            if let Some(id) = id {
                owner_bits_by_id.insert(id.clone(), bits_by_ordinal.get(&k).copied().unwrap_or(0));
            }
        }
    }

    // Units section: result element index → source path, ascending —
    // validated against the result length once it is assembled.
    let mut units: Vec<(usize, String)> = Vec::new();
    if with_units {
        units = read_units(&mut r)?;
        if units.iter().any(|(_, path)| path.is_empty()) {
            return Err(Error::new("empty unit path"));
        }
    }

    let mut result: Vec<Value> = Vec::with_capacity(base_arr.len() + appended.len());
    for (i, e) in base_arr.iter().enumerate() {
        if deleted.contains(&i) {
            continue;
        }
        result.push(replaced.remove(&i).unwrap_or_else(|| (*e).clone()));
    }
    result.extend(appended);
    if !r.done() {
        return Err(Error::new("trailing bytes after payload"));
    }

    let mut applied = Value::Array(result);
    if let Some(external_name) = resolver {
        // Recover the elided created ids: every surviving base element
        // pins its known id, created exceptions override, everything
        // else derives from the applied graph (IDS.md); then the
        // digest must hold. Same failure semantics as elided-snapshot
        // decode: never continue past a mismatch.
        let ph: HashMap<String, usize> = (0..created.len())
            .map(|k| (crate::decode::placeholder(k), k))
            .collect();
        let arr = applied.as_array().unwrap();
        let mut ex: HashMap<usize, Uuid> = HashMap::new();
        let mut created_at: Vec<Option<usize>> = vec![None; created.len()];
        for (i, e) in arr.iter().enumerate() {
            let id = e["@id"].as_str().unwrap();
            match ph.get(id) {
                Some(&k) => {
                    created_at[k] = Some(i);
                    if let Some(&u) = created_exceptions.get(&k) {
                        ex.insert(i, u);
                    }
                }
                None => {
                    ex.insert(i, parse_uuid(id)?);
                }
            }
        }
        let finals =
            sysmlv2_model::ids::assign_ids(&applied, &ex, external_name).map_err(Error::new)?;
        let recovered: Vec<Uuid> = created_at
            .iter()
            .map(|o| o.map(|i| finals[i]))
            .collect::<Option<_>>()
            .ok_or_else(|| Error::new("created element missing from the applied state"))?;
        if crate::encode::id_digest(recovered.iter().copied()) != created_digest.unwrap() {
            return Err(Error::new(
                "recovered created ids do not match the delta digest — the encoder \
                 and applier disagree on id derivation (likely causes, most common \
                 first: different standard-library versions on each side; \
                 id-derivation drift between codec versions; a corrupted exception \
                 map)",
            ));
        }
        let map: std::collections::HashMap<String, String> = recovered
            .iter()
            .enumerate()
            .map(|(k, u)| (crate::decode::placeholder(k), u.to_string()))
            .collect();
        crate::decode::patch_placeholders(&mut applied, &map);
        // The shipped-record ledger keyed created elements by their
        // placeholders — follow the id recovery.
        if !owner_bits_by_id.is_empty() {
            owner_bits_by_id = owner_bits_by_id
                .into_iter()
                .map(|(id, bits)| (map.get(&id).cloned().unwrap_or(id), bits))
                .collect();
        }
    }
    let mut value = canonical_owned(applied)?;
    if implied {
        // Re-materialize elided backpointers on the shipped records:
        // derivation runs over the canonicalized applied state — the
        // identical array, in the identical order, the encoder derived
        // over (the result digest below proves it). Explicit spellings
        // in the record win; absent-key exceptions stay absent; base
        // copies and patch replays are never touched.
        let arr = value.as_array().unwrap();
        let owners = crate::encode::derive_owners(arr);
        let all_ids: Vec<String> = arr
            .iter()
            .map(|e| e["@id"].as_str().unwrap().to_owned())
            .collect();
        let arr = value.as_array_mut().unwrap();
        for (i, e) in arr.iter_mut().enumerate() {
            let obj = e.as_object_mut().unwrap();
            let Some(&bits) = obj
                .get("@id")
                .and_then(Value::as_str)
                .and_then(|id| owner_bits_by_id.get(id))
            else {
                continue;
            };
            let ty = obj["@type"].as_str().unwrap().to_owned();
            let code = field_tables
                .binary_search_by(|(t, _)| t.cmp(&ty.as_str()))
                .expect("shipped record's @type is in the tables");
            let fields = field_tables[code].1;
            for (slot, (prop, _)) in crate::encode::OWNER_SLOTS.iter().enumerate() {
                if crate::ordinal(fields, prop).is_none()
                    || bits & crate::encode::owner_bit(slot) != 0
                    || obj.contains_key(*prop)
                {
                    continue;
                }
                let derived = match owners[i][slot] {
                    Some(j) => serde_json::json!({ "@id": all_ids[j] }),
                    None => Value::Null,
                };
                obj.insert((*prop).to_owned(), derived);
            }
        }
    }
    if base_matched {
        let got = digest_of_canonical(&views(value.as_array().unwrap()))?;
        if got != result_digest {
            return Err(Error::new(
                "applied state does not match the delta's result digest — the \
                 encoder and decoder disagree on apply semantics or the payload \
                 is corrupted",
            ));
        }
    }
    if units
        .last()
        .is_some_and(|&(i, _)| i >= value.as_array().unwrap().len())
    {
        return Err(Error::new("unit root index out of range"));
    }
    report.units = units;
    Ok((value, report))
}
