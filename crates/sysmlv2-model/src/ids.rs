//! Graph-derived element ids (IDS.md) — the **value-side
//! twin** of the builder's `assign_user_ids`: recomputes every
//! non-root element id of a compact interchange element array from
//! structure + names alone. The corpus gate holds it equal to the
//! builder's assignment; the CBOR id-elision mode will use it as its
//! verifier and decoder.
//!
//! Derivation: `id(child) = uuid5(id(parent), segment)` — the
//! *parent's payload id* is the namespace, so one divergent parent
//! never cascades into its subtree. Segments per IDS.md (id
//! scheme 1): a single-member membership with a named member chains
//! **past the membership** — the member takes `"::" + escaped
//! id-name` directly under its owner and the membership takes `"m"`
//! under the member; alias memberships take `"::" + escapedName`;
//! everything else is positional `r{i}`/`e{j}`. Named segments claim
//! owner scope first-come; a collision drops the pair back to the
//! positional chain. Id-names resolve through the graph (declared,
//! else the KerML 8.2.3.5 effective-name fixpoint; external targets
//! through `external_name`).

use serde_json::Value;
use std::collections::{HashMap, HashSet};
use sysmlv2_syntax::ast::escape_name;
use uuid::Uuid;

/// Why a derivation could not run over a payload. A caller distinguishes
/// a malformed payload (every variant but the last) from a payload that
/// is well formed but does not carry enough identity to complete an
/// assignment ([`IdError::NoIdentity`], reachable only from
/// [`assign_ids`]).
///
/// Non-exhaustive: the derivation may come to distinguish further
/// malformed shapes, and naming one is not a breaking change.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum IdError {
    /// The payload is not a flat array of elements.
    NotAnElementArray,
    /// The element at this index is not a JSON object.
    NotAnObject(usize),
    /// The element at this index carries no string `@id`.
    MissingId(usize),
    /// The element at this index carries no string `@type`.
    MissingType(usize),
    /// An `@id` that is not a UUID, so nothing can chain from it.
    InvalidId(String),
    /// The element at this index has neither a derivable id nor an
    /// exception entry naming it.
    NoIdentity(usize),
}

impl std::fmt::Display for IdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IdError::NotAnElementArray => f.write_str("compact payload is a flat element array"),
            IdError::NotAnObject(i) => write!(f, "element {i} is an object"),
            IdError::MissingId(i) => write!(f, "element {i} has a string @id"),
            IdError::MissingType(i) => write!(f, "element {i} has a string @type"),
            IdError::InvalidId(id) => write!(f, "invalid @id `{id}`"),
            IdError::NoIdentity(i) => {
                write!(f, "element {i}: no derivable id and no exception entry")
            }
        }
    }
}

impl std::error::Error for IdError {}

impl From<IdError> for String {
    fn from(error: IdError) -> String {
        error.to_string()
    }
}

/// Per element of `compact` (payload order): the graph-derived id, or
/// `None` where the scheme assigns rather than derives (document
/// roots) or the element is unreachable from any root. `external_name`
/// names reference targets outside the payload (library elements),
/// keyed by the target's id text. Derivation chains from each
/// parent's **payload** id, so one divergent parent never cascades.
pub fn derive_ids(
    compact: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<Option<Uuid>>, IdError> {
    Ok(walk(compact, external_name, None, Paths::Discard)?.0)
}

/// Per element of `compact` (payload order): the ownership path that
/// seeds its id derivation — the payload index of its root plus the
/// `/`-joined segment chain (roots carry an empty chain) — or `None`
/// for elements unreachable from any root. Paths are a function of
/// structure + names alone, so two payloads walked with the same
/// `external_name` give structurally corresponding elements equal
/// paths no matter how their ids were produced.
pub fn segment_paths(
    compact: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<Option<(usize, String)>>, IdError> {
    Ok(walk(compact, external_name, None, Paths::Keep)?.1)
}

/// Compute the **final** id of every element of a payload whose `@id`
/// strings are placeholders (the CBOR id-elision decode path):
/// element `k`'s id is `exceptions[k]` when present, else
/// `uuid5(final(parent), segment)` — chaining from *computed* finals,
/// since the payload carries no real ids. Roots and unreachable
/// elements must have exceptions; a missing one is an error.
pub fn assign_ids(
    compact: &Value,
    exceptions: &HashMap<usize, Uuid>,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<Uuid>, IdError> {
    let derived = walk(compact, external_name, Some(exceptions), Paths::Discard)?.0;
    derived
        .into_iter()
        .enumerate()
        .map(|(i, d)| {
            exceptions
                .get(&i)
                .copied()
                .or(d)
                .ok_or(IdError::NoIdentity(i))
        })
        .collect()
}

type SegmentPaths = Vec<Option<(usize, String)>>;

/// Whether the walk materializes segment paths. Only [`segment_paths`]
/// reads them, and building one costs a string per element plus a copy
/// of the parent's whole path per step — an id derivation, which every
/// encoded payload runs, pays none of it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Paths {
    Keep,
    Discard,
}

/// The ownership paths built during a walk, when they are wanted.
struct Trail(Option<SegmentPaths>);

impl Trail {
    fn new(n: usize, mode: Paths) -> Trail {
        Trail((mode == Paths::Keep).then(|| vec![None; n]))
    }

    /// A root's path: itself, and no segments.
    fn seed(&mut self, root: usize) {
        if let Some(paths) = self.0.as_mut() {
            paths[root] = Some((root, String::new()));
        }
    }

    /// `child`'s path is `parent`'s extended by `seg`. A parent with no
    /// path (unreachable from any root) gives its children none either.
    fn extend(&mut self, child: usize, parent: usize, seg: &str) {
        let Some(paths) = self.0.as_mut() else { return };
        let Some((root, parent_path)) = &paths[parent] else {
            return;
        };
        let (root, path) = (
            *root,
            if parent_path.is_empty() {
                seg.to_owned()
            } else {
                format!("{parent_path}/{seg}")
            },
        );
        paths[child] = Some((root, path));
    }

    fn finish(self, n: usize) -> SegmentPaths {
        self.0.unwrap_or_else(|| vec![None; n])
    }
}

fn walk(
    compact: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
    finals: Option<&HashMap<usize, Uuid>>,
    keep_paths: Paths,
) -> Result<(Vec<Option<Uuid>>, SegmentPaths), IdError> {
    let elems = compact.as_array().ok_or(IdError::NotAnElementArray)?;
    let n = elems.len();
    let obj = |i: usize| elems[i].as_object().expect("checked below");
    let mut index: HashMap<&str, usize> = HashMap::with_capacity(n);
    for (i, e) in elems.iter().enumerate() {
        let o = e.as_object().ok_or(IdError::NotAnObject(i))?;
        let id = o
            .get("@id")
            .and_then(Value::as_str)
            .ok_or(IdError::MissingId(i))?;
        o.get("@type")
            .and_then(Value::as_str)
            .ok_or(IdError::MissingType(i))?;
        index.insert(id, i);
    }
    let ty = |i: usize| obj(i).get("@type").and_then(Value::as_str).unwrap_or("");
    let id_str = |i: usize| obj(i).get("@id").and_then(Value::as_str).unwrap();
    // A reference list property → in-payload target indices, in order.
    let targets = |i: usize, key: &str| -> Vec<usize> {
        match obj(i).get(key) {
            Some(Value::Array(a)) => a
                .iter()
                .filter_map(|v| v.get("@id").and_then(Value::as_str))
                .filter_map(|s| index.get(s).copied())
                .collect(),
            _ => Vec::new(),
        }
    };
    // Both ownership lists, resolved once: the name fixpoint below reads
    // the relationship list of every element on every pass, and the walk
    // reads both again.
    let owned_rels: Vec<Vec<usize>> = (0..n).map(|i| targets(i, "ownedRelationship")).collect();
    let owned_elems: Vec<Vec<usize>> = (0..n).map(|i| targets(i, "ownedRelatedElement")).collect();

    // Names: declared, else the graph-effective fixpoint. This is the
    // id-segment reading of the one naming rule — see
    // `full::effective_name_of` for the rule and its other
    // implementations; a change to one belongs in all of them.
    let declared = |i: usize| -> Option<String> {
        let o = obj(i);
        o.get("declaredName")
            .and_then(Value::as_str)
            .or_else(|| o.get("declaredShortName").and_then(Value::as_str))
            .map(str::to_owned)
    };
    let mut names: Vec<Option<String>> = (0..n).map(declared).collect();
    let effective = |i: usize, names: &[Option<String>]| -> Option<String> {
        for &r in &owned_rels[i] {
            let key = match ty(r) {
                "Redefinition" => "redefinedFeature",
                "ReferenceSubsetting" => "referencedFeature",
                _ => continue,
            };
            let target = obj(r).get(key)?;
            if let Some(s) = target.get("@ref").and_then(Value::as_str) {
                return Some(s.rsplit("::").next().unwrap_or(s).to_string());
            }
            let s = target.get("@id").and_then(Value::as_str)?;
            return match index.get(s) {
                Some(&t) => names[t].clone(),
                None => external_name(s),
            };
        }
        None
    };
    loop {
        let mut changed = false;
        for i in 0..n {
            if names[i].is_some() || ty(i).ends_with("Membership") {
                continue;
            }
            if let Some(name) = effective(i, &names) {
                names[i] = Some(name);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Roots: elements owned by nothing in the payload.
    let mut owned: vec::BitSet = vec::BitSet::new(n);
    for i in 0..n {
        for &r in &owned_rels[i] {
            owned.set(r);
        }
        for &k in &owned_elems[i] {
            owned.set(k);
        }
    }

    let mut derived: Vec<Option<Uuid>> = vec![None; n];
    // The chain namespace: the parent's payload id when verifying
    // (`derive_ids` — divergence must not cascade), the parent's
    // computed/exception id when assigning (`assign_ids` — the payload
    // carries placeholders).
    let final_of = |k: usize, derived: &Vec<Option<Uuid>>| -> Result<Uuid, IdError> {
        match finals {
            Some(exceptions) => exceptions
                .get(&k)
                .copied()
                .or(derived[k])
                .ok_or(IdError::NoIdentity(k)),
            None => {
                Uuid::parse_str(id_str(k)).map_err(|_| IdError::InvalidId(id_str(k).to_string()))
            }
        }
    };
    let mut paths = Trail::new(n, keep_paths);
    let mut stack: Vec<usize> = (0..n).filter(|&i| !owned.get(i)).collect();
    for &root in &stack {
        paths.seed(root);
    }
    let mut visited = vec::BitSet::new(n);
    while let Some(owner) = stack.pop() {
        if visited.get(owner) {
            continue;
        }
        visited.set(owner);
        let owner_ns = final_of(owner, &derived)?;
        let mut used: HashSet<String> = HashSet::new();
        for (i, &rel) in owned_rels[owner].iter().enumerate() {
            let kids = &owned_elems[rel];
            let membership = ty(rel).ends_with("Membership");
            // A single-member membership whose member has an id-name
            // chains **past the membership**: the member
            // takes the owner-scope named segment, and the membership
            // is named by its member — neither references the ordinal,
            // so member insertion cannot disturb named siblings.
            // Owner-scope collisions (duplicate member names, aliases)
            // drop the pair back to the positional chain.
            if membership && kids.len() == 1 {
                if let Some(name) = &names[kids[0]] {
                    let named = format!("::{}", escape_name(name));
                    if used.insert(named.clone()) {
                        let kid = kids[0];
                        derived[kid] = Some(Uuid::new_v5(&owner_ns, named.as_bytes()));
                        paths.extend(kid, owner, &named);
                        stack.push(kid);
                        let kid_ns = final_of(kid, &derived)?;
                        derived[rel] = Some(Uuid::new_v5(&kid_ns, b"m"));
                        paths.extend(rel, kid, "m");
                        stack.push(rel);
                        continue;
                    }
                }
            }
            let mut seg = format!("r{i}");
            if kids.is_empty() && ty(rel) == "Membership" {
                let o = obj(rel);
                if let Some(name) = o
                    .get("memberName")
                    .and_then(Value::as_str)
                    .or_else(|| o.get("memberShortName").and_then(Value::as_str))
                {
                    let named = format!("::{}", escape_name(name));
                    if used.insert(named.clone()) {
                        seg = named;
                    }
                }
            }
            derived[rel] = Some(Uuid::new_v5(&owner_ns, seg.as_bytes()));
            paths.extend(rel, owner, &seg);
            // A relationship can own relationships of its own
            // (annotations, filters) — it is an owner in its own right.
            stack.push(rel);
            let rel_ns = final_of(rel, &derived)?;
            let mut kid_used: HashSet<String> = HashSet::new();
            for (j, &kid) in kids.iter().enumerate() {
                let mut kseg = format!("e{j}");
                if membership {
                    if let Some(name) = &names[kid] {
                        let named = format!("::{}", escape_name(name));
                        if kid_used.insert(named.clone()) {
                            kseg = named;
                        }
                    }
                }
                derived[kid] = Some(Uuid::new_v5(&rel_ns, kseg.as_bytes()));
                paths.extend(kid, rel, &kseg);
                stack.push(kid);
            }
        }
    }
    Ok((derived, paths.finish(n)))
}

/// Tiny fixed-size bit set (no dependency).
mod vec {
    pub struct BitSet(Vec<u64>);
    impl BitSet {
        pub fn new(n: usize) -> Self {
            Self(vec![0; n.div_ceil(64)])
        }
        pub fn set(&mut self, i: usize) {
            self.0[i / 64] |= 1 << (i % 64);
        }
        pub fn get(&self, i: usize) -> bool {
            self.0[i / 64] >> (i % 64) & 1 != 0
        }
    }
}
