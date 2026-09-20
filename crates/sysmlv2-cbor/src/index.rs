//! Compact base index + resolved delta records: the service
//! boundary for stores that hold **digests and structure, not
//! payloads**. A [`BaseIndex`] captures a snapshot's delta-canonical
//! entries (`id`, metaclass code) and ordered ownership adjacency —
//! enough to resolve a strict delta's indices and patch ordinals, and
//! to *transition* to the applied result's canonical order — without
//! the snapshot's content. [`resolve_strict_delta`] /
//! [`resolve_portable_delta`] expose a delta's records (identities,
//! whole elements, field ops, deletes, owner-exception bits, claims,
//! units) for consumers that compile changes directly instead of
//! materializing the applied state.
//!
//! Scope boundary, by design: deltas with **elided created ids**
//! (`FLAG_ELIDE_IDS`) are refused here — recovering those ids derives
//! through element *names*, which the index deliberately omits; apply
//! them against a materialized base instead. Element records under
//! implied owners (flag 0x20) arrive exactly as shipped: their
//! backpointer fields may be absent (derivation-covered); the
//! transitioned index is the authority for result ownership.
//!
//! The caller owns digest gating: pair a stored index with the state
//! digest it was verified against, and compare that digest to the
//! delta's base digest before trusting index resolution.

use crate::cbor::{Head, Reader};
use crate::decode::{
    Tables, gate_flags, read_element_body, read_units, read_uuid_table, read_uuids, read_value,
};
use crate::delta::{Claim, FLAG_DELTA, FLAG_DELTA_PORTABLE, OP_SET, OP_SPLICE, OP_UNSET};
use crate::encode::{FLAG_ELIDE_IDS, FLAG_IMPLIED_OWNERS, FLAG_UNIT_PATHS, table_set, wire_code};
use crate::{Error, ErrorKind};
use serde_json::Value;
use std::collections::HashMap;
use uuid::Uuid;

const INDEX_MAGIC: &[u8; 4] = b"S2BI";
const INDEX_VERSION: u8 = 1;

fn index_ns() -> Uuid {
    Uuid::new_v5(&Uuid::NAMESPACE_URL, b"sysmlv2-cbor:base-index")
}

/// A snapshot's structure in delta-canonical order: per element its
/// id, concrete-metaclass code, and ordered in-payload ownership
/// adjacency (`ownedRelatedElement` / `ownedRelationship` targets).
#[derive(Debug, Clone, PartialEq)]
pub struct BaseIndex {
    ids: Vec<Uuid>,
    types: Vec<u16>,
    kids: Vec<Vec<u32>>,
    rels: Vec<Vec<u32>>,
}

impl BaseIndex {
    /// Build (and canonicalize) from a compact element array.
    ///
    /// # Panics
    /// If an element has no string `@id`. Canonicalization runs first
    /// and refuses such a payload, so one that reached this point
    /// carries them.
    pub fn from_compact(compact: &Value) -> Result<Self, Error> {
        let arr = crate::delta::canonical_views(compact)?;
        let tables = table_set(false);
        let mut ids = Vec::with_capacity(arr.len());
        let mut types = Vec::with_capacity(arr.len());
        let mut pos: HashMap<&str, u32> = HashMap::with_capacity(arr.len());
        for (i, e) in arr.iter().enumerate() {
            let id = e["@id"].as_str().expect("canonicalized");
            let ty = e
                .get("@type")
                .and_then(Value::as_str)
                .ok_or_else(|| Error::new("element has a string @type"))?;
            let code = tables
                .binary_search_by(|(n, _)| n.cmp(&ty))
                .map_err(|_| Error::new(format!("unknown @type `{ty}`")))?;
            ids.push(Uuid::try_parse(id).map_err(|_| Error::new(format!("invalid UUID `{id}`")))?);
            types.push(wire_code(code)?);
            pos.entry(id).or_insert(adjacency_pos(i)?);
        }
        let adjacency = |key: &str| -> Vec<Vec<u32>> {
            arr.iter()
                .map(|e| {
                    e.get(key)
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                        .filter_map(|t| t.get("@id").and_then(Value::as_str))
                        .filter_map(|s| pos.get(s).copied())
                        .collect()
                })
                .collect()
        };
        Ok(Self {
            kids: adjacency("ownedRelatedElement"),
            rels: adjacency("ownedRelationship"),
            ids,
            types,
        })
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// Element id at canonical position `i`.
    #[must_use]
    pub fn id(&self, i: usize) -> Uuid {
        self.ids[i]
    }

    /// Concrete-metaclass wire code at canonical position `i`.
    #[must_use]
    pub fn type_code(&self, i: usize) -> u16 {
        self.types[i]
    }

    /// The ids in canonical order — the strict-delta index space.
    #[must_use]
    pub fn ids(&self) -> &[Uuid] {
        &self.ids
    }

    /// Versioned, checksummed binary form (the registry artifact).
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(self.ids.len() * 20 + 16);
        b.extend_from_slice(INDEX_MAGIC);
        b.push(INDEX_VERSION);
        uvarint(&mut b, self.ids.len() as u64);
        for u in &self.ids {
            b.extend_from_slice(u.as_bytes());
        }
        for t in &self.types {
            uvarint(&mut b, *t as u64);
        }
        for lists in [&self.kids, &self.rels] {
            for l in lists.iter() {
                uvarint(&mut b, l.len() as u64);
                for &x in l {
                    uvarint(&mut b, x as u64);
                }
            }
        }
        let sum = Uuid::new_v5(&index_ns(), &b);
        b.extend_from_slice(sum.as_bytes());
        b
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 21 || &bytes[..4] != INDEX_MAGIC {
            return Err(Error::new("not a base-index artifact"));
        }
        if bytes[4] != INDEX_VERSION {
            return Err(Error::of(
                ErrorKind::UnsupportedVersion,
                format!(
                    "base-index version {} unsupported (this build carries {INDEX_VERSION})",
                    bytes[4]
                ),
            ));
        }
        let (body, sum) = bytes.split_at(bytes.len() - 16);
        if Uuid::new_v5(&index_ns(), body).as_bytes() != sum {
            return Err(Error::new("base-index checksum mismatch"));
        }
        let mut r = VarReader {
            b: &body[5..],
            at: 0,
        };
        let n = r.index()?;
        if n > body.len() / 16 {
            return Err(Error::new("base-index count longer than artifact"));
        }
        let mut ids = Vec::with_capacity(n);
        for _ in 0..n {
            ids.push(Uuid::from_bytes(r.take16()?));
        }
        // Type codes index the compact field tables on every later
        // use (patch resolution, transition), so range-check them here.
        let n_types = table_set(false).len();
        let mut types = Vec::with_capacity(n);
        for _ in 0..n {
            let code = r.uvarint()?;
            let code = u16::try_from(code)
                .ok()
                .filter(|&c| usize::from(c) < n_types)
                .ok_or_else(|| Error::new(format!("base-index type code {code} out of range")))?;
            types.push(code);
        }
        let lists = |r: &mut VarReader| -> Result<Vec<Vec<u32>>, Error> {
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                let m = r.index()?;
                if m > body.len() {
                    return Err(Error::new("base-index list longer than artifact"));
                }
                let mut l = Vec::with_capacity(m);
                for _ in 0..m {
                    let x = u32::try_from(r.uvarint()?)
                        .ok()
                        .filter(|&x| (x as usize) < n)
                        .ok_or_else(|| Error::new("base-index adjacency out of range"))?;
                    l.push(x);
                }
                out.push(l);
            }
            Ok(out)
        };
        let kids = lists(&mut r)?;
        let rels = lists(&mut r)?;
        if r.at != r.b.len() {
            return Err(Error::new("trailing bytes in base-index artifact"));
        }
        Ok(Self {
            ids,
            types,
            kids,
            rels,
        })
    }
}

/// An element's canonical position as a 32-bit adjacency entry. The
/// adjacency lists address the index's own elements, so a snapshot
/// that outgrows the 32-bit space is refused rather than aliased onto
/// a different element.
fn adjacency_pos(position: usize) -> Result<u32, Error> {
    u32::try_from(position)
        .map_err(|_| Error::new("snapshot outgrew the 32-bit adjacency index space"))
}

fn uvarint(b: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            b.push(byte);
            return;
        }
        b.push(byte | 0x80);
    }
}

struct VarReader<'a> {
    b: &'a [u8],
    at: usize,
}

impl VarReader<'_> {
    fn uvarint(&mut self) -> Result<u64, Error> {
        let mut v = 0u64;
        for shift in (0..64).step_by(7) {
            let byte = *self
                .b
                .get(self.at)
                .ok_or_else(|| Error::of(ErrorKind::Truncated, "truncated base-index artifact"))?;
            self.at += 1;
            v |= ((byte & 0x7f) as u64) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err(Error::new("overlong varint in base-index artifact"))
    }

    /// Read a varint as an in-memory index, length or position
    /// ([`Reader::index_of`]).
    fn index(&mut self) -> Result<usize, Error> {
        Reader::index_of(self.uvarint()?)
    }

    fn take16(&mut self) -> Result<[u8; 16], Error> {
        let end = self.at + 16;
        let s = self
            .b
            .get(self.at..end)
            .ok_or_else(|| Error::of(ErrorKind::Truncated, "truncated base-index artifact"))?;
        self.at = end;
        Ok(s.try_into().unwrap())
    }
}

/// A resolved change target.
///
/// Non-exhaustive: further identity modes would land here.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum RecordTarget {
    /// A create; `id` comes from the created-id table.
    Create { id: Uuid },
    /// A strict base target: canonical position + its id.
    Base { index: usize, id: Uuid },
    /// A portable id-keyed target (present in the base or not).
    Id { id: Uuid },
}

/// One field-level patch operation, values decoded to JSON shape
/// (references as `{"@id": …}` / `{"@ref": …}`).
///
/// Non-exhaustive: further opcodes would land here.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum PatchOp {
    Set(Value),
    Unset,
    Splice {
        at: usize,
        del: usize,
        items: Vec<Value>,
    },
}

/// A resolved change payload. `Element` values are **as shipped**:
/// under implied owners their backpointer fields may be absent.
#[derive(Debug, Clone, PartialEq)]
pub enum RecordPayload {
    Element(Value),
    Patch(Vec<(&'static str, PatchOp)>),
    Delete,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedRecord {
    pub target: RecordTarget,
    pub payload: RecordPayload,
    /// Absent-key bits for elided backpointers on shipped elements
    /// (1 = `owningRelationship`, 2 = `owningRelatedElement`).
    pub owner_absent_bits: u64,
}

/// A delta's records and envelope, resolved without a materialized
/// base.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedDelta {
    pub portable: bool,
    pub base_digest: Uuid,
    pub result_digest: Uuid,
    pub claims: Vec<(u64, Claim)>,
    /// Result-canonical unit structure, when carried.
    pub units: Vec<(u64, String)>,
    pub records: Vec<ResolvedRecord>,
}

/// Resolve a **strict** delta's records through a base index: change
/// indices become ids, patch ordinals become property names via the
/// base element's metaclass, and reference values decode through the
/// base-and-created id space. The caller must already have matched
/// the delta's `base_digest` against the digest its index was
/// verified with.
pub fn resolve_strict_delta(bytes: &[u8], base: &BaseIndex) -> Result<ResolvedDelta, Error> {
    resolve(bytes, Some(base))
}

/// Resolve a **portable** delta's records (id-keyed; no index needed).
pub fn resolve_portable_delta(bytes: &[u8]) -> Result<ResolvedDelta, Error> {
    resolve(bytes, None)
}

fn resolve(bytes: &[u8], base: Option<&BaseIndex>) -> Result<ResolvedDelta, Error> {
    let mut r = Reader::new(crate::strip_magic(bytes)?);
    let arity = r.array()?;
    let (_, flags) = crate::decode::parse_header(r.uint()?)?;
    if flags & FLAG_DELTA == 0 {
        return Err(Error::of(ErrorKind::WrongForm, "not a delta payload"));
    }
    let portable = flags & FLAG_DELTA_PORTABLE != 0;
    if portable != base.is_none() {
        return Err(Error::of(
            ErrorKind::WrongForm,
            if portable {
                "portable delta: resolve without a base index"
            } else {
                "strict delta: resolve with its base index"
            },
        ));
    }
    if flags & FLAG_ELIDE_IDS != 0 {
        return Err(Error::of(
            ErrorKind::NeedsResolver,
            "id-elided delta: created-id recovery derives through element names, \
             which a base index does not carry — apply against a materialized base",
        ));
    }
    let with_units = flags & FLAG_UNIT_PATHS != 0;
    let implied = flags & FLAG_IMPLIED_OWNERS != 0;
    gate_flags(
        flags,
        FLAG_DELTA | FLAG_DELTA_PORTABLE | FLAG_UNIT_PATHS | FLAG_IMPLIED_OWNERS,
    )?;
    let expect_arity = 6 + usize::from(implied) + usize::from(with_units);
    if arity != expect_arity {
        return Err(Error::new(format!(
            "delta payload is array({expect_arity}) for these header flags"
        )));
    }
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
    let mut claims = Vec::with_capacity(n_claims);
    for _ in 0..n_claims {
        let key = r.uint()?;
        match r.head()? {
            Head::Bstr(16) => claims.push((
                key,
                Claim::Id(Uuid::from_bytes(r.take(16)?.try_into().unwrap())),
            )),
            Head::Tstr(n) => claims.push((key, Claim::Text(r.tstr_body(n)?.to_owned()))),
            _ => return Err(Error::new("claim is bstr(16) or text")),
        }
    }
    let declared_b = r.index()?;
    if let Some(base) = base {
        if declared_b != base.len() {
            return Err(Error::of(
                ErrorKind::BaseDigestMismatch,
                "base element count differs from the index — wrong or stale index",
            ));
        }
    } else if declared_b != 0 {
        return Err(Error::new("portable delta declares no base index space"));
    }
    let n_ext = r.array()?;
    let exts = read_uuid_table(&mut r, n_ext)?;
    let n_created = r.array()?;
    let created = read_uuids(&mut r, n_created)?;
    // Reference space for decoding payload records: the base ids
    // (strict only), then the created ids, then the externals.
    let base_ids: Vec<String> = base
        .into_iter()
        .flat_map(|b| b.ids.iter().map(Uuid::to_string))
        .collect();
    let created_ids: Vec<String> = created.iter().map(Uuid::to_string).collect();
    let tables = Tables {
        ids: &base_ids,
        created: &created_ids,
        exts: &exts,
    };
    let field_tables = table_set(false);

    let n_changes = match r.head()? {
        Head::Array(k) if k <= r.remaining() => k,
        Head::Array(_) => return Err(Error::new("change list longer than payload")),
        _ => return Err(Error::new("changes are an array")),
    };
    let mut records: Vec<ResolvedRecord> = Vec::with_capacity(n_changes);
    let mut next_created = 0usize;
    for _ in 0..n_changes {
        if r.array()? != 2 {
            return Err(Error::new("change record is array(2)"));
        }
        let target = match r.head()? {
            Head::Null => {
                let &id = created
                    .get(next_created)
                    .ok_or_else(|| Error::new("created id table exhausted"))?;
                next_created += 1;
                RecordTarget::Create { id }
            }
            Head::Uint(i) if !portable => {
                let base = base.unwrap();
                let at = usize::try_from(i)
                    .ok()
                    .filter(|&at| at < base.len())
                    .ok_or_else(|| Error::new(format!("change target {i} out of range")))?;
                RecordTarget::Base {
                    index: at,
                    id: base.ids[at],
                }
            }
            Head::Bstr(16) if portable => RecordTarget::Id {
                id: Uuid::from_bytes(r.take(16)?.try_into().unwrap()),
            },
            _ => return Err(Error::new("change identity is an index, id bytes, or null")),
        };
        let payload = match r.head()? {
            Head::Null => {
                if matches!(target, RecordTarget::Create { .. }) {
                    return Err(Error::new("create record carries no delete"));
                }
                RecordPayload::Delete
            }
            Head::Map(m) => {
                let RecordTarget::Base { index, .. } = target else {
                    return Err(Error::new("patch record targets a base element"));
                };
                let fields = field_tables[base.unwrap().types[index] as usize].1;
                RecordPayload::Patch(parse_patch_ops(&mut r, &tables, m, fields)?)
            }
            Head::Array(3) => {
                let id = match &target {
                    RecordTarget::Create { id }
                    | RecordTarget::Base { id, .. }
                    | RecordTarget::Id { id } => id.to_string(),
                };
                RecordPayload::Element(read_element_body(&mut r, &tables, field_tables, &id)?)
            }
            _ => {
                return Err(Error::new(
                    "change payload is an element, a patch map, or null",
                ));
            }
        };
        records.push(ResolvedRecord {
            target,
            payload,
            owner_absent_bits: 0,
        });
    }
    if next_created != created.len() {
        return Err(Error::new("created id table not fully consumed"));
    }
    if implied {
        let entries = r.ascending_map("owner-exception map", 2, |r| match r.uint()? {
            bits @ 1..=3 => Ok(bits),
            _ => Err(Error::new("owner-exception bits out of range")),
        })?;
        for (k, bits) in entries {
            let rec = records
                .get_mut(k)
                .ok_or_else(|| Error::new("owner-exception index out of range"))?;
            if !matches!(rec.payload, RecordPayload::Element(_)) {
                return Err(Error::new("owner-exception record did not ship an element"));
            }
            rec.owner_absent_bits = bits;
        }
    }
    let mut units: Vec<(u64, String)> = Vec::new();
    if with_units {
        units = read_units(&mut r)?
            .into_iter()
            .map(|(i, path)| (i as u64, path))
            .collect();
    }
    if !r.done() {
        return Err(Error::new("trailing bytes after payload"));
    }
    Ok(ResolvedDelta {
        portable,
        base_digest,
        result_digest,
        claims,
        units,
        records,
    })
}

fn parse_patch_ops(
    r: &mut Reader,
    t: &Tables,
    n: usize,
    fields: &'static [crate::tables::CborField],
) -> Result<Vec<(&'static str, PatchOp)>, Error> {
    use crate::tables::{K_REF_LIST, K_STR_LIST};
    if n > r.remaining() / 2 {
        return Err(Error::new("patch longer than payload"));
    }
    let mut ops = Vec::with_capacity(n);
    let mut prev: Option<u64> = None;
    for _ in 0..n {
        let ord = r.uint()?;
        if prev.is_some_and(|p| ord <= p) {
            return Err(Error::new("patch ordinals not ascending"));
        }
        prev = Some(ord);
        let field = usize::try_from(ord)
            .ok()
            .and_then(|ord| fields.get(ord))
            .ok_or_else(|| Error::new(format!("field ordinal {ord} out of range")))?;
        if r.array()? != 2 {
            return Err(Error::new("patch op is array(2)"));
        }
        let op = match r.uint()? {
            OP_SET => PatchOp::Set(read_value(r, t, field)?),
            OP_UNSET => {
                if r.head()? != Head::Null {
                    return Err(Error::new("unset op carries null"));
                }
                PatchOp::Unset
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
                PatchOp::Splice { at, del, items }
            }
            op => return Err(Error::new(format!("unknown patch opcode {op}"))),
        };
        ops.push((field.0, op));
    }
    Ok(ops)
}

impl ResolvedDelta {
    /// Transition a strict delta's base index to the applied result's
    /// index — the same canonical order, ids, metaclasses, and
    /// adjacency [`BaseIndex::from_compact`] would produce over the
    /// applied state, computed from structure alone. Differentially
    /// gated against `apply_delta_cbor`.
    pub fn transition(&self, base: &BaseIndex) -> Result<BaseIndex, Error> {
        if self.portable {
            return Err(Error::new(
                "portable deltas transition only through a matching base; \
                 resolve strict or apply against content",
            ));
        }
        // Working state per surviving element, keyed by id: metaclass
        // and forward lists as id vectors.
        struct Node {
            id: Uuid,
            ty: u16,
            kids: Vec<Uuid>,
            rels: Vec<Uuid>,
        }
        let to_ids = |l: &[u32]| -> Vec<Uuid> { l.iter().map(|&i| base.ids[i as usize]).collect() };
        let mut order: Vec<Node> = (0..base.len())
            .map(|i| Node {
                id: base.ids[i],
                ty: base.types[i],
                kids: to_ids(&base.kids[i]),
                rels: to_ids(&base.rels[i]),
            })
            .collect();
        let tables = table_set(false);
        let mut deleted: Vec<bool> = vec![false; order.len()];
        let mut appended: Vec<Node> = Vec::new();
        let element_node = |id: Uuid, e: &Value| -> Result<Node, Error> {
            let ty = e
                .get("@type")
                .and_then(Value::as_str)
                .ok_or_else(|| Error::new("element record has a string @type"))?;
            let code = wire_code(
                tables
                    .binary_search_by(|(n, _)| n.cmp(&ty))
                    .map_err(|_| Error::new(format!("unknown @type `{ty}`")))?,
            )?;
            let list = |key: &str| -> Vec<Uuid> {
                e.get(key)
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(|t| t.get("@id").and_then(Value::as_str))
                    .filter_map(|s| Uuid::try_parse(s).ok())
                    .collect()
            };
            Ok(Node {
                id,
                ty: code,
                kids: list("ownedRelatedElement"),
                rels: list("ownedRelationship"),
            })
        };
        for rec in &self.records {
            match (&rec.target, &rec.payload) {
                (RecordTarget::Base { index, .. }, RecordPayload::Delete) => {
                    deleted[*index] = true;
                }
                (RecordTarget::Base { index, id }, RecordPayload::Element(e)) => {
                    order[*index] = element_node(*id, e)?;
                }
                (RecordTarget::Base { index, .. }, RecordPayload::Patch(ops)) => {
                    let node = &mut order[*index];
                    for (prop, op) in ops {
                        let list = match *prop {
                            "ownedRelatedElement" => &mut node.kids,
                            "ownedRelationship" => &mut node.rels,
                            _ => continue,
                        };
                        let items_of = |vs: &[Value]| -> Vec<Uuid> {
                            vs.iter()
                                .filter_map(|t| t.get("@id").and_then(Value::as_str))
                                .filter_map(|s| Uuid::try_parse(s).ok())
                                .collect()
                        };
                        match op {
                            PatchOp::Set(Value::Array(vs)) => *list = items_of(vs),
                            PatchOp::Set(_) | PatchOp::Unset => list.clear(),
                            PatchOp::Splice { at, del, items } => {
                                if at.checked_add(*del).is_none_or(|end| end > list.len()) {
                                    return Err(Error::new(format!("{prop}: splice out of range")));
                                }
                                list.splice(*at..*at + *del, items_of(items));
                            }
                        }
                    }
                }
                (RecordTarget::Create { id }, RecordPayload::Element(e)) => {
                    appended.push(element_node(*id, e)?);
                }
                (RecordTarget::Create { .. }, _) => {
                    return Err(Error::new("create record ships an element"));
                }
                (RecordTarget::Id { .. }, _) => unreachable!("strict deltas resolve base targets"),
            }
        }
        // Applied payload order: surviving base order, then creates.
        let payload: Vec<Node> = order
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !deleted[*i])
            .map(|(_, n)| n)
            .chain(appended)
            .collect();
        // Canonical walk over structure (the delta_canonical rule).
        let pos: HashMap<Uuid, u32> = {
            let mut m = HashMap::with_capacity(payload.len());
            for (i, n) in payload.iter().enumerate() {
                m.entry(n.id).or_insert(adjacency_pos(i)?);
            }
            m
        };
        let resolve_list =
            |l: &[Uuid]| -> Vec<u32> { l.iter().filter_map(|u| pos.get(u).copied()).collect() };
        let kids: Vec<Vec<u32>> = payload.iter().map(|n| resolve_list(&n.kids)).collect();
        let rels: Vec<Vec<u32>> = payload.iter().map(|n| resolve_list(&n.rels)).collect();
        let n = payload.len();
        let mut owned = vec![false; n];
        for lists in [&kids, &rels] {
            for l in lists.iter() {
                for &t in l {
                    owned[t as usize] = true;
                }
            }
        }
        let mut visited = vec![false; n];
        let mut walk: Vec<usize> = Vec::with_capacity(n);
        let mut stack: Vec<usize> = (0..n).rev().filter(|&i| !owned[i]).collect();
        while let Some(i) = stack.pop() {
            if visited[i] {
                continue;
            }
            visited[i] = true;
            walk.push(i);
            for &c in rels[i].iter().rev().chain(kids[i].iter().rev()) {
                if !visited[c as usize] {
                    stack.push(c as usize);
                }
            }
        }
        for (i, seen) in visited.iter().enumerate() {
            if !seen {
                walk.push(i);
            }
        }
        let mut renum: HashMap<usize, u32> = HashMap::with_capacity(walk.len());
        for (k, &i) in walk.iter().enumerate() {
            renum.insert(i, adjacency_pos(k)?);
        }
        Ok(BaseIndex {
            ids: walk.iter().map(|&i| payload[i].id).collect(),
            types: walk.iter().map(|&i| payload[i].ty).collect(),
            kids: walk
                .iter()
                .map(|&i| kids[i].iter().map(|t| renum[&(*t as usize)]).collect())
                .collect(),
            rels: walk
                .iter()
                .map(|&i| rels[i].iter().map(|t| renum[&(*t as usize)]).collect())
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A one-element artifact carrying `code` as its type code, sealed
    /// with the artifact checksum so the reader reaches the code
    /// instead of stopping at the seal. Layout: magic, version, the
    /// element count, one id, the type code, then that element's two
    /// empty adjacency lists.
    fn crafted(code: u64) -> Vec<u8> {
        let mut body = INDEX_MAGIC.to_vec();
        body.push(INDEX_VERSION);
        uvarint(&mut body, 1);
        body.extend_from_slice(&[0x11; 16]);
        uvarint(&mut body, code);
        body.extend_from_slice(&[0, 0]);
        let sum = Uuid::new_v5(&index_ns(), &body);
        body.extend_from_slice(sum.as_bytes());
        body
    }

    /// Artifacts whose body is mutated and then **re-sealed**, so the
    /// reader walks the mutation instead of stopping at the checksum —
    /// the coverage a byte-level fuzz of a sealed artifact cannot
    /// reach. Deterministic, seeded.
    #[test]
    fn resealed_mutations_never_panic() {
        let compact = serde_json::json!([
            { "@type": "Package", "@id": "00000000-0000-4000-8000-000000000001",
              "ownedRelationship": [{ "@id": "00000000-0000-4000-8000-000000000002" }] },
            { "@type": "OwningMembership", "@id": "00000000-0000-4000-8000-000000000002",
              "ownedRelatedElement": [{ "@id": "00000000-0000-4000-8000-000000000003" }] },
            { "@type": "Package", "@id": "00000000-0000-4000-8000-000000000003" },
        ]);
        let sealed = BaseIndex::from_compact(&compact).unwrap().to_bytes();
        let body = &sealed[..sealed.len() - 16];
        // xorshift64*, so the sweep is the same on every run.
        let mut state = 0xBA5E_1DE0_0000_0001_u64;
        let mut next = move || {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            state.wrapping_mul(0x2545_F491_4F6C_DD1D)
        };
        for _ in 0..4000 {
            let mut mutated = body.to_vec();
            let i = usize::try_from(next() % mutated.len() as u64).expect("below a usize");
            match next() % 3 {
                0 => mutated[i] ^= 1u8 << (next() % 8),
                1 => mutated.truncate(i),
                _ => mutated[i] = next().to_le_bytes()[0],
            }
            let sum = Uuid::new_v5(&index_ns(), &mutated);
            mutated.extend_from_slice(sum.as_bytes());
            // Err is fine; panicking is not. A survivor must also
            // round-trip, since it is by then a well-formed index.
            if let Ok(index) = BaseIndex::from_bytes(&mutated) {
                assert_eq!(
                    BaseIndex::from_bytes(&index.to_bytes()).unwrap(),
                    index,
                    "a loaded index re-seals to itself"
                );
            }
        }
    }

    #[test]
    fn crafted_type_codes_out_of_range_are_refused() {
        let package = u64::from(crate::type_code("Package").unwrap());
        assert!(
            BaseIndex::from_bytes(&crafted(package)).is_ok(),
            "the crafting reaches the code, not the checksum"
        );
        for code in [
            table_set(false).len() as u64,
            u64::from(u16::MAX),
            70_000,
            u64::MAX,
        ] {
            let err = BaseIndex::from_bytes(&crafted(code))
                .unwrap_err()
                .to_string();
            assert!(err.contains("type code"), "code {code}: {err}");
        }
    }
}
