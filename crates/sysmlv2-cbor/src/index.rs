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
use crate::decode::{Tables, read_element_body, read_uuid_table, read_value};
use crate::delta::{Claim, FLAG_DELTA, FLAG_DELTA_PORTABLE, OP_SET, OP_SPLICE, OP_UNSET};
use crate::encode::{FLAG_ELIDE_IDS, FLAG_IMPLIED_OWNERS, FLAG_UNIT_PATHS, table_set};
use crate::{Error, delta_canonical};
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
    pub fn from_compact(compact: &Value) -> Result<Self, Error> {
        let canon = delta_canonical(compact)?;
        let arr = canon.as_array().unwrap();
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
            types.push(code as u16);
            pos.entry(id).or_insert(i as u32);
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

    pub fn len(&self) -> usize {
        self.ids.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// Element id at canonical position `i`.
    pub fn id(&self, i: usize) -> Uuid {
        self.ids[i]
    }

    /// Concrete-metaclass wire code at canonical position `i`.
    pub fn type_code(&self, i: usize) -> u16 {
        self.types[i]
    }

    /// The ids in canonical order — the strict-delta index space.
    pub fn ids(&self) -> &[Uuid] {
        &self.ids
    }

    /// Versioned, checksummed binary form (the registry artifact).
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
            return Err(Error::new(format!(
                "base-index version {} unsupported (this build carries {INDEX_VERSION})",
                bytes[4]
            )));
        }
        let (body, sum) = bytes.split_at(bytes.len() - 16);
        if Uuid::new_v5(&index_ns(), body).as_bytes() != sum {
            return Err(Error::new("base-index checksum mismatch"));
        }
        let mut r = VarReader {
            b: &body[5..],
            at: 0,
        };
        let n = r.uvarint()? as usize;
        if n > body.len() / 16 {
            return Err(Error::new("base-index count longer than artifact"));
        }
        let mut ids = Vec::with_capacity(n);
        for _ in 0..n {
            ids.push(Uuid::from_bytes(r.take16()?));
        }
        let mut types = Vec::with_capacity(n);
        for _ in 0..n {
            types.push(r.uvarint()? as u16);
        }
        let lists = |r: &mut VarReader| -> Result<Vec<Vec<u32>>, Error> {
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                let m = r.uvarint()? as usize;
                if m > body.len() {
                    return Err(Error::new("base-index list longer than artifact"));
                }
                let mut l = Vec::with_capacity(m);
                for _ in 0..m {
                    let x = r.uvarint()?;
                    if x as usize >= n {
                        return Err(Error::new("base-index adjacency out of range"));
                    }
                    l.push(x as u32);
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
                .ok_or_else(|| Error::new("truncated base-index artifact"))?;
            self.at += 1;
            v |= ((byte & 0x7f) as u64) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err(Error::new("overlong varint in base-index artifact"))
    }

    fn take16(&mut self) -> Result<[u8; 16], Error> {
        let end = self.at + 16;
        let s = self
            .b
            .get(self.at..end)
            .ok_or_else(|| Error::new("truncated base-index artifact"))?;
        self.at = end;
        Ok(s.try_into().unwrap())
    }
}

/// A resolved change target.
#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
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
        return Err(Error::new("not a delta payload"));
    }
    let portable = flags & FLAG_DELTA_PORTABLE != 0;
    if portable != base.is_none() {
        return Err(Error::new(if portable {
            "portable delta: resolve without a base index"
        } else {
            "strict delta: resolve with its base index"
        }));
    }
    if flags & FLAG_ELIDE_IDS != 0 {
        return Err(Error::new(
            "id-elided delta: created-id recovery derives through element names, \
             which a base index does not carry — apply against a materialized base",
        ));
    }
    let with_units = flags & FLAG_UNIT_PATHS != 0;
    let implied = flags & FLAG_IMPLIED_OWNERS != 0;
    let known = FLAG_DELTA | FLAG_DELTA_PORTABLE | FLAG_UNIT_PATHS | FLAG_IMPLIED_OWNERS;
    if flags & !known != 0 {
        return Err(Error::new(format!("unknown header flags {flags:#x}")));
    }
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
    let declared_b = r.uint()? as usize;
    if let Some(base) = base {
        if declared_b != base.len() {
            return Err(Error::new(
                "base element count differs from the index — wrong or stale index",
            ));
        }
    } else if declared_b != 0 {
        return Err(Error::new("portable delta declares no base index space"));
    }
    let n_ext = r.array()?;
    let exts = read_uuid_table(&mut r, n_ext)?;
    let n_created = r.array()?;
    let created = read_uuid_table(&mut r, n_created)?;
    let base_ids: Vec<String> = base
        .map(|b| b.ids.iter().map(Uuid::to_string).collect())
        .unwrap_or_default();
    let combined: Vec<String> = base_ids.iter().cloned().chain(created.clone()).collect();
    let tables = Tables {
        ids: &combined,
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
                let id = created
                    .get(next_created)
                    .ok_or_else(|| Error::new("created id table exhausted"))?;
                next_created += 1;
                RecordTarget::Create {
                    id: Uuid::try_parse(id).unwrap(),
                }
            }
            Head::Uint(i) if !portable => {
                let i = i as usize;
                let base = base.unwrap();
                if i >= base.len() {
                    return Err(Error::new(format!("change target {i} out of range")));
                }
                RecordTarget::Base {
                    index: i,
                    id: base.ids[i],
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
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 2 => m,
            Head::Map(_) => return Err(Error::new("owner-exception map longer than payload")),
            _ => return Err(Error::new("owner-exception map expected")),
        };
        let mut prev: i64 = -1;
        for _ in 0..m {
            let k = r.uint()? as usize;
            if k as i64 <= prev {
                return Err(Error::new("owner-exception indices not ascending"));
            }
            prev = k as i64;
            let bits = r.uint()?;
            if bits == 0 || bits > 3 {
                return Err(Error::new("owner-exception bits out of range"));
            }
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
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 2 => m,
            Head::Map(_) => return Err(Error::new("unit-path map longer than payload")),
            _ => return Err(Error::new("unit-path map expected")),
        };
        for _ in 0..m {
            let i = r.uint()?;
            match r.head()? {
                Head::Tstr(n) => units.push((i, r.tstr_body(n)?.to_owned())),
                _ => return Err(Error::new("unit path is a text string")),
            }
        }
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
    let mut prev: i32 = -1;
    for _ in 0..n {
        let ord = r.uint()?;
        if ord as i32 <= prev {
            return Err(Error::new("patch ordinals not ascending"));
        }
        prev = ord as i32;
        let field = fields
            .get(ord as usize)
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
                let at = r.uint()? as usize;
                let del = r.uint()? as usize;
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
            let code = tables
                .binary_search_by(|(n, _)| n.cmp(&ty))
                .map_err(|_| Error::new(format!("unknown @type `{ty}`")))?
                as u16;
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
        let pos: HashMap<Uuid, usize> = {
            let mut m = HashMap::with_capacity(payload.len());
            for (i, n) in payload.iter().enumerate() {
                m.entry(n.id).or_insert(i);
            }
            m
        };
        let resolve_list = |l: &[Uuid]| -> Vec<u32> {
            l.iter()
                .filter_map(|u| pos.get(u))
                .map(|&i| i as u32)
                .collect()
        };
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
        let renum: HashMap<usize, u32> = walk
            .iter()
            .enumerate()
            .map(|(k, &i)| (i, k as u32))
            .collect();
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
