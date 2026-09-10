//! Compact element array (`serde_json::Value`) → CBOR payload.
//!
//! Layout: `array(4)` of header word
//! (`layout u8 · tables u16 · scheme u8 · flags u8`), external-UUID table
//! (sorted `bstr(16)`), id table (`bstr(16)` in element order), and the
//! element list. Each element is `array(3)`:
//! `[type code, presence bits, ordinal-keyed map of non-default values]`
//! — a presence bit marks a property present with its default value, so
//! the instance-dependent key sets of the compact emitter reproduce
//! exactly.

use crate::cbor::Writer;
use crate::tables::{
    CborField, ENUM_TABLES, FULL_METACLASS_FIELDS, K_BOOL, K_ELEMENT_ID, K_ENUM, K_LITERAL, K_REF,
    K_REF_LIST, K_STR, K_STR_LIST, METACLASS_FIELDS,
};
use crate::{Error, ordinal};
use serde_json::{Map, Value};
use std::collections::{BTreeSet, HashMap};
use uuid::Uuid;

/// Header flag reserved for the optional id-elision mode.
/// Never set by this version's encoder; the decoder refuses it so a
/// pre-elision decoder can never misread an elided payload.
pub const FLAG_ELIDE_IDS: u8 = 1;

/// Header flag marking a **full-form** payload: element fields index
/// the `FULL_METACLASS_FIELDS` ordinal space (derived properties
/// included) instead of the compact tables.
pub const FLAG_FULL_FORM: u8 = 2;

/// Header flag marking a payload that carries its model's **unit
/// structure**: the body grows a fifth item, a map from element index
/// (each unit's root namespace) to that unit's source path, so a
/// decoded model can be laid back out as its original files.
pub const FLAG_UNIT_PATHS: u8 = 16;

/// Header flag marking a payload whose **ownership backpointers** are
/// implied: an `owningRelationship` / `owningRelatedElement`
/// value that equals its derivation from the payload's forward
/// ownership lists (`ownedRelatedElement` / `ownedRelationship` —
/// each pair is a metamodel inverse) is not spelled on the wire; the
/// decoder re-derives it. Deviations still spell explicitly (a value
/// entry, or the presence-bit null), and elements whose source JSON
/// lacked the key entirely ride a dedicated section (element index →
/// absent-key bits) after the element list, so decode stays
/// Value-identical for every input. Compact snapshot forms only.
/// The digest space is untouched: digests canonicalize through
/// the internal owners-spelled canonical encoding
/// (`to_compact_cbor_canonical`), which always spells owners.
pub const FLAG_IMPLIED_OWNERS: u8 = 32;

/// The two backpointers and the forward list each derives from:
/// slot 0 = `owningRelationship` ← membership in some element's
/// `ownedRelatedElement`; slot 1 = `owningRelatedElement` ←
/// membership in some element's `ownedRelationship`.
pub(crate) const OWNER_SLOTS: [(&str, &str); 2] = [
    ("owningRelationship", "ownedRelatedElement"),
    ("owningRelatedElement", "ownedRelationship"),
];

/// Absent-key exception bit for a backpointer slot.
pub(crate) fn owner_bit(slot: usize) -> u64 {
    1 << slot
}

/// Per element, the derived owner (element index) for each backpointer
/// slot — `None` where no in-payload forward list claims it (derived
/// null). The first claimant in element order, then list order, wins;
/// encoder and decoder agree by running this identical rule over the
/// identical arrays.
pub(crate) fn derive_owners(arr: &[Value]) -> Vec<[Option<usize>; 2]> {
    let mut index: HashMap<&str, usize> = HashMap::with_capacity(arr.len());
    for (i, e) in arr.iter().enumerate() {
        if let Some(id) = e.get("@id").and_then(Value::as_str) {
            index.entry(id).or_insert(i);
        }
    }
    let mut owners = vec![[None, None]; arr.len()];
    for (i, e) in arr.iter().enumerate() {
        for (slot, (_, forward)) in OWNER_SLOTS.iter().enumerate() {
            let targets = e.get(*forward).and_then(Value::as_array);
            for t in targets.into_iter().flatten() {
                let j = t
                    .get("@id")
                    .and_then(Value::as_str)
                    .and_then(|s| index.get(s));
                if let Some(&j) = j {
                    if owners[j][slot].is_none() {
                        owners[j][slot] = Some(i);
                    }
                }
            }
        }
    }
    owners
}

/// The header word: `layout u8 · tables u16 · scheme u8 · flags u8`,
/// packed big-endian into one uint. Decoders refuse `layout`
/// unconditionally, `tables` whenever they decode element records,
/// and `scheme` only when id derivation is in play (elided payloads).
pub(crate) fn header_word(flags: u8) -> u64 {
    (crate::LAYOUT_VERSION as u64) << 32
        | (crate::tables::CBOR_TABLES_VERSION as u64) << 16
        | (crate::ID_SCHEME_VERSION as u64) << 8
        | flags as u64
}

pub(crate) fn table_set(full: bool) -> &'static [(&'static str, &'static [CborField])] {
    if full {
        FULL_METACLASS_FIELDS
    } else {
        METACLASS_FIELDS
    }
}

pub(crate) fn ctx(ty: &str, prop: &str, what: &str) -> Error {
    Error::new(format!("{ty}.{prop}: {what}"))
}

fn parse_uuid(s: &str) -> Result<Uuid, Error> {
    Uuid::try_parse(s).map_err(|_| Error::new(format!("invalid UUID `{s}`")))
}

/// The element object, its metaclass, its field table, and its `@id`.
pub(crate) struct Elem<'a> {
    pub(crate) obj: &'a Map<String, Value>,
    pub(crate) ty: &'a str,
    pub(crate) code: u16,
    pub(crate) fields: &'static [CborField],
    pub(crate) id: &'a str,
    pub(crate) uuid: Uuid,
}

pub(crate) fn elems_of<'a>(
    value: &'a Value,
    tables: &'static [(&'static str, &'static [CborField])],
) -> Result<Vec<Elem<'a>>, Error> {
    let arr = value
        .as_array()
        .ok_or_else(|| Error::new("interchange payload is a flat element array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for e in arr {
        let obj = e
            .as_object()
            .ok_or_else(|| Error::new("element is an object"))?;
        let ty = obj
            .get("@type")
            .and_then(Value::as_str)
            .ok_or_else(|| Error::new("element has a string @type"))?;
        let code = tables
            .binary_search_by(|(n, _)| n.cmp(&ty))
            .map_err(|_| Error::new(format!("unknown @type `{ty}`")))? as u16;
        let id = obj
            .get("@id")
            .and_then(Value::as_str)
            .ok_or_else(|| Error::new(format!("{ty}: element has a string @id")))?;
        out.push(Elem {
            obj,
            ty,
            code,
            fields: tables[code as usize].1,
            id,
            uuid: parse_uuid(id)?,
        });
    }
    Ok(out)
}

/// Default JSON value of a field, or `None` for kinds without one.
/// `id` feeds the `elementId` mirror rule.
pub(crate) fn default_value(field: &CborField, id: &str) -> Option<Value> {
    let (_, kind, etbl, dflt) = *field;
    Some(match kind {
        K_BOOL => Value::Bool(dflt == 1),
        K_STR | K_REF => Value::Null,
        K_STR_LIST | K_REF_LIST => Value::Array(Vec::new()),
        K_ENUM => match dflt {
            255 => Value::Null,
            i => Value::String(ENUM_TABLES[etbl as usize][i as usize].to_owned()),
        },
        K_ELEMENT_ID => Value::String(id.to_owned()),
        _ => return None,
    })
}

/// `{"@id": …}` target UUID, if the value is an id-based reference.
pub(crate) fn ref_uuid(v: &Value) -> Result<Option<Uuid>, Error> {
    let Value::Object(o) = v else { return Ok(None) };
    match (o.len(), o.get("@id"), o.get("@ref")) {
        (1, Some(Value::String(s)), None) => parse_uuid(s).map(Some),
        (1, None, Some(Value::String(_))) => Ok(None),
        _ => Err(Error::new("reference is {\"@id\": …} or {\"@ref\": …}")),
    }
}

pub(crate) struct Interner {
    pub(crate) local: HashMap<Uuid, usize>,
    pub(crate) ext: Vec<Uuid>,
    pub(crate) ext_index: HashMap<Uuid, usize>,
}

impl Interner {
    pub(crate) fn build(elems: &[Elem]) -> Result<Self, Error> {
        let mut local = HashMap::with_capacity(elems.len());
        for (i, e) in elems.iter().enumerate() {
            if local.insert(e.uuid, i).is_some() {
                return Err(Error::new(format!("duplicate element @id `{}`", e.id)));
            }
        }
        Self::with_locals(local, elems)
    }

    /// An interner over a caller-chosen local index space (the delta
    /// forms seed it with base/created ids); externals are collected
    /// from `elems`' references as in [`Self::build`].
    pub(crate) fn with_locals(local: HashMap<Uuid, usize>, elems: &[Elem]) -> Result<Self, Error> {
        let mut ext = BTreeSet::new();
        for e in elems {
            for (key, value) in e.obj {
                if key == "@id" || key == "@type" {
                    continue;
                }
                let ord = ordinal(e.fields, key)
                    .ok_or_else(|| ctx(e.ty, key, "not a compact-form property"))?;
                let kind = e.fields[ord as usize].1;
                let targets: Box<dyn Iterator<Item = &Value>> = match (kind, value) {
                    (K_REF, v) => Box::new(std::iter::once(v)),
                    (K_REF_LIST, Value::Array(a)) => Box::new(a.iter()),
                    _ => continue,
                };
                for t in targets {
                    if let Some(u) = ref_uuid(t)? {
                        if !local.contains_key(&u) {
                            ext.insert(u);
                        }
                    }
                }
            }
        }
        let ext: Vec<Uuid> = ext.into_iter().collect();
        let ext_index = ext.iter().enumerate().map(|(i, &u)| (u, i)).collect();
        Ok(Self {
            local,
            ext,
            ext_index,
        })
    }

    /// Wire index of a reference target: locals first, then externals.
    pub(crate) fn index(&self, u: Uuid) -> u64 {
        match self.local.get(&u) {
            Some(&i) => i as u64,
            None => (self.local.len() + self.ext_index[&u]) as u64,
        }
    }
}

pub(crate) fn write_ref(w: &mut Writer, interner: &Interner, v: &Value) -> Result<(), Error> {
    match ref_uuid(v)? {
        Some(u) => w.uint(interner.index(u)),
        None => w.tstr(v["@ref"].as_str().unwrap()),
    }
    Ok(())
}

pub(crate) fn write_value(
    w: &mut Writer,
    interner: &Interner,
    ty: &str,
    field: &CborField,
    v: &Value,
) -> Result<(), Error> {
    let (prop, kind, etbl, _) = *field;
    let bad = |what| ctx(ty, prop, what);
    match (kind, v) {
        // An explicit null that is not the field's default.
        (_, Value::Null) => w.null(),
        (K_BOOL, Value::Bool(b)) => w.bool(*b),
        (K_STR | K_ELEMENT_ID, Value::String(s)) => w.tstr(s),
        (K_STR_LIST, Value::Array(a)) => {
            w.array(a.len());
            for s in a {
                w.tstr(s.as_str().ok_or_else(|| bad("string list holds strings"))?);
            }
        }
        (K_REF, Value::Object(_)) => write_ref(w, interner, v)?,
        (K_REF_LIST, Value::Array(a)) => {
            w.array(a.len());
            for t in a {
                write_ref(w, interner, t)?;
            }
        }
        (K_ENUM, Value::String(s)) => {
            let table = ENUM_TABLES[etbl as usize];
            let i = table
                .iter()
                .position(|x| x == s)
                .ok_or_else(|| bad("value in the enum vocabulary"))?;
            w.uint(i as u64);
        }
        (K_LITERAL, Value::Bool(b)) => w.bool(*b),
        (K_LITERAL, Value::String(s)) => w.tstr(s),
        (K_LITERAL, Value::Number(n)) => {
            if let Some(u) = n.as_u64() {
                w.uint(u);
            } else if let Some(i) = n.as_i64() {
                w.int(i);
            } else {
                w.f64(n.as_f64().ok_or_else(|| bad("finite number"))?);
            }
        }
        _ => return Err(bad("value shape matches the field kind")),
    }
    Ok(())
}

pub(crate) fn write_element(
    w: &mut Writer,
    interner: &Interner,
    e: &Elem,
    implied_owners: Option<&[Option<&str>; 2]>,
) -> Result<(), Error> {
    // Presence bits: u64 fast path, byte-string bitmap for the wide
    // full-form field lists (bit i of byte i/8, little-endian).
    let mut bits = vec![0u8; e.fields.len().div_ceil(8)];
    let mut entries: Vec<(u8, &Value)> = Vec::new();
    'keys: for (key, value) in e.obj {
        if key == "@id" || key == "@type" {
            continue;
        }
        if let Some(derived) = implied_owners {
            for (slot, (prop, _)) in OWNER_SLOTS.iter().enumerate() {
                if key != prop {
                    continue;
                }
                let matches = match (derived[slot], value) {
                    (None, Value::Null) => true,
                    (Some(id), Value::Object(o)) => {
                        o.len() == 1 && o.get("@id").and_then(Value::as_str) == Some(id)
                    }
                    _ => false,
                };
                if matches {
                    continue 'keys;
                }
                break;
            }
        }
        // Interner::build verified every key.
        let ord = ordinal(e.fields, key).unwrap();
        let field = &e.fields[ord as usize];
        if default_value(field, e.id).is_some_and(|d| d == *value) {
            bits[ord as usize / 8] |= 1 << (ord % 8);
        } else {
            entries.push((ord, value));
        }
    }
    entries.sort_by_key(|&(ord, _)| ord);
    w.array(3);
    w.uint(e.code as u64);
    if e.fields.len() <= 64 {
        let mut presence = 0u64;
        for (i, b) in bits.iter().enumerate() {
            presence |= (*b as u64) << (i * 8);
        }
        w.uint(presence);
    } else {
        w.bstr(&bits);
    }
    w.map(entries.len());
    for (ord, value) in entries {
        w.uint(ord as u64);
        write_value(w, interner, e.ty, &e.fields[ord as usize], value)?;
    }
    Ok(())
}

/// Validate a unit-structure table against the element count: indices
/// strictly ascending and in range, paths non-empty. `None` for an
/// empty table — absent and empty encode identically.
fn check_units(
    units: &[(usize, String)],
    n_elems: usize,
) -> Result<Option<&[(usize, String)]>, Error> {
    if units.is_empty() {
        return Ok(None);
    }
    let mut prev: Option<usize> = None;
    for (i, path) in units {
        if *i >= n_elems {
            return Err(Error::new(format!("unit root index {i} out of range")));
        }
        if prev.is_some_and(|p| p >= *i) {
            return Err(Error::new("unit root indices not ascending"));
        }
        if path.is_empty() {
            return Err(Error::new("empty unit path"));
        }
        prev = Some(*i);
    }
    Ok(Some(units))
}

fn write_units(w: &mut Writer, units: &[(usize, String)]) {
    w.map(units.len());
    for (i, path) in units {
        w.uint(*i as u64);
        w.tstr(path);
    }
}

/// Per-element derived-owner id strings (`None` = derived null), and
/// the absent-key exception entries `(element index, slot bits)` —
/// the two ingredients [`FLAG_IMPLIED_OWNERS`] encoding needs.
pub(crate) type OwnerPlan<'a> = (Vec<[Option<&'a str>; 2]>, Vec<(u64, u64)>);

pub(crate) fn owner_plan<'a>(value: &'a Value, elems: &[Elem<'a>]) -> OwnerPlan<'a> {
    let arr = value.as_array().expect("elems_of validated the array");
    let owners = derive_owners(arr);
    let derived: Vec<[Option<&str>; 2]> = owners
        .iter()
        .map(|o| o.map(|s| s.map(|j| elems[j].id)))
        .collect();
    let mut exceptions = Vec::new();
    for (i, e) in elems.iter().enumerate() {
        let bits = owner_absent_bits(e);
        if bits != 0 {
            exceptions.push((i as u64, bits));
        }
    }
    (derived, exceptions)
}

/// Absent-key bits for one element: the backpointer slots its
/// metaclass carries but its source JSON does not spell — the states
/// re-derivation must not add.
pub(crate) fn owner_absent_bits(e: &Elem) -> u64 {
    let mut bits = 0u64;
    for (slot, (prop, _)) in OWNER_SLOTS.iter().enumerate() {
        if ordinal(e.fields, prop).is_some() && !e.obj.contains_key(*prop) {
            bits |= owner_bit(slot);
        }
    }
    bits
}

fn write_owner_exceptions(w: &mut Writer, exceptions: &[(u64, u64)]) {
    w.map(exceptions.len());
    for (i, bits) in exceptions {
        w.uint(*i);
        w.uint(*bits);
    }
}

fn encode(
    value: &Value,
    full: bool,
    units: &[(usize, String)],
    implied_owners: bool,
) -> Result<Vec<u8>, Error> {
    let elems = elems_of(value, table_set(full))?;
    let units = check_units(units, elems.len())?;
    let interner = Interner::build(&elems)?;
    let implied = implied_owners && !full;
    let owners = implied.then(|| owner_plan(value, &elems));
    let mut flags = if full { FLAG_FULL_FORM } else { 0 };
    if units.is_some() {
        flags |= FLAG_UNIT_PATHS;
    }
    if implied {
        flags |= FLAG_IMPLIED_OWNERS;
    }
    let mut w = Writer::with_magic();
    w.array(4 + usize::from(implied) + usize::from(units.is_some()));
    w.uint(header_word(flags));
    w.array(interner.ext.len());
    for u in &interner.ext {
        w.bstr(u.as_bytes());
    }
    w.array(elems.len());
    for e in &elems {
        w.bstr(e.uuid.as_bytes());
    }
    w.array(elems.len());
    for (i, e) in elems.iter().enumerate() {
        write_element(&mut w, &interner, e, owners.as_ref().map(|(d, _)| &d[i]))?;
    }
    if let Some((_, exceptions)) = &owners {
        write_owner_exceptions(&mut w, exceptions);
    }
    if let Some(units) = units {
        write_units(&mut w, units);
    }
    Ok(w.into_bytes())
}

/// Encode a compact interchange element array to CBOR. Ownership
/// backpointers travel implied ([`FLAG_IMPLIED_OWNERS`]) — decode
/// re-derives them, Value-identically.
pub fn to_compact_cbor(value: &Value) -> Result<Vec<u8>, Error> {
    encode(value, false, &[], true)
}

/// The digest-space encoding: owners always spelled, no
/// [`FLAG_IMPLIED_OWNERS`]. State digests canonicalize through this,
/// so wire-format elision never moves a digest. Not a wire emitter.
pub(crate) fn to_compact_cbor_canonical(value: &Value) -> Result<Vec<u8>, Error> {
    encode(value, false, &[], false)
}

/// [`to_compact_cbor`] carrying the model's **unit structure**: each
/// entry pairs the element index of a unit's root namespace with that
/// unit's source path, so decoders can lay the model back out as its
/// original files. An empty table encodes exactly like
/// [`to_compact_cbor`].
pub fn to_compact_cbor_with_units(
    value: &Value,
    units: &[(usize, String)],
) -> Result<Vec<u8>, Error> {
    encode(value, false, units, true)
}

/// The digest namespace for [`id_digest`] (fixed, versioned with the
/// wire format).
fn digest_ns() -> Uuid {
    Uuid::new_v5(&Uuid::NAMESPACE_URL, b"sysmlv2-cbor:id-digest")
}

/// The recovered-id integrity digest: `uuid5(DIGEST_NS, id₀ ‖ id₁ ‖ …)`
/// over the final 16-byte ids in element order — exactly the id table
/// a non-elided payload would carry.
pub(crate) fn id_digest(ids: impl Iterator<Item = Uuid>) -> Uuid {
    let mut buf = Vec::new();
    for u in ids {
        buf.extend_from_slice(u.as_bytes());
    }
    Uuid::new_v5(&digest_ns(), &buf)
}

/// [`to_compact_cbor`] with **id elision** (opt-in): ids the
/// receiver can re-derive from the graph (IDS.md) are not shipped —
/// the id table becomes a per-element exception map (roots, foreign
/// ids, underivable elements) plus a mandatory integrity digest the
/// decoder verifies against its recovered ids. `external_name` names
/// reference targets outside the payload (library elements) for the
/// effective-name chains; payloads not typed against a library never
/// consult it. Any payload encodes: a foreign document simply lands
/// entirely in the exception map (≈ the non-elided size).
pub fn to_compact_cbor_elided(
    value: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Vec<u8>, Error> {
    to_compact_cbor_elided_with_units(value, external_name, &[])
}

/// [`to_compact_cbor_elided`] carrying the model's unit structure
/// (see [`to_compact_cbor_with_units`]).
pub fn to_compact_cbor_elided_with_units(
    value: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
    units: &[(usize, String)],
) -> Result<Vec<u8>, Error> {
    let elems = elems_of(value, table_set(false))?;
    let units = check_units(units, elems.len())?;
    let interner = Interner::build(&elems)?;
    let derived = sysmlv2_model::ids::derive_ids(value, external_name).map_err(Error::new)?;
    let exceptions: Vec<(u64, Uuid)> = elems
        .iter()
        .enumerate()
        .filter(|&(i, e)| derived[i] != Some(e.uuid))
        .map(|(i, e)| (i as u64, e.uuid))
        .collect();
    let digest = id_digest(elems.iter().map(|e| e.uuid));
    let (owner_derived, owner_exceptions) = owner_plan(value, &elems);
    let mut flags = FLAG_ELIDE_IDS | FLAG_IMPLIED_OWNERS;
    if units.is_some() {
        flags |= FLAG_UNIT_PATHS;
    }
    let mut w = Writer::with_magic();
    w.array(5 + usize::from(units.is_some()));
    w.uint(header_word(flags));
    w.array(interner.ext.len());
    for u in &interner.ext {
        w.bstr(u.as_bytes());
    }
    // In place of the id table: the exception map + the digest.
    w.array(2);
    w.map(exceptions.len());
    for (i, u) in &exceptions {
        w.uint(*i);
        w.bstr(u.as_bytes());
    }
    w.bstr(digest.as_bytes());
    w.array(elems.len());
    for (i, e) in elems.iter().enumerate() {
        write_element(&mut w, &interner, e, Some(&owner_derived[i]))?;
    }
    write_owner_exceptions(&mut w, &owner_exceptions);
    if let Some(units) = units {
        write_units(&mut w, units);
    }
    Ok(w.into_bytes())
}

/// Encode a **full-form** interchange element array (derived
/// properties + implied relationships, as `to_full_json` emits) to
/// CBOR, in the full ordinal space with the full-form header flag.
/// An emit view for clients that want the materialized element list
/// without running derivation — full-form CBOR is never an ingest
/// format: lift consumes the compact form.
pub fn to_full_cbor(value: &Value) -> Result<Vec<u8>, Error> {
    encode(value, true, &[], false)
}

/// [`to_full_cbor`] carrying the model's unit structure (see
/// [`to_compact_cbor_with_units`]).
pub fn to_full_cbor_with_units(value: &Value, units: &[(usize, String)]) -> Result<Vec<u8>, Error> {
    encode(value, true, units, false)
}
