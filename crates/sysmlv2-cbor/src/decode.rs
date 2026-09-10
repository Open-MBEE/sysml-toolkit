//! CBOR payload → compact element array (`serde_json::Value`),
//! byte-for-byte inverse of [`crate::encode`]: presence bits
//! re-materialize default values (including the `elementId` mirror),
//! ordinal keys re-expand to property names, reference indices
//! re-expand to `{"@id": …}` objects, `@ref` text survives verbatim.

use crate::Error;
use crate::cbor::{Head, Reader};
use crate::encode::{
    FLAG_ELIDE_IDS, FLAG_FULL_FORM, FLAG_IMPLIED_OWNERS, FLAG_UNIT_PATHS, OWNER_SLOTS,
    derive_owners, owner_bit, table_set,
};
use crate::tables::{
    CBOR_TABLES_VERSION, CborField, ENUM_TABLES, K_ENUM, K_LITERAL, K_REF, K_REF_LIST, K_STR_LIST,
};
use serde_json::{Map, Number, Value, json};
use uuid::Uuid;

/// Presence bits: u64 for field lists that fit, byte-string bitmap for
/// the wide full-form lists (bit i of byte i/8, little-endian).
enum Presence<'a> {
    Small(u64),
    Big(&'a [u8]),
}

impl Presence<'_> {
    fn get(&self, i: usize) -> bool {
        match self {
            Presence::Small(bits) => i < 64 && bits >> i & 1 != 0,
            Presence::Big(bytes) => bytes[i / 8] >> (i % 8) & 1 != 0,
        }
    }

    fn validate(&self, n_fields: usize, ty: &str) -> Result<(), Error> {
        let ok = match self {
            Presence::Small(bits) => n_fields >= 64 || bits >> n_fields == 0,
            Presence::Big(bytes) => {
                bytes.len() == n_fields.div_ceil(8)
                    && (n_fields % 8 == 0 || bytes[n_fields / 8] >> (n_fields % 8) == 0)
            }
        };
        if ok {
            Ok(())
        } else {
            Err(Error::new(format!("{ty}: presence bits out of range")))
        }
    }
}

pub(crate) fn read_uuid_table(r: &mut Reader, n: usize) -> Result<Vec<String>, Error> {
    // Each entry takes a 1-byte head + 16 UUID bytes.
    if n > r.remaining() / 17 {
        return Err(Error::new("UUID table longer than payload"));
    }
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let b: [u8; 16] = r.bstr(16)?.try_into().unwrap();
        out.push(Uuid::from_bytes(b).to_string());
    }
    Ok(out)
}

pub(crate) struct Tables<'a> {
    pub(crate) ids: &'a [String],
    pub(crate) exts: &'a [String],
}

impl Tables<'_> {
    pub(crate) fn reference(&self, index: u64) -> Result<Value, Error> {
        let i = index as usize;
        let id = self
            .ids
            .get(i)
            .or_else(|| self.exts.get(i.wrapping_sub(self.ids.len())))
            .ok_or_else(|| Error::new(format!("reference index {index} out of range")))?;
        Ok(json!({ "@id": id }))
    }
}

fn read_string(r: &mut Reader) -> Result<String, Error> {
    match r.head()? {
        Head::Tstr(n) => Ok(r.tstr_body(n)?.to_owned()),
        _ => Err(Error::new("expected text string")),
    }
}

pub(crate) fn read_value(r: &mut Reader, t: &Tables, field: &CborField) -> Result<Value, Error> {
    let (prop, kind, etbl, _) = *field;
    let head = r.head()?;
    // An explicit null is legal for any field kind (a non-default null).
    if head == Head::Null {
        return Ok(Value::Null);
    }
    Ok(match (kind, head) {
        (K_REF, Head::Uint(i)) => t.reference(i)?,
        (K_REF, Head::Tstr(n)) => json!({ "@ref": r.tstr_body(n)? }),
        (K_REF_LIST, Head::Array(len)) => {
            if len > r.remaining() {
                return Err(Error::new(format!("{prop}: list longer than payload")));
            }
            let mut a = Vec::with_capacity(len);
            for _ in 0..len {
                a.push(match r.head()? {
                    Head::Uint(i) => t.reference(i)?,
                    Head::Tstr(n) => json!({ "@ref": r.tstr_body(n)? }),
                    _ => return Err(Error::new(format!("{prop}: bad reference item"))),
                });
            }
            Value::Array(a)
        }
        (K_STR_LIST, Head::Array(len)) => {
            if len > r.remaining() {
                return Err(Error::new(format!("{prop}: list longer than payload")));
            }
            let mut a = Vec::with_capacity(len);
            for _ in 0..len {
                a.push(Value::String(read_string(r)?));
            }
            Value::Array(a)
        }
        (K_ENUM, Head::Uint(i)) => {
            let table = ENUM_TABLES[etbl as usize];
            let s = *table
                .get(i as usize)
                .ok_or_else(|| Error::new(format!("{prop}: enum index {i} out of range")))?;
            Value::String(s.to_owned())
        }
        (K_LITERAL, Head::Uint(u)) => Value::Number(Number::from(u)),
        (K_LITERAL, Head::NInt(a)) => {
            let v = i64::try_from(a)
                .ok()
                .and_then(|a| (-1i64).checked_sub(a))
                .ok_or_else(|| Error::new(format!("{prop}: integer out of range")))?;
            Value::Number(Number::from(v))
        }
        (K_LITERAL, Head::F64(f)) => Value::Number(
            Number::from_f64(f).ok_or_else(|| Error::new(format!("{prop}: non-finite number")))?,
        ),
        (_, Head::True) => Value::Bool(true),
        (_, Head::False) => Value::Bool(false),
        (_, Head::Tstr(n)) => Value::String(r.tstr_body(n)?.to_owned()),
        _ => {
            return Err(Error::new(format!(
                "{prop}: value does not match field kind"
            )));
        }
    })
}

pub(crate) fn read_element(
    r: &mut Reader,
    t: &Tables,
    tables: &'static [(&'static str, &'static [CborField])],
    id: &str,
) -> Result<Value, Error> {
    if r.array()? != 3 {
        return Err(Error::new("element is array(3)"));
    }
    read_element_body(r, t, tables, id)
}

/// [`read_element`] after its `array(3)` head has been consumed — the
/// delta reader peeks that head to tell an element payload from a
/// delete marker.
pub(crate) fn read_element_body(
    r: &mut Reader,
    t: &Tables,
    tables: &'static [(&'static str, &'static [CborField])],
    id: &str,
) -> Result<Value, Error> {
    let code = r.uint()?;
    let (ty, fields) = tables
        .get(code as usize)
        .ok_or_else(|| Error::new(format!("type code {code} out of range")))?;
    let presence = match r.head()? {
        Head::Uint(bits) => Presence::Small(bits),
        Head::Bstr(n) => Presence::Big(r.take(n)?),
        _ => return Err(Error::new(format!("{ty}: presence is uint or bytes"))),
    };
    presence.validate(fields.len(), ty)?;
    let mut obj = Map::new();
    obj.insert("@id".into(), Value::String(id.to_owned()));
    obj.insert("@type".into(), Value::String((*ty).to_owned()));
    let entries = match r.head()? {
        Head::Map(n) => n,
        _ => return Err(Error::new("element fields are a map")),
    };
    let mut prev: i32 = -1;
    for _ in 0..entries {
        let ord = r.uint()?;
        if ord as i32 <= prev {
            return Err(Error::new(format!("{ty}: field ordinals not ascending")));
        }
        prev = ord as i32;
        let field = fields
            .get(ord as usize)
            .ok_or_else(|| Error::new(format!("{ty}: field ordinal {ord} out of range")))?;
        if presence.get(ord as usize) {
            return Err(Error::new(format!(
                "{ty}.{}: both presence bit and value",
                field.0
            )));
        }
        obj.insert(field.0.to_owned(), read_value(r, t, field)?);
    }
    for (ord, field) in fields.iter().enumerate() {
        if !presence.get(ord) {
            continue;
        }
        if field.1 == K_LITERAL {
            return Err(Error::new(format!(
                "{ty}.{}: literal has no default",
                field.0
            )));
        }
        let default = crate::encode::default_value(field, id).unwrap();
        obj.insert(field.0.to_owned(), default);
    }
    Ok(Value::Object(obj))
}

/// Placeholder `@id` for element `k` during elided decode (the delta
/// reader keys it by created ordinal); replaced by the recovered id
/// before the Value leaves this crate. Version digit 8 keeps the space
/// disjoint from real v4/v5 ids.
pub(crate) fn placeholder(k: usize) -> String {
    format!("ffffffff-ffff-8fff-8fff-{k:012x}")
}

/// Targeted rewrite of placeholder ids: `@id`/`elementId` values and
/// `{"@id": …}` reference objects only — never arbitrary strings.
pub(crate) fn patch_placeholders(v: &mut Value, map: &std::collections::HashMap<String, String>) {
    match v {
        Value::Array(a) => a.iter_mut().for_each(|x| patch_placeholders(x, map)),
        Value::Object(o) => {
            for (k, val) in o.iter_mut() {
                match val {
                    Value::String(s) if k == "@id" || k == "elementId" => {
                        if let Some(real) = map.get(s) {
                            *val = Value::String(real.clone());
                        }
                    }
                    _ => patch_placeholders(val, map),
                }
            }
        }
        _ => {}
    }
}

type Resolver<'a> = &'a dyn Fn(&str) -> Option<String>;

/// Unpack and gate the header word
/// (`layout u8 · tables u16 · scheme u8 · flags u8`): the layout axis
/// refuses unconditionally; the tables axis refuses because every
/// decode reads element records through the generated tables; the
/// scheme axis is returned `(scheme, flags)` for the caller to gate
/// only where id derivation is actually in play.
pub(crate) fn parse_header(header: u64) -> Result<(u8, u8), Error> {
    if header >> 40 != 0 {
        return Err(Error::new("unrecognized header word"));
    }
    let layout = (header >> 32) as u8;
    let tables = (header >> 16) as u16;
    let scheme = (header >> 8) as u8;
    let flags = header as u8;
    if layout != crate::LAYOUT_VERSION {
        return Err(Error::new(format!(
            "layout version {layout} unsupported (decoder carries {})",
            crate::LAYOUT_VERSION
        )));
    }
    if tables != CBOR_TABLES_VERSION {
        return Err(Error::new(format!(
            "table version {tables} unsupported (decoder carries {CBOR_TABLES_VERSION})"
        )));
    }
    Ok((scheme, flags))
}

fn decode(
    bytes: &[u8],
    expect_full: Option<bool>,
    resolver: Option<Resolver>,
) -> Result<(Value, Vec<(u64, String)>), Error> {
    let mut r = Reader::new(crate::strip_magic(bytes)?);
    // Read the arity and header before judging shape, so a delta
    // payload (array(6)) gets its pointed message instead of a bare
    // arity complaint.
    let arity = r.array()?;
    let (scheme, flags) = parse_header(r.uint()?)?;
    if flags & crate::delta::FLAG_DELTA != 0 {
        return Err(Error::new(
            "delta payload; apply with apply_delta_cbor against its base",
        ));
    }
    if flags & !(FLAG_ELIDE_IDS | FLAG_FULL_FORM | FLAG_UNIT_PATHS | FLAG_IMPLIED_OWNERS) != 0 {
        return Err(Error::new(format!("unknown header flags {flags:#x}")));
    }
    let with_units = flags & FLAG_UNIT_PATHS != 0;
    let implied = flags & FLAG_IMPLIED_OWNERS != 0;
    let expect_arity = 4 + usize::from(implied) + usize::from(with_units);
    if arity != expect_arity {
        return Err(Error::new(format!(
            "payload is array({expect_arity}) for these header flags"
        )));
    }
    let full = flags & FLAG_FULL_FORM != 0;
    let elided = flags & FLAG_ELIDE_IDS != 0;
    if implied && full {
        return Err(Error::new("owner elision applies to the compact form only"));
    }
    // The derivation-scheme axis gates only payloads that actually
    // derive ids; explicit-id payloads decode regardless of it.
    if elided && scheme != crate::ID_SCHEME_VERSION {
        return Err(Error::new(format!(
            "id-derivation scheme {scheme} unsupported (decoder carries {}); \
             the payload's ids cannot be recovered here",
            crate::ID_SCHEME_VERSION
        )));
    }
    match expect_full {
        Some(false) if full => {
            return Err(Error::new(
                "full-form payload; decode with from_full_cbor (compact is the ingest form)",
            ));
        }
        Some(true) if !full => {
            return Err(Error::new("compact payload; decode with from_compact_cbor"));
        }
        _ => {}
    }
    if elided && full {
        return Err(Error::new("id elision applies to the compact form only"));
    }
    let resolver = if elided {
        Some(resolver.ok_or_else(|| {
            Error::new(
                "id-elided payload; decode with from_compact_cbor_elided (or from_cbor_with) \
                 and, for library-typed models, the library name resolver",
            )
        })?)
    } else {
        None
    };
    let field_tables = table_set(full);
    let n_ext = r.array()?;
    let exts = read_uuid_table(&mut r, n_ext)?;

    // Id section: the id table, or (elided) the exception map + digest.
    let mut exceptions: Vec<(u64, Uuid)> = Vec::new();
    let mut digest: Option<Uuid> = None;
    let mut ids: Vec<String> = Vec::new();
    if elided {
        if r.array()? != 2 {
            return Err(Error::new("elided id section is array(2)"));
        }
        let m = match r.head()? {
            Head::Map(m) => m,
            _ => return Err(Error::new("exception map expected")),
        };
        if m > r.remaining() / 18 {
            return Err(Error::new("exception map longer than payload"));
        }
        let mut prev: i64 = -1;
        for _ in 0..m {
            let k = r.uint()?;
            if k as i64 <= prev {
                return Err(Error::new("exception indices not ascending"));
            }
            prev = k as i64;
            let b: [u8; 16] = r.bstr(16)?.try_into().unwrap();
            exceptions.push((k, Uuid::from_bytes(b)));
        }
        let d: [u8; 16] = r.bstr(16)?.try_into().unwrap();
        digest = Some(Uuid::from_bytes(d));
    } else {
        let n = r.array()?;
        ids = read_uuid_table(&mut r, n)?;
    }

    let n = r.array()?;
    if elided {
        if n > r.remaining() {
            return Err(Error::new("element count longer than payload"));
        }
        ids = (0..n).map(placeholder).collect();
        if exceptions.last().is_some_and(|&(k, _)| k as usize >= n) {
            return Err(Error::new("exception index out of range"));
        }
    } else if ids.len() != n {
        return Err(Error::new("element count differs from id table"));
    }
    let tables = Tables {
        ids: &ids,
        exts: &exts,
    };
    let mut out = Vec::with_capacity(n);
    for id in &ids {
        out.push(read_element(&mut r, &tables, field_tables, id)?);
    }
    // Owner exceptions (FLAG_IMPLIED_OWNERS): element index →
    // absent-key bits — the elements whose source JSON lacked the
    // backpointer key entirely, which re-derivation must not add.
    let mut owner_exceptions: std::collections::HashMap<usize, u64> =
        std::collections::HashMap::new();
    if implied {
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 2 => m,
            Head::Map(_) => return Err(Error::new("owner-exception map longer than payload")),
            _ => return Err(Error::new("owner-exception map expected")),
        };
        let mut prev: i64 = -1;
        for _ in 0..m {
            let k = r.uint()?;
            if k as i64 <= prev {
                return Err(Error::new("owner-exception indices not ascending"));
            }
            if k as usize >= n {
                return Err(Error::new("owner-exception index out of range"));
            }
            prev = k as i64;
            let bits = r.uint()?;
            if bits == 0 || bits > 3 {
                return Err(Error::new("owner-exception bits out of range"));
            }
            owner_exceptions.insert(k as usize, bits);
        }
    }
    // Unit structure: element index of each unit's root namespace →
    // that unit's source path.
    let mut units: Vec<(u64, String)> = Vec::new();
    if with_units {
        let m = match r.head()? {
            Head::Map(m) => m,
            _ => return Err(Error::new("unit-path map expected")),
        };
        if m > r.remaining() / 2 {
            return Err(Error::new("unit-path map longer than payload"));
        }
        let mut prev: i64 = -1;
        for _ in 0..m {
            let k = r.uint()?;
            if k as i64 <= prev {
                return Err(Error::new("unit root indices not ascending"));
            }
            if k as usize >= n {
                return Err(Error::new("unit root index out of range"));
            }
            prev = k as i64;
            units.push((k, read_string(&mut r)?));
        }
    }
    if !r.done() {
        return Err(Error::new("trailing bytes after payload"));
    }
    let mut value = Value::Array(out);

    if implied {
        // Re-materialize implied backpointers: derivation over the
        // decoded forward lists (identical rule to the encoder — under
        // id elision both sides run it over placeholder ids, which is
        // fine: the rule only matches ids within the payload). An
        // explicitly spelled value always wins; an absent-key
        // exception keeps the key absent.
        let owners = derive_owners(value.as_array().unwrap());
        let arr = value.as_array_mut().unwrap();
        for (i, e) in arr.iter_mut().enumerate() {
            let exc = owner_exceptions.get(&i).copied().unwrap_or(0);
            let obj = e.as_object_mut().unwrap();
            let ty = obj["@type"].as_str().unwrap();
            let code = field_tables
                .binary_search_by(|(t, _)| t.cmp(&ty))
                .expect("decoded @type is in the tables");
            let fields = field_tables[code].1;
            for (slot, (prop, _)) in OWNER_SLOTS.iter().enumerate() {
                if crate::ordinal(fields, prop).is_none()
                    || exc & owner_bit(slot) != 0
                    || obj.contains_key(*prop)
                {
                    continue;
                }
                let derived = match owners[i][slot] {
                    Some(j) => json!({ "@id": ids[j] }),
                    None => Value::Null,
                };
                obj.insert((*prop).to_owned(), derived);
            }
        }
    }

    if let Some(external_name) = resolver {
        // Recover the elided ids: exceptions override, everything else
        // derives (IDS.md); then the digest must hold — a mismatch
        // means library skew (the effective-name chains resolved
        // against a different library), derivation drift across codec
        // versions, or exception-map corruption. Never continue.
        let exceptions: std::collections::HashMap<usize, Uuid> = exceptions
            .into_iter()
            .map(|(k, u)| (k as usize, u))
            .collect();
        let finals = sysmlv2_model::ids::assign_ids(&value, &exceptions, external_name)
            .map_err(Error::new)?;
        let expect = digest.unwrap();
        let got = crate::encode::id_digest(finals.iter().copied());
        if got != expect {
            return Err(Error::new(
                "recovered ids do not match the payload digest — the encoder and decoder \
                 disagree on id derivation (likely causes, most common first: different \
                 standard-library versions on each side; id-derivation drift between codec \
                 versions; a corrupted exception map)",
            ));
        }
        let map: std::collections::HashMap<String, String> = finals
            .iter()
            .enumerate()
            .map(|(k, u)| (placeholder(k), u.to_string()))
            .collect();
        patch_placeholders(&mut value, &map);
    }
    Ok((value, units))
}

/// Decode a compact-form CBOR payload back to the compact interchange
/// element array. Refuses full-form payloads (compact is the ingest
/// form; expand at the edge only) and id-elided payloads (those need
/// a resolver — [`from_compact_cbor_elided`]).
pub fn from_compact_cbor(bytes: &[u8]) -> Result<Value, Error> {
    Ok(decode(bytes, Some(false), None)?.0)
}

/// [`from_compact_cbor`] accepting **id-elided** payloads:
/// elided ids re-derive from the graph, exceptions override, and the
/// payload digest must match the recovered id sequence — a mismatch is
/// a hard error. `external_name` names reference targets outside the
/// payload (library elements) for the effective-name chains; pass
/// `&|_| None` for payloads not typed against a library.
pub fn from_compact_cbor_elided(
    bytes: &[u8],
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Value, Error> {
    Ok(decode(bytes, Some(false), Some(&external_name))?.0)
}

/// Decode a **full-form** CBOR payload back to the full interchange
/// element array — for clients that consume the materialized element
/// list directly. Never an ingest path: lift consumes the compact form.
pub fn from_full_cbor(bytes: &[u8]) -> Result<Value, Error> {
    Ok(decode(bytes, Some(true), None)?.0)
}

/// Decode either form, whichever the header flags declare. The
/// convert pipeline uses this for `.cbor` inputs (a decoded full form
/// then normalizes to compact exactly like full JSON input). Id-elided
/// payloads need [`from_cbor_with`].
pub fn from_cbor(bytes: &[u8]) -> Result<Value, Error> {
    Ok(decode(bytes, None, None)?.0)
}

/// [`from_cbor`] with a resolver, accepting id-elided payloads too.
pub fn from_cbor_with(
    bytes: &[u8],
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<Value, Error> {
    Ok(decode(bytes, None, Some(&external_name))?.0)
}

/// [`from_cbor_with`] also returning the payload's **unit structure**
/// when it carries one (`FLAG_UNIT_PATHS`): pairs of (element index of
/// a unit's root namespace, that unit's source path), in index order.
/// Empty for payloads without the section.
pub fn from_cbor_with_units(
    bytes: &[u8],
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<(Value, Vec<(u64, String)>), Error> {
    decode(bytes, None, Some(&external_name))
}

/// [`from_compact_cbor`] also returning the payload's unit structure
/// (see [`from_cbor_with_units`]).
pub fn from_compact_cbor_units(bytes: &[u8]) -> Result<(Value, Vec<(u64, String)>), Error> {
    decode(bytes, Some(false), None)
}
