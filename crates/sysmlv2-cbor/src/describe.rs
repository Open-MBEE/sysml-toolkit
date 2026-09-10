//! **Payload inspection** — say what an s2c payload *is and
//! does* without decoding or applying it. A delta cannot even decode
//! without its base, so this is the only preview a host gets; for
//! snapshots it is a cheap structural walk (element bodies are
//! skipped, not materialized, but the whole payload is walked so a
//! described payload is structurally well-formed).
//!
//! The summary is a JSON object (stable keys, documented on
//! [`describe`]) rather than a struct, because its consumers are
//! hosts across FFI boundaries (wasm, CLI) that want to render it,
//! not compute with it.

use crate::cbor::{Head, Reader};
use crate::delta::{FLAG_DELTA, FLAG_DELTA_PORTABLE};
use crate::encode::{FLAG_ELIDE_IDS, FLAG_FULL_FORM};
use crate::{Error, strip_magic};
use serde_json::{Map, Value, json};
use uuid::Uuid;

/// How many change-target identities the delta summary lists before
/// truncating (the counts stay exact either way).
const TARGET_CAP: usize = 64;

fn uuid16(r: &mut Reader) -> Result<Uuid, Error> {
    Ok(Uuid::from_bytes(r.bstr(16)?.try_into().unwrap()))
}

/// Inspect a payload and return its summary:
///
/// ```json
/// {
///   "form": "compact" | "full" | "delta",
///   "bytes": 1234,
///   "versions": { "layout": 1, "tables": 1, "scheme": 1,
///                 "supported": true },
///   // snapshots:
///   "elements": 91319, "externals": 2, "idsElided": false,
///   "exceptions": 94, "idDigest": "…",          // elided only
///   // deltas:
///   "delta": {
///     "identityMode": "strict" | "portable",
///     "baseDigest": "…", "resultDigest": "…",
///     "claims": [ { "key": 1, "id": "…" } | { "key": 2, "text": "…" } ],
///     "baseElements": 123, "created": 4, "externals": 1,
///     "changes": { "creates": 4, "updates": 2, "deletes": 1 },
///     "patchedUpdates": 1,                        // field-patch update records
///     "idsElided": false,
///     "exceptions": 1, "idDigest": "…",          // elided deltas only
///     "createdIds": ["…"],                        // empty when elided
///     "updateTargets": [...], "deleteTargets": [...],
///     "targetsTruncated": false
///   }
/// }
/// ```
///
/// Change targets are element ids (portable mode) or indices into the
/// digest-pinned canonical base order (strict mode — only meaningful
/// to a holder of the base). Header versions are reported, not gated
/// (only the wire layout must match — without it the structure cannot
/// be read); `versions.supported` says whether this build's decoders
/// would accept the payload outright.
pub fn describe(bytes: &[u8]) -> Result<Value, Error> {
    let mut r = Reader::new(strip_magic(bytes)?);
    let arity = r.array()?;
    let header = r.uint()?;
    if header >> 40 != 0 {
        return Err(Error::new("unrecognized header word"));
    }
    let layout = (header >> 32) as u8;
    let tables = (header >> 16) as u16;
    let scheme = (header >> 8) as u8;
    let flags = header as u8;
    if layout != crate::LAYOUT_VERSION {
        return Err(Error::new(format!(
            "layout version {layout} unsupported (this build carries {})",
            crate::LAYOUT_VERSION
        )));
    }
    let delta = flags & FLAG_DELTA != 0;
    let elided = flags & FLAG_ELIDE_IDS != 0;
    let full = flags & FLAG_FULL_FORM != 0;
    let with_units = flags & crate::FLAG_UNIT_PATHS != 0;
    let implied = flags & crate::FLAG_IMPLIED_OWNERS != 0;
    let known = FLAG_DELTA
        | FLAG_DELTA_PORTABLE
        | FLAG_ELIDE_IDS
        | FLAG_FULL_FORM
        | crate::FLAG_UNIT_PATHS
        | crate::FLAG_IMPLIED_OWNERS;
    if flags & !known != 0 {
        return Err(Error::new(format!("unknown header flags {flags:#x}")));
    }
    let supported = tables == crate::tables::CBOR_TABLES_VERSION
        && (!elided || scheme == crate::ID_SCHEME_VERSION);
    let mut out = Map::new();
    out.insert(
        "form".into(),
        json!(if delta {
            "delta"
        } else if full {
            "full"
        } else {
            "compact"
        }),
    );
    out.insert("bytes".into(), json!(bytes.len()));
    out.insert(
        "versions".into(),
        json!({ "layout": layout, "tables": tables, "scheme": scheme,
                "supported": supported }),
    );

    if !delta {
        let expect_arity = 4 + usize::from(implied) + usize::from(with_units);
        if arity != expect_arity {
            return Err(Error::new(format!(
                "payload is array({expect_arity}) for these header flags"
            )));
        }
        out.insert("idsElided".into(), json!(elided));
        out.insert("impliedOwners".into(), json!(implied));
        let n_ext = r.array()?;
        if n_ext > r.remaining() / 17 {
            return Err(Error::new("UUID table longer than payload"));
        }
        for _ in 0..n_ext {
            r.bstr(16)?;
        }
        out.insert("externals".into(), json!(n_ext));
        if elided {
            if r.array()? != 2 {
                return Err(Error::new("elided id section is array(2)"));
            }
            let m = match r.head()? {
                Head::Map(m) if m <= r.remaining() / 18 => m,
                Head::Map(_) => return Err(Error::new("exception map longer than payload")),
                _ => return Err(Error::new("exception map expected")),
            };
            for _ in 0..m {
                r.uint()?;
                r.bstr(16)?;
            }
            out.insert("exceptions".into(), json!(m));
            out.insert("idDigest".into(), json!(uuid16(&mut r)?.to_string()));
        } else {
            let n = r.array()?;
            if n > r.remaining() / 17 {
                return Err(Error::new("UUID table longer than payload"));
            }
            for _ in 0..n {
                r.bstr(16)?;
            }
        }
        let elements = r.array()?;
        if elements > r.remaining() {
            return Err(Error::new("element count longer than payload"));
        }
        out.insert("elements".into(), json!(elements));
        r.skip_items(elements as u64)?;
        if implied {
            // Owner exceptions: element index → absent-key bits.
            let m = match r.head()? {
                Head::Map(m) if m <= r.remaining() / 2 => m,
                Head::Map(_) => return Err(Error::new("owner-exception map longer than payload")),
                _ => return Err(Error::new("owner-exception map expected")),
            };
            for _ in 0..m {
                r.uint()?;
                r.uint()?;
            }
            out.insert("ownerExceptions".into(), json!(m));
        }
        if with_units {
            // Unit structure: root element index → source path.
            let m = match r.head()? {
                Head::Map(m) if m <= r.remaining() / 2 => m,
                Head::Map(_) => return Err(Error::new("unit-path map longer than payload")),
                _ => return Err(Error::new("unit-path map expected")),
            };
            let mut units = Vec::with_capacity(m);
            for _ in 0..m {
                let index = r.uint()?;
                let path = match r.head()? {
                    Head::Tstr(n) => r.tstr_body(n)?.to_owned(),
                    _ => return Err(Error::new("unit path is a text string")),
                };
                units.push(json!({ "index": index, "path": path }));
            }
            out.insert("units".into(), json!(units));
        }
        if !r.done() {
            return Err(Error::new("trailing bytes after payload"));
        }
        return Ok(Value::Object(out));
    }

    // Delta payload.
    let expect_arity = 6 + usize::from(implied) + usize::from(with_units);
    if arity != expect_arity {
        return Err(Error::new(format!(
            "delta payload is array({expect_arity}) for these header flags"
        )));
    }
    let portable = flags & FLAG_DELTA_PORTABLE != 0;
    if r.array()? != 3 {
        return Err(Error::new("base section is array(3)"));
    }
    let base_digest = uuid16(&mut r)?;
    let result_digest = uuid16(&mut r)?;
    let n_claims = match r.head()? {
        Head::Map(m) if m <= r.remaining() / 2 => m,
        Head::Map(_) => return Err(Error::new("claims map longer than payload")),
        _ => return Err(Error::new("claims are a map")),
    };
    let mut claims = Vec::with_capacity(n_claims);
    for _ in 0..n_claims {
        let key = r.uint()?;
        match r.head()? {
            Head::Bstr(16) => claims.push(json!({ "key": key,
                "id": Uuid::from_bytes(r.take(16)?.try_into().unwrap()).to_string() })),
            Head::Tstr(n) => claims.push(json!({ "key": key, "text": r.tstr_body(n)? })),
            _ => return Err(Error::new("claim is bstr(16) or text")),
        }
    }
    let base_elements = r.uint()?;
    let n_ext = r.array()?;
    if n_ext > r.remaining() / 17 {
        return Err(Error::new("UUID table longer than payload"));
    }
    for _ in 0..n_ext {
        r.bstr(16)?;
    }
    // Created ids: the id table, or (elided) count + exception map +
    // recovered-id digest — the ids themselves are not in the payload.
    let mut created_ids = Vec::new();
    let mut exceptions: Option<usize> = None;
    let mut id_digest: Option<Uuid> = None;
    let n_created = if elided {
        if r.array()? != 3 {
            return Err(Error::new("elided created-id section is array(3)"));
        }
        let n = r.uint()? as usize;
        if n > r.remaining() {
            return Err(Error::new("created count longer than payload"));
        }
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 18 => m,
            Head::Map(_) => return Err(Error::new("exception map longer than payload")),
            _ => return Err(Error::new("exception map expected")),
        };
        for _ in 0..m {
            r.uint()?;
            r.bstr(16)?;
        }
        exceptions = Some(m);
        id_digest = Some(uuid16(&mut r)?);
        n
    } else {
        let n = r.array()?;
        if n > r.remaining() / 17 {
            return Err(Error::new("UUID table longer than payload"));
        }
        for i in 0..n {
            let u = uuid16(&mut r)?;
            if i < TARGET_CAP {
                created_ids.push(json!(u.to_string()));
            }
        }
        n
    };
    let n_changes = match r.head()? {
        Head::Array(k) if k <= r.remaining() => k,
        Head::Array(_) => return Err(Error::new("change list longer than payload")),
        _ => return Err(Error::new("changes are an array")),
    };
    let (mut creates, mut updates, mut deletes) = (0usize, 0usize, 0usize);
    let mut patched_updates = 0usize;
    let mut update_targets = Vec::new();
    let mut delete_targets = Vec::new();
    for _ in 0..n_changes {
        if r.array()? != 2 {
            return Err(Error::new("change record is array(2)"));
        }
        // Identity: null (create), uint index (strict), id bytes (portable).
        let identity: Option<Value> = match r.head()? {
            Head::Null => None,
            Head::Uint(i) if !portable => Some(json!(i)),
            Head::Bstr(16) if portable => Some(json!(
                Uuid::from_bytes(r.take(16)?.try_into().unwrap()).to_string()
            )),
            _ => return Err(Error::new("change identity is an index, id bytes, or null")),
        };
        // Payload: null (delete) or an element record (array(3)).
        match r.head()? {
            Head::Null => match identity {
                Some(id) => {
                    deletes += 1;
                    if delete_targets.len() < TARGET_CAP {
                        delete_targets.push(id);
                    }
                }
                None => return Err(Error::new("create record carries no delete")),
            },
            Head::Array(3) => match identity {
                Some(id) => {
                    updates += 1;
                    if update_targets.len() < TARGET_CAP {
                        update_targets.push(id);
                    }
                    r.skip_items(3)?;
                }
                None => {
                    creates += 1;
                    r.skip_items(3)?;
                }
            },
            // Field-patch update: map of ordinal → op pairs.
            Head::Map(m) => match identity {
                Some(id) => {
                    updates += 1;
                    patched_updates += 1;
                    if update_targets.len() < TARGET_CAP {
                        update_targets.push(id);
                    }
                    r.skip_items(2 * m as u64)?;
                }
                None => return Err(Error::new("patch record carries no create")),
            },
            _ => return Err(Error::new("change payload is an element or null")),
        }
    }
    // Owner exceptions: change-record ordinal → absent-key
    // bits on records that shipped whole elements.
    let mut owner_exceptions: Option<usize> = None;
    if implied {
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 2 => m,
            Head::Map(_) => return Err(Error::new("owner-exception map longer than payload")),
            _ => return Err(Error::new("owner-exception map expected")),
        };
        for _ in 0..m {
            r.uint()?;
            r.uint()?;
        }
        owner_exceptions = Some(m);
    }
    // Units section: result element index → source path.
    let mut units = Vec::new();
    if with_units {
        let m = match r.head()? {
            Head::Map(m) if m <= r.remaining() / 2 => m,
            Head::Map(_) => return Err(Error::new("unit-path map longer than payload")),
            _ => return Err(Error::new("unit-path map expected")),
        };
        for _ in 0..m {
            let index = r.uint()?;
            let path = match r.head()? {
                Head::Tstr(n) => r.tstr_body(n)?.to_owned(),
                _ => return Err(Error::new("unit path is a text string")),
            };
            units.push(json!({ "index": index, "path": path }));
        }
    }
    if !r.done() {
        return Err(Error::new("trailing bytes after payload"));
    }
    let truncated = creates > TARGET_CAP || updates > TARGET_CAP || deletes > TARGET_CAP;
    let mut d = json!({
        "identityMode": if portable { "portable" } else { "strict" },
        "baseDigest": base_digest.to_string(),
        "resultDigest": result_digest.to_string(),
        "claims": claims,
        "baseElements": base_elements,
        "created": n_created,
        "externals": n_ext,
        "changes": { "creates": creates, "updates": updates, "deletes": deletes },
        "patchedUpdates": patched_updates,
        "idsElided": elided,
        "createdIds": created_ids,
        "updateTargets": update_targets,
        "deleteTargets": delete_targets,
        "targetsTruncated": truncated,
        "impliedOwners": implied,
    });
    if let (Some(m), Some(u)) = (exceptions, id_digest) {
        let o = d.as_object_mut().unwrap();
        o.insert("exceptions".into(), json!(m));
        o.insert("idDigest".into(), json!(u.to_string()));
    }
    if let Some(m) = owner_exceptions {
        d.as_object_mut()
            .unwrap()
            .insert("ownerExceptions".into(), json!(m));
    }
    if with_units {
        d.as_object_mut()
            .unwrap()
            .insert("units".into(), json!(units));
    }
    out.insert("delta".into(), d);
    Ok(Value::Object(out))
}
