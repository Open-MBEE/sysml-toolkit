//! Standard-library resolver artifact, consumer side: load the
//! versioned JSON artifact and resolve library references — **no
//! `Model`, no library cache, no library sources**. Pure parsing over
//! the artifact bytes, so it serves native services and wasm hosts
//! identically.
//!
//! What it answers:
//! - [`StdlibResolver::external_name`] — id → last effective-name
//!   segment: exactly the resolver id-elided decode and owner
//!   derivation consult ([`crate::from_cbor_with`] and friends).
//! - [`StdlibResolver::segments`] — id → full qualified-name segments.
//! - [`StdlibResolver::id_of`] — element qualified name → id (the
//!   full-form completion direction). Membership/alias entries are
//!   deliberately absent here, and names listed in the artifact's
//!   collision set resolve to `None` while [`StdlibResolver::
//!   is_collision`] reports them — loud, never nondeterministic.
//!
//! Pinning: an artifact binds to an exact library state (its compact
//! export's state digest) and the codec table/scheme versions it was
//! generated under. [`StdlibResolver::assert_compatible`] refuses a
//! mismatch with this build; comparing [`StdlibResolver::
//! library_state_digest`] against a store's pinned stdlib commit
//! digest is the caller's binding check.

use crate::{Error, ErrorKind};
use serde_json::Value;
use std::collections::{HashMap, HashSet};

/// A loaded, validated resolver artifact.
pub struct StdlibResolver {
    toolkit: String,
    tables_version: u16,
    scheme_version: u8,
    library_state_digest: String,
    units: usize,
    forward: HashMap<String, Vec<String>>,
    inverse: HashMap<String, String>,
    collisions: HashSet<String>,
}

impl StdlibResolver {
    pub fn from_json_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let v: Value = serde_json::from_slice(bytes)
            .map_err(|e| Error::new(format!("resolver artifact is JSON: {e}")))?;
        Self::from_value(&v)
    }

    pub fn from_value(v: &Value) -> Result<Self, Error> {
        let str_field = |key: &str| -> Result<String, Error> {
            v.get(key)
                .and_then(Value::as_str)
                .map(str::to_owned)
                .ok_or_else(|| Error::new(format!("resolver artifact carries `{key}`")))
        };
        if str_field("format")? != "sysmlv2-stdlib-resolver" {
            return Err(Error::new("not a stdlib resolver artifact"));
        }
        let version = v.get("formatVersion").and_then(Value::as_u64).unwrap_or(0);
        if version != 1 {
            return Err(Error::of(
                ErrorKind::UnsupportedVersion,
                format!(
                    "resolver artifact format version {version} unsupported \
                     (this build carries 1)"
                ),
            ));
        }
        let uint = |key: &str| -> Result<u64, Error> {
            v.get(key)
                .and_then(Value::as_u64)
                .ok_or_else(|| Error::new(format!("resolver artifact carries `{key}`")))
        };
        let forward_value = v
            .get("forward")
            .and_then(Value::as_object)
            .ok_or_else(|| Error::new("resolver artifact carries a `forward` map"))?;
        let mut forward = HashMap::with_capacity(forward_value.len());
        for (id, segments) in forward_value {
            let segments: Vec<String> = segments
                .as_array()
                .ok_or_else(|| Error::new(format!("forward[{id}] is a segment array")))?
                .iter()
                .map(|s| {
                    s.as_str()
                        .map(str::to_owned)
                        .ok_or_else(|| Error::new(format!("forward[{id}] segments are strings")))
                })
                .collect::<Result<_, _>>()?;
            if segments.is_empty() {
                return Err(Error::new(format!(
                    "forward[{id}] has at least one segment"
                )));
            }
            forward.insert(id.clone(), segments);
        }
        let inverse_value = v
            .get("inverse")
            .and_then(Value::as_object)
            .ok_or_else(|| Error::new("resolver artifact carries an `inverse` map"))?;
        let inverse: HashMap<String, String> = inverse_value
            .iter()
            .map(|(qname, id)| {
                id.as_str()
                    .map(|s| (qname.clone(), s.to_owned()))
                    .ok_or_else(|| Error::new(format!("inverse[{qname}] is an id string")))
            })
            .collect::<Result<_, _>>()?;
        let collisions: HashSet<String> = v
            .get("collisions")
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(Value::as_str)
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default();
        // Each version axis is compared against this build's, so a
        // value that does not fit its width must refuse rather than
        // narrow into a version it is not (65537 is not tables
        // version 1).
        let tables_version = uint("tablesVersion")?;
        let scheme_version = uint("schemeVersion")?;
        let units = uint("units")?;
        Ok(Self {
            toolkit: str_field("toolkit")?,
            tables_version: u16::try_from(tables_version)
                .map_err(|_| Error::new("resolver artifact `tablesVersion` is out of range"))?,
            scheme_version: u8::try_from(scheme_version)
                .map_err(|_| Error::new("resolver artifact `schemeVersion` is out of range"))?,
            library_state_digest: str_field("libraryStateDigest")?,
            units: usize::try_from(units)
                .map_err(|_| Error::new("resolver artifact `units` is out of range"))?,
            forward,
            inverse,
            collisions,
        })
    }

    /// Refuse an artifact generated under different codec axes than
    /// this build decodes with — same doctrine as the wire header.
    pub fn assert_compatible(&self) -> Result<(), Error> {
        if self.tables_version != crate::tables::CBOR_TABLES_VERSION {
            return Err(Error::of(
                ErrorKind::UnsupportedVersion,
                format!(
                    "resolver artifact tables version {} unsupported (this build carries {})",
                    self.tables_version,
                    crate::tables::CBOR_TABLES_VERSION
                ),
            ));
        }
        if self.scheme_version != crate::ID_SCHEME_VERSION {
            return Err(Error::of(
                ErrorKind::UnsupportedVersion,
                format!(
                    "resolver artifact id-scheme version {} unsupported (this build carries {})",
                    self.scheme_version,
                    crate::ID_SCHEME_VERSION
                ),
            ));
        }
        Ok(())
    }

    /// The last effective-name segment for a library id — the exact
    /// signature id-elided decode wants. Pass as
    /// `&|s| resolver.external_name(s)`.
    #[must_use]
    pub fn external_name(&self, id: &str) -> Option<String> {
        self.forward.get(id).and_then(|s| s.last()).cloned()
    }

    /// Full qualified-name segments for a library id.
    pub fn segments(&self, id: &str) -> Option<&[String]> {
        self.forward.get(id).map(Vec::as_slice)
    }

    /// Element id for a qualified name (`::`-joined). Collisions and
    /// membership/alias names resolve to `None` by policy.
    pub fn id_of(&self, qname: &str) -> Option<&str> {
        self.inverse.get(qname).map(String::as_str)
    }

    /// Whether a qualified name was excluded from the inverse because
    /// distinct elements claim it.
    #[must_use]
    pub fn is_collision(&self, qname: &str) -> bool {
        self.collisions.contains(qname)
    }

    #[must_use]
    pub fn library_state_digest(&self) -> &str {
        &self.library_state_digest
    }

    #[must_use]
    pub fn toolkit(&self) -> &str {
        &self.toolkit
    }

    #[must_use]
    pub fn units(&self) -> usize {
        self.units
    }

    #[must_use]
    pub fn forward_len(&self) -> usize {
        self.forward.len()
    }

    #[must_use]
    pub fn inverse_len(&self) -> usize {
        self.inverse.len()
    }
}
