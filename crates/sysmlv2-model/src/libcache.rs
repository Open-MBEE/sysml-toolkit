//! Precompiled standard-library resolution cache.
//!
//! Building a model resolves every pending reference by scope search; over
//! the ~1.6 MB standard library that is ~75% of the build time and repeats
//! identically on every CLI invocation. Library units are always lowered
//! *first* (`Builder::build_model`) and completely, so their pending
//! references occupy a stable prefix of the pending queue in deterministic
//! order — a cache can therefore store just the per-reference *outcomes*
//! (the target element's deterministic UUID, or "unresolved") keyed by the
//! library's content hash, and a warm build replays them positionally
//! instead of searching.
//!
//! Soundness:
//! - The cache file is keyed by the crate version plus every library
//!   file's name and bytes — any library change misses.
//! - The header carries the toolkit build identity ([`TOOLKIT_BUILD`]):
//!   crate version plus a build-time fingerprint of the semantics-bearing
//!   crate sources. A cache recorded by any other build — including a
//!   working-tree state at the same crate version — fails to load and is
//!   re-recorded in place, so a resolution, id-assignment, or evaluation
//!   change can never replay pre-change outcomes.
//! - Replay validates each target UUID against the freshly lowered library
//!   elements; an unknown UUID falls back to a full resolve for that entry.
//! - A user unit whose top-level names collide with a library's top-level
//!   names could (pathologically) capture a library reference; the builder
//!   disables replay entirely in that case (see `build_model`).
//! - The equivalence gate: cold and warm builds must emit byte-identical
//!   compact JSON (`tests/libcache.rs`).

use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use uuid::Uuid;

// v4: `lib_qnames` also carries redefinition-named library members
// (effective names), consumed by the full form's memberName derivation.
// v5: effective-named library members (and their memberships, plus alias
// memberships and document root namespaces) get normative KerML 9.1
// qualified-name IDs — cached `lib_ids` from earlier versions are stale.
// From v5 on, [`TOOLKIT_BUILD`] invalidates automatically across source
// changes; bump the MAGIC digit only for serialized-layout changes.
// v6: outcomes may carry the root names their resolution missed, so a
// replay can re-resolve exactly the entries a model's root additions reach.
const MAGIC: &[u8; 8] = b"SYSML6LC";

/// Toolkit build identity stamped into every serialized cache: the crate
/// version plus a fingerprint of the semantics-bearing crate sources
/// (computed by `build.rs`). [`LibraryCache::from_bytes`] rejects a cache
/// stamped by any other build, so recorded outcomes never outlive the
/// code that recorded them — the crate version alone cannot distinguish
/// two working-tree states, and the pending-sequence fingerprint cannot
/// see a search-rule change that leaves the queue identical.
pub const TOOLKIT_BUILD: &str = concat!(
    env!("CARGO_PKG_VERSION"),
    "+",
    env!("SYSMLV2_SEMANTICS_FINGERPRINT")
);

/// The serialized header carries the build identity's length in one byte.
const _: () = assert!(
    TOOLKIT_BUILD.len() <= 255,
    "the cache header stores the build identity's length in one byte"
);

/// Recorded resolution outcomes for a library's pending references, in
/// queue order. `None` = the reference did not resolve (also cached — the
/// unresolved long tail is re-reported identically without re-searching).
#[derive(Clone)]
pub struct LibraryCache {
    pub(crate) outcomes: Vec<Option<Uuid>>,
    /// Per outcome, the root-namespace names its resolution looked up and
    /// missed. A model that introduces one of them resolves that entry
    /// afresh instead of replaying it.
    pub(crate) outcome_misses: Vec<Vec<String>>,
    /// Element ids of the library prefix, in creation order — replayed at
    /// element creation so the warm build skips ownership-path
    /// construction, per-element UUIDv5 hashing, and the whole normative
    /// re-assignment pass (the "sealed snapshot").
    pub(crate) lib_ids: Vec<Uuid>,
    /// The library name table (`Builder::lib_qnames`) the re-assignment
    /// pass would have produced — normative id → qualified-name segments.
    pub(crate) lib_qnames: Vec<(Uuid, Vec<String>)>,
    /// Library membership/alias ids → member segments
    /// (`Builder::lib_mem_qnames`) — kept separate so name→id inversions
    /// see elements only.
    pub(crate) lib_mem_qnames: Vec<(Uuid, Vec<String>)>,
    /// Hash of the pending-reference *sequence* the outcomes were recorded
    /// against ((element, key, name) per library ref, in order). Replay is
    /// positional, so any lowering change — even at the same crate version,
    /// e.g. during development — must invalidate; the builder recomputes
    /// this from the live queue and rejects the cache on mismatch.
    pub(crate) fingerprint: u64,
}

/// Largest cache file either loader reads. A file beyond it is a foreign
/// or damaged one, not an allocation request: the loaders check the size
/// before reading and bound the read itself, so a miss costs a `stat`.
pub(crate) const MAX_BYTES: u64 = 256 * 1024 * 1024;

/// Write `bytes` to `path` so that readers see either the previous file
/// or the whole new one, never a partial write. The temporary file
/// carries a fresh identifier: two processes recording the same cache
/// would otherwise interleave their writes into one sibling file, and a
/// crash would strand a partial file exactly where the next writer looks.
pub(crate) fn write_atomically(path: &Path, bytes: &[u8]) -> io::Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir)?;
    }
    let temporary = path.with_extension(format!("{}.tmp", Uuid::new_v4()));
    let result = (|| {
        std::fs::File::create(&temporary)?.write_all(bytes)?;
        std::fs::rename(&temporary, path)
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

/// Read a cache file whole, refusing one past [`MAX_BYTES`].
pub(crate) fn read_capped(path: &Path) -> Option<Vec<u8>> {
    let file = std::fs::File::open(path).ok()?;
    if file.metadata().ok()?.len() > MAX_BYTES {
        return None;
    }
    let mut buf = Vec::new();
    file.take(MAX_BYTES + 1).read_to_end(&mut buf).ok()?;
    (buf.len() as u64 <= MAX_BYTES).then_some(buf)
}

impl LibraryCache {
    /// Serialize to `path`, atomically.
    pub fn save(&self, path: &Path) -> io::Result<()> {
        write_atomically(path, &self.to_bytes())
    }

    /// The serialized form `save` writes — for hosts that carry the
    /// sealed snapshot without a filesystem (WASM: fetch the bytes,
    /// [`Self::from_bytes`] them). Versioned, fingerprinted, and
    /// checksummed exactly like the on-disk file.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf: Vec<u8> =
            Vec::with_capacity(16 + TOOLKIT_BUILD.len() + self.outcomes.len() * 17);
        buf.extend_from_slice(MAGIC);
        buf.push(TOOLKIT_BUILD.len() as u8);
        buf.extend_from_slice(TOOLKIT_BUILD.as_bytes());
        buf.extend_from_slice(&self.fingerprint.to_le_bytes());
        buf.extend_from_slice(&(self.outcomes.len() as u64).to_le_bytes());
        for (i, o) in self.outcomes.iter().enumerate() {
            let misses = self.outcome_misses.get(i).map_or(&[][..], Vec::as_slice);
            let tag = match (o, misses.is_empty()) {
                (None, true) => 0,
                (Some(_), true) => 1,
                (None, false) => 2,
                (Some(_), false) => 3,
            };
            buf.push(tag);
            if let Some(id) = o {
                buf.extend_from_slice(id.as_bytes());
            }
            if !misses.is_empty() {
                buf.extend_from_slice(&(misses.len() as u32).to_le_bytes());
                for name in misses {
                    buf.extend_from_slice(&(name.len() as u32).to_le_bytes());
                    buf.extend_from_slice(name.as_bytes());
                }
            }
        }
        buf.extend_from_slice(&(self.lib_ids.len() as u64).to_le_bytes());
        for id in &self.lib_ids {
            buf.extend_from_slice(id.as_bytes());
        }
        for table in [&self.lib_qnames, &self.lib_mem_qnames] {
            buf.extend_from_slice(&(table.len() as u64).to_le_bytes());
            for (id, segs) in table {
                buf.extend_from_slice(id.as_bytes());
                buf.extend_from_slice(&(segs.len() as u32).to_le_bytes());
                for seg in segs {
                    buf.extend_from_slice(&(seg.len() as u32).to_le_bytes());
                    buf.extend_from_slice(seg.as_bytes());
                }
            }
        }
        // Whole-file integrity: replayed ids/outcomes are trusted content,
        // so a trailing FNV-1a of everything above rejects corruption at
        // load (staleness is separately covered by the key + fingerprint).
        let mut check = Fnv::new();
        check.update(&buf);
        buf.extend_from_slice(&check.finish().to_le_bytes());
        buf
    }

    /// Deserialize from `path`; `None` on any mismatch (missing file,
    /// other toolkit build, truncation, a file past the cache size limit)
    /// — the caller then falls back to a cold build and re-records.
    pub fn load(path: &Path) -> Option<LibraryCache> {
        Self::from_bytes(&read_capped(path)?)
    }

    /// Deserialize [`Self::to_bytes`] output; `None` on any mismatch
    /// (other toolkit build, truncation, corruption) — the caller then
    /// falls back to a cold build.
    pub fn from_bytes(buf: &[u8]) -> Option<LibraryCache> {
        if buf.len() < 8 {
            return None;
        }
        let (body, tail) = buf.split_at(buf.len() - 8);
        let mut check = Fnv::new();
        check.update(body);
        if tail != check.finish().to_le_bytes() {
            return None;
        }
        let buf = body;
        let rest = buf.strip_prefix(MAGIC.as_slice())?;
        let (vlen, rest) = rest.split_first()?;
        let vlen = *vlen as usize;
        if rest.len() < vlen || &rest[..vlen] != TOOLKIT_BUILD.as_bytes() {
            return None;
        }
        let rest = &rest[vlen..];
        if rest.len() < 16 {
            return None;
        }
        let fingerprint = u64::from_le_bytes(rest[..8].try_into().ok()?);
        let count = u64::from_le_bytes(rest[8..16].try_into().ok()?) as usize;
        let mut rest = &rest[16..];
        // Every entry is at least one byte — a count beyond the remaining
        // bytes is a truncated or foreign file, not an allocation request.
        if count > rest.len() {
            return None;
        }
        let mut outcomes = Vec::with_capacity(count);
        let mut outcome_misses = Vec::with_capacity(count);
        for _ in 0..count {
            let (tag, mut r) = rest.split_first()?;
            if !matches!(tag, 0..=3) {
                return None;
            }
            if tag & 1 == 1 {
                if r.len() < 16 {
                    return None;
                }
                outcomes.push(Some(Uuid::from_bytes(r[..16].try_into().ok()?)));
                r = &r[16..];
            } else {
                outcomes.push(None);
            }
            let mut misses = Vec::new();
            if tag & 2 == 2 {
                if r.len() < 4 {
                    return None;
                }
                let n = u32::from_le_bytes(r[..4].try_into().ok()?) as usize;
                r = &r[4..];
                // Each name costs at least its length prefix.
                if n > r.len() / 4 {
                    return None;
                }
                for _ in 0..n {
                    if r.len() < 4 {
                        return None;
                    }
                    let len = u32::from_le_bytes(r[..4].try_into().ok()?) as usize;
                    r = &r[4..];
                    if r.len() < len {
                        return None;
                    }
                    misses.push(String::from_utf8(r[..len].to_vec()).ok()?);
                    r = &r[len..];
                }
            }
            outcome_misses.push(misses);
            rest = r;
        }
        fn take<'a>(rest: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
            if rest.len() < n {
                return None;
            }
            let (head, tail) = rest.split_at(n);
            *rest = tail;
            Some(head)
        }
        let n_ids = u64::from_le_bytes(take(&mut rest, 8)?.try_into().ok()?) as usize;
        if n_ids > rest.len() / 16 {
            return None;
        }
        let mut lib_ids = Vec::with_capacity(n_ids);
        for _ in 0..n_ids {
            lib_ids.push(Uuid::from_bytes(take(&mut rest, 16)?.try_into().ok()?));
        }
        fn take_qnames(rest: &mut &[u8]) -> Option<Vec<(Uuid, Vec<String>)>> {
            fn take<'a>(rest: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
                if rest.len() < n {
                    return None;
                }
                let (head, tail) = rest.split_at(n);
                *rest = tail;
                Some(head)
            }
            let n_qn = u64::from_le_bytes(take(rest, 8)?.try_into().ok()?) as usize;
            if n_qn > rest.len() / 20 {
                return None;
            }
            let mut qnames = Vec::with_capacity(n_qn);
            for _ in 0..n_qn {
                let id = Uuid::from_bytes(take(rest, 16)?.try_into().ok()?);
                let n_segs = u32::from_le_bytes(take(rest, 4)?.try_into().ok()?) as usize;
                if n_segs > rest.len() / 4 {
                    return None;
                }
                let mut segs = Vec::with_capacity(n_segs);
                for _ in 0..n_segs {
                    let len = u32::from_le_bytes(take(rest, 4)?.try_into().ok()?) as usize;
                    segs.push(String::from_utf8(take(rest, len)?.to_vec()).ok()?);
                }
                qnames.push((id, segs));
            }
            Some(qnames)
        }
        let lib_qnames = take_qnames(&mut rest)?;
        let lib_mem_qnames = take_qnames(&mut rest)?;
        if !rest.is_empty() {
            return None;
        }
        Some(LibraryCache {
            outcomes,
            outcome_misses,
            fingerprint,
            lib_ids,
            lib_qnames,
            lib_mem_qnames,
        })
    }
}

/// Content hash of a library directory: FNV-1a 64 over the crate version
/// and every model file's name and bytes, in the same sorted order
/// [`crate::model::Model::load_library_dir`] reads them. Deliberately the
/// *released* version, not [`TOOLKIT_BUILD`]: the cache path stays stable
/// across working-tree builds, so a build-mismatched file is overwritten
/// in place instead of accumulating one file per source change.
pub fn hash_library_dir(dir: &Path) -> io::Result<u64> {
    let mut files = Vec::new();
    crate::model::collect_model_files(dir, &mut files)?;
    files.sort();
    let mut h = Fnv::new();
    h.update(env!("CARGO_PKG_VERSION").as_bytes());
    for path in files {
        h.update(
            path.file_name()
                .map(|n| n.to_string_lossy())
                .unwrap_or_default()
                .as_bytes(),
        );
        h.update(&std::fs::read(&path)?);
    }
    Ok(h.finish())
}

/// Default cache file path for a library keyed by `key`:
/// `$SYSMLV2_CACHE_DIR`, else `$XDG_CACHE_HOME/sysmlv2`, else
/// `$HOME/.cache/sysmlv2`. `None` when no base directory can be determined.
pub fn default_cache_path(key: u64) -> Option<PathBuf> {
    let base = std::env::var_os("SYSMLV2_CACHE_DIR")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("XDG_CACHE_HOME").map(|c| PathBuf::from(c).join("sysmlv2")))
        .or_else(|| {
            std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache").join("sysmlv2"))
        })?;
    Some(base.join(format!("stdlib-{key:016x}.libcache")))
}

/// FNV-1a, 64-bit — tiny, dependency-free, deterministic across platforms.
pub(crate) struct Fnv(u64);

impl Fnv {
    pub(crate) fn new() -> Fnv {
        Fnv(0xcbf29ce484222325)
    }
    pub(crate) fn update(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
    pub(crate) fn finish(&self) -> u64 {
        self.0
    }
}
