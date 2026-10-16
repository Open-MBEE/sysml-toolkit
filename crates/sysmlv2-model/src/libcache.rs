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
// v7: include the authored graph format so resolution recordings cannot cross it.
// v8: whether the outcomes are the library's own fixed point.
const MAGIC: &[u8; 8] = b"SYSML9LC";

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
    pub(crate) graph_format: crate::model::GraphFormat,
    /// Whether the outcomes are the library's own fixed point: recorded
    /// from the library alone, by a resolution whose passes agreed. An
    /// oscillating library keeps its first pass's outcomes instead, which a
    /// replay may not treat as final.
    pub(crate) fixed_point: bool,
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
    write_atomically_parts(path, &[bytes])
}

/// [`write_atomically`] of `parts` written one after the other, so that a
/// file made of a small header and a large payload is not joined in memory
/// first.
pub(crate) fn write_atomically_parts(path: &Path, parts: &[&[u8]]) -> io::Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir)?;
    }
    let temporary = path.with_extension(format!("{}.tmp", Uuid::new_v4()));
    let result = (|| {
        let mut file = std::fs::File::create(&temporary)?;
        for part in parts {
            file.write_all(part)?;
        }
        std::fs::rename(&temporary, path)
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

/// A snapshot's bytes as a load holds them: the file mapped in place where
/// the target maps files, else read whole. Read only ever as a byte slice,
/// through the decoder's bounds checks.
pub(crate) enum SnapshotBytes {
    #[cfg(not(target_family = "wasm"))]
    Mapped(memmap2::Mmap),
    Owned(Vec<u8>),
}
impl AsRef<[u8]> for SnapshotBytes {
    fn as_ref(&self) -> &[u8] {
        match self {
            #[cfg(not(target_family = "wasm"))]
            Self::Mapped(map) => map,
            Self::Owned(bytes) => bytes,
        }
    }
}

/// A snapshot file mapped into memory, refusing one past [`MAX_BYTES`];
/// read whole where the target cannot map a file or the map is refused.
///
/// The cache's files and the shipped snapshots are written under a
/// temporary name and renamed into place (`write_atomically_parts`), never
/// rewritten where they lie, so what a map shows does not change under the
/// decoder; a snapshot written again gets a file of its own, and the one
/// mapped stays whole until the map is dropped. A file another process
/// rewrites in place while it is mapped is outside that contract: the
/// decoder reads a changed one as corrupt through the part checksums, and
/// a truncated one faults at the missing pages, which the process does not
/// survive. Where the platform refuses to replace a mapped file (Windows),
/// another process writing the same key while this one holds the map gets
/// the cache's "could not save" warning and prepares from source; nothing
/// in this process writes a file it has mapped, since a save follows a
/// miss.
pub(crate) fn map_capped(path: &Path) -> Option<SnapshotBytes> {
    let file = std::fs::File::open(path).ok()?;
    if file.metadata().ok()?.len() > MAX_BYTES {
        return None;
    }
    #[cfg(not(target_family = "wasm"))]
    {
        // SAFETY: the file is a snapshot this toolkit wrote by rename, or
        // one shipped beside it; nothing in this process writes to it, and
        // a change by another process is outside the cache's contract
        // (above). The map is read as a byte slice only.
        if let Ok(map) = unsafe { memmap2::Mmap::map(&file) } {
            // The whole file is read once, soon, by several threads: let
            // the pages come in ahead of them (a hint the unix targets
            // take; the map reads the same everywhere).
            #[cfg(unix)]
            let _ = map.advise(memmap2::Advice::WillNeed);
            return Some(SnapshotBytes::Mapped(map));
        }
    }
    let mut buf = Vec::new();
    file.take(MAX_BYTES + 1).read_to_end(&mut buf).ok()?;
    (buf.len() as u64 <= MAX_BYTES).then_some(SnapshotBytes::Owned(buf))
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

    /// The graph format the outcomes were recorded for; a build of another
    /// format cannot replay them.
    #[must_use]
    pub fn graph_format(&self) -> crate::model::GraphFormat {
        self.graph_format
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
        buf.push(self.graph_format.version());
        buf.push(u8::from(self.fixed_point));
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
        let (format, rest) = rest[vlen..].split_first()?;
        let graph_format = match format {
            2 => crate::model::GraphFormat::LegacyV2,
            3 => crate::model::GraphFormat::CanonicalV3,
            _ => return None,
        };
        let (fixed_point, rest) = rest.split_first()?;
        let fixed_point = match fixed_point {
            0 => false,
            1 => true,
            _ => return None,
        };
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
            graph_format,
            fixed_point,
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
    let listing = file_stamps(&files)?;
    let keys = DIRECTORY_KEYS.get_or_init(Default::default);
    if let Some(key) = memoized_key(keys, dir, &listing) {
        return Ok(key);
    }
    let key = hash_files(&files)?;
    keys.lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(dir.to_path_buf(), (listing, key));
    Ok(key)
}

/// A model file's path, length and modification time: what a directory's
/// listing is compared by between two hashes of it.
type FileStamp = (PathBuf, u64, Option<std::time::SystemTime>);

/// The content keys of the library directories this process hashed, each
/// with the listing it was hashed over, so that a directory whose files
/// have not changed answers its key again without reading them. A later
/// load of the same directory in a long-lived process (a language server,
/// an SDK opening sessions in turn) reads nothing but the directory's
/// metadata.
type DirectoryKeys = std::sync::Mutex<std::collections::HashMap<PathBuf, (Vec<FileStamp>, u64)>>;
static DIRECTORY_KEYS: std::sync::OnceLock<DirectoryKeys> = std::sync::OnceLock::new();

fn file_stamps(files: &[PathBuf]) -> io::Result<Vec<FileStamp>> {
    files
        .iter()
        .map(|path| {
            let meta = std::fs::metadata(path)?;
            Ok((path.clone(), meta.len(), meta.modified().ok()))
        })
        .collect()
}

/// The key `dir` hashed to while its listing was `listing`, if this process
/// hashed it and no file's length or modification time has changed since.
fn memoized_key(keys: &DirectoryKeys, dir: &Path, listing: &[FileStamp]) -> Option<u64> {
    let keys = keys.lock().unwrap_or_else(|e| e.into_inner());
    let (known, key) = keys.get(dir)?;
    (known.as_slice() == listing).then_some(*key)
}

/// The content hash of `files` (sorted), as [`hash_library_dir`] defines it.
fn hash_files(files: &[PathBuf]) -> io::Result<u64> {
    let mut h = Fnv::new();
    h.update(env!("CARGO_PKG_VERSION").as_bytes());
    for path in files {
        h.update(
            path.file_name()
                .map(|n| n.to_string_lossy())
                .unwrap_or_default()
                .as_bytes(),
        );
        h.update(&std::fs::read(path)?);
    }
    Ok(h.finish())
}

/// Content key of in-memory library units, `(name, text)` in load order:
/// what a prepared snapshot of a source bundle is keyed by, so a bundle
/// whose units changed (or were reordered) misses. Mixes the released
/// version like [`hash_library_dir`].
pub fn hash_units<'a>(units: impl IntoIterator<Item = (&'a str, &'a str)>) -> u64 {
    let mut h = Fnv::new();
    h.update(env!("CARGO_PKG_VERSION").as_bytes());
    for (name, text) in units {
        h.update(name.as_bytes());
        h.update(&[0]);
        h.update(text.as_bytes());
        h.update(&[0]);
    }
    h.finish()
}

/// Where a snapshot shipped with the toolkit may lie, as recording paths
/// (`stdlib-<key>.libcache`; the snapshot is the `.prepared` sibling of
/// each): under `$SYSMLV2_LIB_SNAPSHOT_DIR`, then under the directory named
/// `prepared` beside the executable. Written there by
/// `prepare_library_into`; read in place by a load whose cache has no
/// snapshot. [`shipped_cache_paths_for`] also looks beside the library.
pub fn shipped_cache_paths(key: u64) -> Vec<PathBuf> {
    shipped_cache_paths_for(key, None)
}

/// [`shipped_cache_paths`] for a load of the library directory `library`:
/// the directory named `prepared` beside the library directory is looked
/// in after `$SYSMLV2_LIB_SNAPSHOT_DIR` and before the one beside the
/// executable — a library packaged with a host (a Python extension, a
/// web bundle) ships its snapshot beside itself, where the executable is
/// the host's.
pub fn shipped_cache_paths_for(key: u64, library: Option<&Path>) -> Vec<PathBuf> {
    let name = format!("stdlib-{key:016x}.libcache");
    shipped_dirs(
        std::env::var_os("SYSMLV2_LIB_SNAPSHOT_DIR").map(PathBuf::from),
        library,
        std::env::current_exe().ok(),
    )
    .into_iter()
    .map(|dir| dir.join(&name))
    .collect()
}

/// The directories [`shipped_cache_paths_for`] looks in, in order:
/// `snapshot_dir` (`$SYSMLV2_LIB_SNAPSHOT_DIR`), `prepared` beside the
/// library directory, `prepared` beside the executable.
fn shipped_dirs(
    snapshot_dir: Option<PathBuf>,
    library: Option<&Path>,
    exe: Option<PathBuf>,
) -> Vec<PathBuf> {
    let beside = |path: Option<&Path>| Some(path?.parent()?.join("prepared"));
    snapshot_dir
        .into_iter()
        .chain(beside(library))
        .chain(beside(exe.as_deref()))
        .collect()
}

/// The directory the library cache lives in: `$SYSMLV2_CACHE_DIR`, else
/// `$XDG_CACHE_HOME/sysmlv2`, else `$HOME/.cache/sysmlv2`; on Windows, which
/// sets neither of the last two, `%LOCALAPPDATA%\sysmlv2`, else
/// `%USERPROFILE%\.cache\sysmlv2`. `None` when no base directory can be
/// determined.
pub fn default_cache_dir() -> Option<PathBuf> {
    cache_dir_from(|name| std::env::var_os(name), cfg!(windows))
}

/// [`default_cache_dir`] over the variables `var` answers, on Windows when
/// `windows`.
fn cache_dir_from(
    var: impl Fn(&str) -> Option<std::ffi::OsString>,
    windows: bool,
) -> Option<PathBuf> {
    let under = |name: &str, tail: &[&str]| {
        var(name).map(|base| tail.iter().fold(PathBuf::from(base), |p, s| p.join(s)))
    };
    under("SYSMLV2_CACHE_DIR", &[])
        .or_else(|| under("XDG_CACHE_HOME", &["sysmlv2"]))
        .or_else(|| under("HOME", &[".cache", "sysmlv2"]))
        .or_else(|| {
            windows
                .then(|| under("LOCALAPPDATA", &["sysmlv2"]))
                .flatten()
        })
        .or_else(|| {
            windows
                .then(|| under("USERPROFILE", &[".cache", "sysmlv2"]))
                .flatten()
        })
}

/// The recording path of the library keyed by `key` in the cache
/// directory `dir`, `stdlib-<key>.libcache`; its complete snapshot is the
/// `prepared` sibling.
pub(crate) fn cache_path_in(dir: &Path, key: u64) -> PathBuf {
    dir.join(format!("stdlib-{key:016x}.libcache"))
}

/// Default cache file path for a library keyed by `key`
/// (`stdlib-<key>.libcache` under [`default_cache_dir`]); `None` when no base
/// directory can be determined.
pub fn default_cache_path(key: u64) -> Option<PathBuf> {
    Some(cache_path_in(&default_cache_dir()?, key))
}

/// FNV-1a, 64-bit — tiny, dependency-free, deterministic across platforms.
/// FNV-1a over bytes, folded eight bytes at a time: a snapshot is tens of
/// megabytes, and the byte-at-a-time fold cost as much as decoding a
/// fifth of it. A partial word is kept until the next bytes complete it,
/// so the sum does not depend on how the bytes are fed (the streamed
/// snapshot reader hashes what it takes, piece by piece); the tail is
/// folded byte by byte at the end.
pub(crate) struct Fnv {
    hash: u64,
    pending: [u8; 8],
    pending_len: usize,
}

const FNV_PRIME: u64 = 0x100000001b3;

impl Fnv {
    pub(crate) fn new() -> Fnv {
        Fnv {
            hash: 0xcbf29ce484222325,
            pending: [0; 8],
            pending_len: 0,
        }
    }
    pub(crate) fn update(&mut self, mut bytes: &[u8]) {
        if self.pending_len > 0 {
            let take = bytes.len().min(8 - self.pending_len);
            self.pending[self.pending_len..self.pending_len + take].copy_from_slice(&bytes[..take]);
            self.pending_len += take;
            bytes = &bytes[take..];
            if self.pending_len < 8 {
                return;
            }
            self.fold(u64::from_le_bytes(self.pending));
            self.pending_len = 0;
        }
        let (chunks, rest) = bytes.as_chunks::<8>();
        for chunk in chunks {
            self.fold(u64::from_le_bytes(*chunk));
        }
        self.pending[..rest.len()].copy_from_slice(rest);
        self.pending_len = rest.len();
    }
    #[inline]
    fn fold(&mut self, word: u64) {
        self.hash ^= word;
        self.hash = self.hash.wrapping_mul(FNV_PRIME);
    }
    pub(crate) fn finish(&self) -> u64 {
        let mut hash = self.hash;
        for &b in &self.pending[..self.pending_len] {
            hash ^= b as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shipped-snapshot directories, in the order they are tried: the
    /// given directory, `prepared` beside the library, `prepared` beside
    /// the executable; a missing one is left out.
    #[test]
    fn shipped_snapshots_are_looked_for_beside_the_library_too() {
        let p = PathBuf::from;
        assert_eq!(
            shipped_dirs(
                Some(p("/s")),
                Some(Path::new("/pkg/sysml.library")),
                Some(p("/usr/bin/python3")),
            ),
            vec![p("/s"), p("/pkg/prepared"), p("/usr/bin/prepared")]
        );
        assert_eq!(
            shipped_dirs(None, Some(Path::new("/pkg/sysml.library")), None),
            vec![p("/pkg/prepared")]
        );
        assert_eq!(
            shipped_dirs(None, None, Some(p("/opt/sysmlv2"))),
            vec![p("/opt/prepared")]
        );
        let for_library = shipped_cache_paths_for(0x1234, Some(Path::new("/pkg/sysml.library")));
        assert!(for_library.contains(&p("/pkg/prepared/stdlib-0000000000001234.libcache")));
    }

    /// A directory hashed once answers its key from its listing while no
    /// file's length or modification time changed; a changed file is read
    /// again and keys differently, and the same content keys the same.
    #[test]
    fn the_directory_key_is_answered_from_its_listing_until_a_file_changes() {
        let dir = std::env::temp_dir().join(format!("sysmlv2-dirkey-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("lib.sysml");
        std::fs::write(&file, "standard library package L { part def A; }").unwrap();
        let first = hash_library_dir(&dir).unwrap();
        let mut files = vec![file.clone()];
        files.sort();
        let listing = file_stamps(&files).unwrap();
        let keys = DIRECTORY_KEYS.get_or_init(Default::default);
        assert_eq!(memoized_key(keys, &dir, &listing), Some(first));
        assert_eq!(hash_library_dir(&dir).unwrap(), first);

        std::fs::write(
            &file,
            "standard library package L { part def A; part def B; }",
        )
        .unwrap();
        let changed = file_stamps(&files).unwrap();
        assert_eq!(
            memoized_key(keys, &dir, &changed),
            None,
            "the listing changed"
        );
        let second = hash_library_dir(&dir).unwrap();
        assert_ne!(second, first);
        assert_eq!(memoized_key(keys, &dir, &changed), Some(second));

        std::fs::write(&file, "standard library package L { part def A; }").unwrap();
        assert_eq!(hash_library_dir(&dir).unwrap(), first, "keyed by content");
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// `SYSMLV2_CACHE_DIR` wins, then the two POSIX variables; on Windows,
    /// which sets neither, the platform's own locations follow.
    #[test]
    fn the_cache_directory_falls_back_to_the_platforms_on_windows() {
        let vars = |set: &'static [(&'static str, &'static str)]| {
            move |name: &str| {
                set.iter()
                    .find(|(k, _)| *k == name)
                    .map(|(_, v)| std::ffi::OsString::from(v))
            }
        };
        let p = |s: &str| Some(PathBuf::from(s));
        assert_eq!(
            cache_dir_from(vars(&[("SYSMLV2_CACHE_DIR", "/c"), ("HOME", "/h")]), false),
            p("/c")
        );
        assert_eq!(
            cache_dir_from(vars(&[("XDG_CACHE_HOME", "/x"), ("HOME", "/h")]), false),
            p("/x/sysmlv2")
        );
        assert_eq!(
            cache_dir_from(vars(&[("HOME", "/h")]), false),
            p("/h/.cache/sysmlv2")
        );
        assert_eq!(
            cache_dir_from(
                vars(&[("LOCALAPPDATA", "/l"), ("USERPROFILE", "/u")]),
                false
            ),
            None,
            "the platform locations are Windows's"
        );
        assert_eq!(
            cache_dir_from(vars(&[("LOCALAPPDATA", "/l"), ("USERPROFILE", "/u")]), true),
            p("/l/sysmlv2")
        );
        assert_eq!(
            cache_dir_from(vars(&[("USERPROFILE", "/u")]), true),
            p("/u/.cache/sysmlv2")
        );
        assert_eq!(
            cache_dir_from(vars(&[("HOME", "/h"), ("LOCALAPPDATA", "/l")]), true),
            p("/h/.cache/sysmlv2"),
            "a set HOME keeps its place"
        );
        assert_eq!(cache_dir_from(vars(&[]), true), None);
    }

    /// The checksum does not depend on how the bytes are fed: any
    /// chunking gives the one-shot sum, and an input under eight bytes
    /// hashes as byte-wise FNV-1a does.
    #[test]
    fn the_checksum_is_the_same_however_the_bytes_are_fed() {
        let bytes: Vec<u8> = (0..1000u32).map(|i| (i * 7919 % 251) as u8).collect();
        let one_shot = {
            let mut h = super::Fnv::new();
            h.update(&bytes);
            h.finish()
        };
        for window in [1, 3, 7, 8, 9, 13, 64, 1000] {
            let mut h = super::Fnv::new();
            for chunk in bytes.chunks(window) {
                h.update(chunk);
            }
            assert_eq!(h.finish(), one_shot, "window {window}");
        }
        let byte_wise = |bytes: &[u8]| {
            let mut hash: u64 = 0xcbf29ce484222325;
            for &b in bytes {
                hash ^= b as u64;
                hash = hash.wrapping_mul(0x100000001b3);
            }
            hash
        };
        for len in 0..8 {
            let mut h = super::Fnv::new();
            h.update(&bytes[..len]);
            assert_eq!(h.finish(), byte_wise(&bytes[..len]), "{len} bytes");
        }
        let mut h = super::Fnv::new();
        h.update(&bytes[..5]);
        let mid = h.finish();
        h.update(&bytes[5..]);
        assert_eq!(
            h.finish(),
            one_shot,
            "finishing midway reads the pending tail without consuming it"
        );
        assert_eq!(mid, byte_wise(&bytes[..5]));
    }
}
