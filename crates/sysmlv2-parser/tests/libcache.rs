//! Standard-library resolution cache: recording, replay, and the
//! cold/warm equivalence gate.

use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::libcache::{LibraryCache, TOOLKIT_BUILD, hash_library_dir};
use sysmlv2_parser::model::Model;

const USER_SRC: &str = "package Demo {
    private import ScalarValues::*;
    part def Vehicle { attribute mass : Real = 1500.0; }
    part car : Vehicle { attribute :>> mass = 1200.0; }
}";

fn lib_model(user: &str) -> Model {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source("t.sysml", user);
    model
}

/// The gate: a warm (replayed) build must emit byte-identical compact JSON
/// to a cold build — over the full standard library.
#[test]
fn cold_and_warm_builds_are_identical() {
    if !sysmlv2_testkit::library_dir().exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    // Cold build, recording.
    let mut model = lib_model(USER_SRC);
    model.record_library_cache();
    let cold = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    let cache = model
        .take_recorded_library_cache()
        .expect("recording armed before the build");
    assert!(!cache_is_empty(&cache), "library refs must be recorded");

    // Serialization round-trip through a real file.
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-test-{}", std::process::id()));
    let path = dir.join("stdlib.libcache");
    cache.save(&path).unwrap();
    let cache = LibraryCache::load(&path).expect("cache must load back");
    std::fs::remove_dir_all(&dir).ok();

    // Warm build, replaying.
    let mut model = lib_model(USER_SRC);
    model.set_library_cache(cache);
    let warm = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    assert_eq!(cold, warm, "replayed build diverged from cold build");
}

/// A user reference that disambiguates through a *library-internal*
/// redefinition must resolve identically cold and warm: replay records
/// spec outcomes like the slow path, so the inherited-merge shadowing
/// (which reads only recorded outcomes) sees library redefinitions in
/// both cache states. The shape distills the geometry-example diamond —
/// `:>> coordinateFrame` is inherited both through the typing and
/// through the subsetted collection member, and the collection member's
/// body redefines it.
#[test]
fn library_redefinition_shadowing_survives_replay() {
    if !sysmlv2_testkit::library_dir().exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let user = "package Demo {
        private import SpatialItems::*;
        part def Chassis :> SpatialItem;
        part vehicle : SpatialItem {
            part chassis : Chassis[1] :> componentParts {
                attribute :>> coordinateFrame;
            }
        }
    }";
    let mut model = lib_model(user);
    model.record_library_cache();
    let cold = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    let cache = model.take_recorded_library_cache().unwrap();
    assert!(
        !cold.contains("\"@ref\":\"coordinateFrame\""),
        "the redefinition target must resolve on the cold build"
    );

    let mut model = lib_model(user);
    model.set_library_cache(cache);
    let warm = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    assert_eq!(cold, warm, "replayed build diverged from cold build");
}

fn cache_is_empty(cache: &LibraryCache) -> bool {
    // Proxy via the serialized form (`outcomes` is crate-private): an empty
    // cache serializes to just the header.
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-len-{}", std::process::id()));
    let path = dir.join("probe.libcache");
    cache.save(&path).unwrap();
    let len = std::fs::metadata(&path).unwrap().len();
    std::fs::remove_dir_all(&dir).ok();
    len < 64
}

/// A user unit shadowing a library top-level name disables replay — output
/// must still match a cold build exactly.
#[test]
fn shadowing_user_package_disables_replay_soundly() {
    if !sysmlv2_testkit::library_dir().exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let shadowing = "package ScalarValues { part def Real; } \
                     package Demo { part def P; part p : P; }";
    let mut model = lib_model(USER_SRC);
    model.record_library_cache();
    let _ = model_to_compact_json(&model);
    let cache = model.take_recorded_library_cache().unwrap();

    let mut cold = lib_model(shadowing);
    let cold_json = serde_json::to_string(&model_to_compact_json(&cold)).unwrap();
    let _ = &mut cold;

    let mut warm = lib_model(shadowing);
    warm.set_library_cache(cache);
    let warm_json = serde_json::to_string(&model_to_compact_json(&warm)).unwrap();
    assert_eq!(cold_json, warm_json);
}

/// A cache whose fingerprint does not match the live pending sequence
/// (e.g. recorded before a lowering change at the same crate version) is
/// silently ignored — the warm build falls back to full resolution and
/// must still match the cold build exactly.
#[test]
fn stale_fingerprint_disables_replay_soundly() {
    if !sysmlv2_testkit::library_dir().exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = lib_model(USER_SRC);
    model.record_library_cache();
    let cold = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    let cache = model.take_recorded_library_cache().unwrap();

    // Flip the fingerprint on disk (offset: 8 magic + 1 + version len) and
    // re-seal the trailing whole-file checksum, simulating a cache recorded
    // against different lowering rather than plain corruption.
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-fp-{}", std::process::id()));
    let path = dir.join("stdlib.libcache");
    cache.save(&path).unwrap();
    let mut bytes = std::fs::read(&path).unwrap();
    let fp_off = 9 + bytes[8] as usize;
    bytes[fp_off] ^= 0xff;
    let body_len = bytes.len() - 8;
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in &bytes[..body_len] {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    bytes[body_len..].copy_from_slice(&h.to_le_bytes());
    std::fs::write(&path, &bytes).unwrap();
    let tampered = LibraryCache::load(&path).expect("structurally valid");

    // Plain corruption (checksum not re-sealed) must be rejected at load.
    let mut corrupt = std::fs::read(&path).unwrap();
    corrupt[fp_off + 1] ^= 0xff;
    let cpath = dir.join("corrupt.libcache");
    std::fs::write(&cpath, &corrupt).unwrap();
    assert!(
        LibraryCache::load(&cpath).is_none(),
        "corruption must not load"
    );
    std::fs::remove_dir_all(&dir).ok();

    let mut model = lib_model(USER_SRC);
    model.set_library_cache(tampered);
    let warm = serde_json::to_string(&model_to_compact_json(&model)).unwrap();
    assert_eq!(cold, warm, "stale cache must be ignored, not replayed");
}

/// Corrupted or foreign cache files must be rejected, not trusted.
#[test]
fn invalid_cache_files_are_rejected() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-bad-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("bad.libcache");
    std::fs::write(&path, b"SYSML2LC\x05junk").unwrap();
    assert!(LibraryCache::load(&path).is_none());
    std::fs::write(&path, b"not a cache at all").unwrap();
    assert!(LibraryCache::load(&path).is_none());
    // A structurally plausible header whose count field exceeds the file
    // (e.g. a pre-fingerprint cache read by this format) must be rejected
    // without attempting the allocation.
    let version = env!("CARGO_PKG_VERSION").as_bytes();
    let mut huge = Vec::new();
    huge.extend_from_slice(b"SYSML3LC");
    huge.push(version.len() as u8);
    huge.extend_from_slice(version);
    huge.extend_from_slice(&0u64.to_le_bytes());
    huge.extend_from_slice(&u64::MAX.to_le_bytes());
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in &huge {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    huge.extend_from_slice(&h.to_le_bytes());
    std::fs::write(&path, &huge).unwrap();
    assert!(LibraryCache::load(&path).is_none());
    std::fs::remove_dir_all(&dir).ok();
}

/// The header's build identity must be finer than the crate version: two
/// working-tree states share a version, and a semantics change that
/// leaves the pending queue unchanged slips past the sequence
/// fingerprint — only a per-build source fingerprint catches it.
#[test]
fn header_carries_a_source_fingerprint_beyond_the_crate_version() {
    let fp = TOOLKIT_BUILD
        .strip_prefix(env!("CARGO_PKG_VERSION"))
        .expect("build identity starts with the crate version")
        .strip_prefix('+')
        .expect("build identity carries a fingerprint component");
    assert_eq!(fp.len(), 16, "fingerprint is an FNV-1a 64 in hex");
    assert!(fp.chars().all(|c| c.is_ascii_hexdigit()));
}

/// A cache stamped by another toolkit build — same crate version,
/// different source fingerprint, the exact miss behind a stale cached
/// export serving pre-change evaluated values — must be rejected at
/// load, as must one stamped with the bare crate version.
#[test]
fn cache_from_another_toolkit_build_is_rejected() {
    fn sealed_empty_cache(build: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(b"SYSML5LC");
        buf.push(build.len() as u8);
        buf.extend_from_slice(build);
        buf.extend_from_slice(&0u64.to_le_bytes()); // pending fingerprint
        for _ in 0..4 {
            buf.extend_from_slice(&0u64.to_le_bytes()); // empty tables
        }
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in &buf {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        buf.extend_from_slice(&h.to_le_bytes());
        buf
    }

    // Control: an otherwise-valid empty cache from *this* build loads.
    assert!(LibraryCache::from_bytes(&sealed_empty_cache(TOOLKIT_BUILD.as_bytes())).is_some());

    // Same crate version, one fingerprint digit off.
    let mut other = TOOLKIT_BUILD.as_bytes().to_vec();
    *other.last_mut().unwrap() ^= 0x01;
    assert!(
        LibraryCache::from_bytes(&sealed_empty_cache(&other)).is_none(),
        "a different source fingerprint must not load"
    );

    // Bare crate version (the pre-fingerprint header form).
    assert!(
        LibraryCache::from_bytes(&sealed_empty_cache(env!("CARGO_PKG_VERSION").as_bytes()))
            .is_none(),
        "a version-only header must not load"
    );
}

/// The directory hash must be stable across runs and sensitive to content.
#[test]
fn library_hash_is_content_keyed() {
    if !sysmlv2_testkit::library_dir().exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let a = hash_library_dir(&sysmlv2_testkit::library_dir()).unwrap();
    let b = hash_library_dir(&sysmlv2_testkit::library_dir()).unwrap();
    assert_eq!(a, b);

    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-hash-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("a.sysml"), "package A;").unwrap();
    let h1 = hash_library_dir(&dir).unwrap();
    std::fs::write(dir.join("a.sysml"), "package B;").unwrap();
    let h2 = hash_library_dir(&dir).unwrap();
    assert_ne!(h1, h2);
    std::fs::remove_dir_all(&dir).ok();
}
