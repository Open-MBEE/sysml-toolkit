//! Standard-library resolution cache: recording, replay, and the
//! cold/warm equivalence gate.

use sysmlv2_parser::json::{library_to_compact_json, model_to_compact_json};
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

/// A recorded miss that a user root import completes must resolve afresh
/// under replay: outcomes carry the root names they missed, and replay
/// skips exactly the entries a model's root additions reach.
#[test]
fn replay_re_resolves_outcomes_a_root_import_completes() {
    let library = "package Other { part def X; } package L { part def A :> X; }";
    let mut recorder = Model::new();
    recorder.add_library_source("Lib.sysml", library);
    recorder.record_library_cache();
    let _ = model_to_compact_json(&recorder);
    let cache = recorder.take_recorded_library_cache().unwrap();
    let cache = LibraryCache::from_bytes(&cache.to_bytes()).expect("miss names round-trip");
    for user in [
        "private import Other::*; package U { part a : L::A; }",
        "package U { part a : L::A; }",
    ] {
        let graphs = |cache: Option<LibraryCache>| {
            let mut model = Model::new();
            model.add_library_source("Lib.sysml", library);
            model.add_source("t.sysml", user);
            if let Some(cache) = cache {
                model.set_library_cache(cache);
            }
            (
                serde_json::to_string(&model_to_compact_json(&model)).unwrap(),
                serde_json::to_string(&library_to_compact_json(&model)).unwrap(),
            )
        };
        let cold = graphs(None);
        let warm = graphs(Some(cache.clone()));
        assert_eq!(cold, warm, "{user}");
        let completed = user.starts_with("private import");
        assert_eq!(
            !warm.1.contains("\"@ref\":\"X\""),
            completed,
            "{user}: the library reference resolves only through the import"
        );
    }
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

    // Flip the fingerprint on disk (offset: 8 magic + 1 + build len + 1
    // graph format + 1 fixed point) and re-seal the trailing whole-file
    // checksum, simulating a cache recorded against different lowering
    // rather than plain corruption.
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-fp-{}", std::process::id()));
    let path = dir.join("stdlib.libcache");
    cache.save(&path).unwrap();
    let mut bytes = std::fs::read(&path).unwrap();
    let fp_off = 11 + bytes[8] as usize;
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

/// Both cache loaders refuse a file too large to be one of theirs before
/// reading it, so a wrong or hostile file at the cache path costs a file
/// size lookup rather than its length in memory. The snapshot loader is
/// the sibling of the resolution-recording loader here: they share the
/// limit and the capped read.
#[test]
fn oversized_cache_files_are_refused_without_reading_them() {
    use sysmlv2_parser::prepared::PreparedLibrary;
    let dir = std::env::temp_dir().join(format!("sysmlv2-libcache-huge-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("huge.libcache");
    // Sparse: the bytes are never allocated on disk either.
    let file = std::fs::File::create(&path).unwrap();
    file.set_len(256 * 1024 * 1024 + 1).unwrap();
    drop(file);
    let started = std::time::Instant::now();
    assert!(LibraryCache::load(&path).is_none());
    assert!(PreparedLibrary::load(&path, 0).is_none());
    assert!(
        started.elapsed() < std::time::Duration::from_secs(5),
        "the file must be refused by size, not read"
    );
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
        buf.extend_from_slice(b"SYSML8LC");
        buf.push(build.len() as u8);
        buf.extend_from_slice(build);
        buf.push(2); // legacy authored graph format
        buf.push(1); // the library's own fixed point
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

#[test]
fn anonymous_redefinition_fanout_survives_library_replay() {
    if !sysmlv2_testkit::library_dir().exists() {
        return;
    }
    let source = "package Demo {
        part def Item;
        part def Container { ref part items : Item[*]; }
        part a : Item;
        part c : Container {
            ref :>> items = a; ref :>> items = a; ref :>> items = a;
        }
    }";
    let mut model = lib_model(source);
    model.record_library_cache();
    let cold = model_to_compact_json(&model);
    let cache = model.take_recorded_library_cache().unwrap();
    let rows = cold.as_array().unwrap();
    let base = &rows.iter().find(|e| e["declaredName"] == "items").unwrap()["@id"];
    let edges: Vec<_> = rows
        .iter()
        .filter(|e| e["@type"] == "Redefinition")
        .collect();
    assert_eq!(edges.len(), 3);
    assert!(edges.iter().all(|e| &e["redefinedFeature"]["@id"] == base));
    let mut model = lib_model(source);
    model.set_library_cache(cache);
    assert_eq!(model_to_compact_json(&model), cold);
    assert!(sysmlv2_parser::check::validate_model(&model).is_empty());
}

/// xorshift64* — tiny, deterministic, no dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn pick<'a>(&mut self, choices: &[&'a str]) -> &'a str {
        choices[(self.next() % choices.len() as u64) as usize]
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// The keywords a generated source spells its definitions and features
/// with, and the extension of its units.
struct Dialect {
    definition: &'static str,
    feature: &'static str,
    extension: &'static str,
}

const SYSML: Dialect = Dialect {
    definition: "part def",
    feature: "part",
    extension: "sysml",
};

const KERML: Dialect = Dialect {
    definition: "class",
    feature: "feature",
    extension: "kerml",
};

/// Members of a generated definition: typings, subsettings and
/// redefinitions of names its bases may or may not supply, nested
/// definitions, aliases and nested bodies.
fn generated_members(rng: &mut Rng, d: &Dialect, depth: usize) -> String {
    let (def, feature) = (d.definition, d.feature);
    let mut out = String::new();
    for k in 0..rng.below(5) {
        out += &match rng.below(9) {
            0 | 1 => {
                let ty = rng.pick(&[
                    "Inner", "Inner2", "X", "K", "T", "Y", "AX", "Q::T", "Other::X", "A",
                ]);
                format!("{feature} f{k} : {ty}; ")
            }
            2 => format!("{feature} :>> {}; ", rng.pick(&["y", "z", "w"])),
            3 => format!("{feature} g{k} :> {}; ", rng.pick(&["y", "z", "w"])),
            4 => match rng.pick(&["Inner", "Inner2", "T", "y"]) {
                "y" => format!("{feature} y; "),
                name => format!("{def} {name}; "),
            },
            5 if depth < 2 => {
                let ty = rng.pick(&["Inner", "X", "K", "T"]);
                format!(
                    "{feature} h{k} : {ty} {{ {}}} ",
                    generated_members(rng, d, depth + 1)
                )
            }
            6 => format!("{feature} {}; ", rng.pick(&["y", "z"])),
            7 => format!("alias Al{k} for {}; ", rng.pick(&["X", "K", "Inner"])),
            _ => {
                let redefined = rng.pick(&["y", "z", "w", "v"]);
                let ty = rng.pick(&["Inner", "Inner2", "T"]);
                format!("{feature} :>> {redefined} : {ty}; ")
            }
        };
    }
    out
}

/// A library whose references miss root names a model may supply: `X`
/// and `Y` live in a package the library never imports, `Q` usually
/// nowhere.
fn generated_library(rng: &mut Rng, d: &Dialect) -> String {
    let (def, feature) = (d.definition, d.feature);
    let mut other = String::new();
    for name in ["X", "Y"] {
        let base = if rng.below(100) < 40 {
            format!(" :> {}", rng.pick(&["L::K", "L::A", "Y"]))
        } else {
            String::new()
        };
        if name == "Y" && base.ends_with('Y') {
            continue;
        }
        other += &format!(
            "{def} {name}{base} {{ {feature} y; {feature} z; {def} Inner; \
             {def} Inner2 {{ {feature} w; }} {}}} ",
            generated_members(rng, d, 1)
        );
    }
    let mut l = String::new();
    for _ in 0..rng.below(3) {
        l += rng.pick(&[
            "import Q::*; ",
            "private import Q::*; ",
            "import X::*; ",
            "private import Other::X; ",
            "import Q::**; ",
            "import Q::T; ",
            "alias AX for X; ",
        ]);
    }
    let names = ["K", "A", "B", "C", "D"];
    for (i, name) in names.iter().take(2 + rng.below(4)).enumerate() {
        let mut bases: Vec<&str> = Vec::new();
        for _ in 0..rng.below(3) {
            let base = rng.pick(&["X", "Y", "K", "A", "B", "AX", "Q::T", "Other::Y", "T"]);
            if !names[i..].contains(&base) && !bases.contains(&base) {
                bases.push(base);
            }
        }
        let spec = if bases.is_empty() {
            String::new()
        } else {
            format!(" :> {}", bases.join(", "))
        };
        l += &format!("{def} {name}{spec} {{ {}}} ", generated_members(rng, d, 0));
    }
    let q = if rng.below(100) < 20 {
        format!("package Q {{ {def} T {{ {feature} y; }} }} ")
    } else {
        String::new()
    };
    format!("package Other {{ {other}}} package L {{ {l}}} {q}")
}

/// A model that supplies some of the names the library missed, through
/// root declarations and root imports, and refers into the library.
fn generated_model(rng: &mut Rng, d: &Dialect) -> String {
    let (def, feature) = (d.definition, d.feature);
    let mut out = String::new();
    for _ in 0..=rng.below(3) {
        out += &match rng.below(8) {
            0 => "private import Other::*; ".to_string(),
            1 => "public import Other::X; ".to_string(),
            2 => format!("{def} X {{ {feature} y; {feature} z; {def} Inner; {def} Inner2; }} "),
            3 => format!("package Q {{ {def} T {{ {feature} y; {feature} w; }} {def} Inner; }} "),
            4 => format!("{def} Inner; "),
            5 => format!("{def} T {{ {feature} z; }} "),
            6 => format!("package X {{ {def} Inner; {def} Inner2 {{ {feature} y; }} }} "),
            _ => format!("{feature} y; "),
        };
    }
    out + &format!(
        "package P {{ {feature} a : L::A; {feature} k : L::K; {feature} m :> L::K::y; }}"
    )
}

/// Differential gate for library resolution recordings and prepared
/// libraries: over generated libraries and models that supply names the
/// library missed, a build replaying a recording of the library alone,
/// one on the library prepared alone, and one on the library prepared
/// while recording (whose joint builds replay that recording) must equal
/// a cold build.
/// Whatever an outcome reads — lookup caches another reference filled,
/// other references' recorded outcomes, the recorded lookup graph — must
/// carry the root misses behind it, or the replay keeps a stale outcome;
/// and whether resolution runs its later passes must not depend on
/// whether the library resolves alone. Each seed generates one pair per
/// dialect. Deeper runs:
/// `REPLAY_FUZZ_ITERS=100000 cargo test --release --test libcache`.
#[test]
fn replayed_generated_libraries_match_cold_builds() {
    let iters: u64 = std::env::var("REPLAY_FUZZ_ITERS")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(500);
    let mut checked = 0;
    for seed in 1..=iters {
        for (d, stream) in [(&SYSML, 0), (&KERML, 0x5EED)] {
            let mut rng = Rng((seed ^ stream).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
            let library = generated_library(&mut rng, d);
            let user = generated_model(&mut rng, d);
            let (library_unit, user_unit) = (
                format!("lib.{}", d.extension),
                format!("user.{}", d.extension),
            );
            let mut cold = Model::new();
            let parsed = cold
                .add_library_source(&library_unit, &library)
                .diagnostics
                .is_empty()
                && cold.add_source(&user_unit, &user).diagnostics.is_empty();
            if !parsed {
                continue;
            }
            let mut recorder = Model::new();
            recorder.add_library_source(&library_unit, &library);
            recorder.record_library_cache();
            let _ = library_to_compact_json(&recorder);
            let recording = recorder.take_recorded_library_cache().unwrap();
            let mut replay = Model::new();
            replay.add_library_source(&library_unit, &library);
            replay.set_library_cache(LibraryCache::from_bytes(&recording.to_bytes()).unwrap());
            replay.add_source(&user_unit, &user);
            let mut alone = Model::new();
            alone.add_library_source(&library_unit, &library);
            let mut prepared = Model::new();
            alone
                .prepare_library()
                .unwrap()
                .install(&mut prepared)
                .unwrap();
            prepared.add_source(&user_unit, &user);
            let mut recording_alone = Model::new();
            recording_alone.add_library_source(&library_unit, &library);
            recording_alone.record_library_cache();
            let mut replaying = Model::new();
            recording_alone
                .prepare_library()
                .unwrap()
                .install(&mut replaying)
                .unwrap();
            replaying.add_source(&user_unit, &user);
            for (build, model) in [
                ("replayed", &replay),
                ("prepared", &prepared),
                ("prepared-and-replaying", &replaying),
            ] {
                for (graph, of) in [
                    (
                        "user",
                        model_to_compact_json as fn(&Model) -> serde_json::Value,
                    ),
                    ("library", library_to_compact_json),
                ] {
                    assert!(
                        of(model) == of(&cold),
                        "{} seed {seed}: the {build} {graph} graph diverged from a cold build\n\
                         library: {library}\nmodel: {user}",
                        d.extension
                    );
                }
            }
            checked += 1;
        }
    }
    assert!(checked > iters, "most generated sources parse");
}
