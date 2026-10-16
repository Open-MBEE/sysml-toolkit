//! A standard library given as a bundle file — `[{name, text}]`, the
//! shape the wasm package ships — with the prepared snapshot generated
//! from it beside it: the run decodes the snapshot instead of preparing
//! the library, and answers as a directory of the same library does.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::libcache::{self, LibraryCache};
use sysmlv2_model::model::{GraphFormat, Model};

/// A scratch directory, removed when the test ends.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!(
            "sysmlv2-library-bundle-{}-{name}",
            std::process::id()
        ));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        Scratch(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }

    fn write(&self, name: &str, bytes: impl AsRef<[u8]>) -> PathBuf {
        let path = self.path(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, bytes).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).ok();
    }
}

/// A small library over two directories, one of its units KerML, then
/// the ambient libraries, as the generator orders a bundle: the
/// directory's files sorted by path, named by their path within it.
fn library() -> Vec<(String, String)> {
    let mut units = vec![
        (
            "Base.kerml".to_string(),
            "standard library package Base { class Thing; }".to_string(),
        ),
        (
            "Kinds/Parts.sysml".to_string(),
            "standard library package Parts { part def Wheel :> Base::Thing; \
             attribute def Mass; attribute def Frame { attribute orthogonal = true; } }"
                .to_string(),
        ),
    ];
    units.extend(
        sysmlv2_model::ambient::LIBRARIES
            .iter()
            .map(|(name, text)| (name.to_string(), text.to_string())),
    );
    units
}

/// The library's own files in a directory, as `--lib <dir>` reads them.
fn library_dir(scratch: &Scratch) -> PathBuf {
    for (name, text) in library() {
        if !name.starts_with("local-packages/") {
            scratch.write(&format!("library/{name}"), text);
        }
    }
    scratch.path("library")
}

/// The bundle file for `units`.
fn bundle(scratch: &Scratch, name: &str, units: &[(String, String)]) -> PathBuf {
    let json: Vec<serde_json::Value> = units
        .iter()
        .map(|(name, text)| serde_json::json!({ "name": name, "text": text }))
        .collect();
    scratch.write(name, serde_json::to_vec(&json).unwrap())
}

/// The prepared snapshot of `units`, made as the generator makes the one
/// it ships beside its bundle: the library's resolution recorded first,
/// then the library prepared over it, plans made, keyed by the units.
fn snapshot(units: &[(String, String)]) -> Vec<u8> {
    snapshot_as(units, GraphFormat::LegacyV2)
}

/// [`snapshot`] for a model of `format`.
fn snapshot_as(units: &[(String, String)], format: GraphFormat) -> Vec<u8> {
    let with_units = || {
        let mut model = Model::with_graph_format(format);
        for (name, text) in units {
            model.add_library_source(name.clone(), text);
        }
        model
    };
    let mut model = with_units();
    model.record_library_cache();
    drop(ResolvedModel::build(&model));
    let recording = model.take_recorded_library_cache().unwrap().to_bytes();
    let mut model = with_units();
    model.set_library_cache(LibraryCache::from_bytes(&recording).unwrap());
    let library = model.prepare_library().unwrap();
    library.make_plans();
    let key = libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
    library.to_bytes(key).unwrap()
}

const MODEL: &str = "package Garage {\n\
                     \x20   part car : Base::Thing {\n\
                     \x20       part wheel : Parts::Wheel[4];\n\
                     \x20       attribute mass : Parts::Mass;\n\
                     \x20       part spare : Parts::Tyre;\n\
                     \x20   }\n\
                     \x20   #TransformMeta::Generated part def Rack;\n\
                     }\n";

/// A model overriding the library's bound value: the finding names the
/// unit the value is bound in.
const OVERRIDE: &str = "package Rig {\n\
                        \x20   attribute def Square :> Parts::Frame {\n\
                        \x20       attribute :>> orthogonal = false;\n\
                        \x20   }\n\
                        }\n";

/// The offset and length of part `i` of a snapshot: past the magic and
/// build lines and the key, the part table is ten (length, checksum)
/// words, and the parts follow it in order.
fn part(bytes: &[u8], i: usize) -> (usize, usize) {
    let line = |from: usize| from + bytes[from..].iter().position(|&b| b == b'\n').unwrap() + 1;
    let table = line(line(0)) + 8;
    let word = |at: usize| {
        usize::try_from(u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())).unwrap()
    };
    let lengths: Vec<usize> = (0..10).map(|k| word(table + 16 * k)).collect();
    let payload = table + 16 * 10;
    (payload + lengths[..i].iter().sum::<usize>(), lengths[i])
}

/// `sysmlv2 check` of `model` against `lib`, with the cache in `cache`.
fn check(lib: &Path, model: &Path, cache: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .arg("check")
        .args(args)
        .arg("--lib")
        .arg(lib)
        .arg(model)
        .env("SYSMLV2_CACHE_DIR", cache)
        .env_remove("SYSMLV2_LIB_CACHE")
        .env_remove("SYSMLV2_LIB_SNAPSHOT_DIR")
        .env_remove("SYSMLV2_AMBIENT")
        .output()
        .unwrap()
}

/// The files a run left in the cache directory.
fn cached(cache: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(cache)
        .map(|entries| {
            entries
                .flatten()
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .collect()
        })
        .unwrap_or_default();
    names.sort();
    names
}

#[test]
fn a_bundle_with_its_snapshot_beside_it_loads_without_preparing() {
    let scratch = Scratch::new("beside");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    scratch.write("sysml-library.prepared", snapshot(&units));
    let model = scratch.write("garage.sysml", MODEL);
    let cache = scratch.path("cache");
    let out = check(&lib, &model, &cache, &[]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{stderr}");
    // The library resolved: only the one name it lacks is reported.
    assert_eq!(
        stderr.matches("unresolved reference").count(),
        1,
        "{stderr}"
    );
    assert!(stderr.contains("`Parts::Tyre`"), "{stderr}");
    // Nothing was prepared, so nothing was written for the next run.
    assert_eq!(cached(&cache), Vec::<String>::new());
}

#[test]
fn check_against_a_bundle_reports_what_a_directory_of_it_reports() {
    let scratch = Scratch::new("same");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    scratch.write("sysml-library.prepared", snapshot(&units));
    let dir = library_dir(&scratch);
    let model = scratch.write("garage.sysml", MODEL);
    for args in [&[][..], &["--format", "json"][..]] {
        let from_bundle = check(&lib, &model, &scratch.path("cache-bundle"), args);
        let from_dir = check(&dir, &model, &scratch.path("cache-dir"), args);
        assert_eq!(
            String::from_utf8_lossy(&from_bundle.stderr),
            String::from_utf8_lossy(&from_dir.stderr),
            "{args:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&from_bundle.stdout),
            String::from_utf8_lossy(&from_dir.stdout),
            "{args:?}"
        );
        assert_eq!(from_bundle.status.code(), from_dir.status.code());
    }
    // A finding that names where a library value is bound names the unit
    // by its bundle path, and differs from the directory's in that alone.
    let model = scratch.write("rig.sysml", OVERRIDE);
    for args in [&[][..], &["--format", "json"][..]] {
        let from_bundle = check(&lib, &model, &scratch.path("cache-bundle"), args);
        let from_dir = check(&dir, &model, &scratch.path("cache-dir"), args);
        let [bundle_out, dir_out] = [&from_bundle, &from_dir].map(|out| {
            String::from_utf8_lossy(&out.stderr).into_owned()
                + &String::from_utf8_lossy(&out.stdout)
        });
        assert!(
            bundle_out.contains("validateFeatureValueOverriding"),
            "{bundle_out}"
        );
        assert!(
            bundle_out.contains("bound at Kinds/Parts.sysml:"),
            "{bundle_out}"
        );
        assert!(dir_out.contains("bound at Parts.sysml:"), "{dir_out}");
        assert_eq!(
            bundle_out.replace("Kinds/Parts.sysml", "Parts.sysml"),
            dir_out,
            "{args:?}"
        );
        assert_eq!(from_bundle.status.code(), from_dir.status.code());
    }
}

#[test]
fn a_snapshot_that_does_not_fit_the_bundle_is_passed_over_and_the_library_prepared() {
    let scratch = Scratch::new("mismatch");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    let model = scratch.write("garage.sysml", MODEL);
    let expected = check(&lib, &model, &scratch.path("cache-expected"), &[]);
    assert!(expected.status.success());
    // A snapshot of another library — one unit's text differs — one for
    // another graph format, one stamped by another toolkit build, and one
    // that is not a snapshot at all.
    let mut other = units.clone();
    other[0].1.push_str("\n// edited\n");
    let mut another_build = snapshot(&units);
    let build = libcache::TOOLKIT_BUILD.as_bytes();
    let at = another_build
        .windows(build.len())
        .position(|w| w == build)
        .unwrap();
    another_build[at + build.len() - 1] ^= 0x01;
    for (name, beside) in [
        ("other", snapshot(&other)),
        ("format", snapshot_as(&units, GraphFormat::CanonicalV3)),
        ("build", another_build),
        ("damaged", b"damaged".to_vec()),
    ] {
        let beside_path = scratch.write("sysml-library.prepared", &beside);
        let cache = scratch.path(&format!("cache-{name}"));
        let out = check(&lib, &model, &cache, &[]);
        assert_eq!(out.stderr, expected.stderr, "{name}");
        assert!(out.status.success(), "{name}");
        // The file beside the bundle is the host's: it is left as it lies.
        assert_eq!(std::fs::read(&beside_path).unwrap(), beside, "{name}");
        // The library was prepared and saved for the next run, under the
        // bundle's own content key.
        let key = libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
        assert_eq!(
            cached(&cache),
            [
                format!("stdlib-{key:016x}.libcache"),
                format!("stdlib-{key:016x}.prepared"),
            ],
            "{name}"
        );
        // The next run decodes the cache's snapshot and rewrites nothing.
        let saved = cache.join(format!("stdlib-{key:016x}.prepared"));
        let modified = std::fs::metadata(&saved).unwrap().modified().unwrap();
        let warm = check(&lib, &model, &cache, &[]);
        assert_eq!(warm.stderr, expected.stderr, "{name}");
        assert_eq!(
            std::fs::metadata(&saved).unwrap().modified().unwrap(),
            modified,
            "{name}"
        );
    }
}

#[test]
fn a_beside_snapshot_with_a_damaged_part_is_left_where_it_lies() {
    let scratch = Scratch::new("damaged-part");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    let model = scratch.write("garage.sysml", MODEL);
    let expected = check(&lib, &model, &scratch.path("cache-expected"), &[]);
    // A byte flipped in the middle of the facts, the part read apart from
    // the load: the run finds it out after the snapshot was taken.
    let mut bytes = snapshot(&units);
    let (at, len) = part(&bytes, 5);
    bytes[at + len / 2] ^= 0xff;
    let beside = scratch.write("sysml-library.prepared", &bytes);
    let out = check(&lib, &model, &scratch.path("cache"), &[]);
    assert_eq!(out.stderr, expected.stderr);
    assert!(out.status.success());
    // A damaged part of the cache's own snapshot removes it; one beside a
    // bundle is the host's, and stays as it is.
    assert_eq!(std::fs::read(&beside).unwrap(), bytes);
}

#[test]
fn a_bundle_loads_its_own_ambient_units_whatever_the_ambient_switch_says() {
    let scratch = Scratch::new("ambient");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    scratch.write("sysml-library.prepared", snapshot(&units));
    let model = scratch.write("garage.sysml", MODEL);
    let cache = scratch.path("cache");
    let on = check(&lib, &model, &cache, &[]);
    let off = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["check", "--lib"])
        .arg(&lib)
        .arg(&model)
        .env("SYSMLV2_CACHE_DIR", &cache)
        .env("SYSMLV2_AMBIENT", "off")
        .env_remove("SYSMLV2_LIB_CACHE")
        .output()
        .unwrap();
    // `TransformMeta::Generated` resolves either way: the bundle carries
    // it, and the snapshot beside the bundle serves both runs.
    let stderr = String::from_utf8_lossy(&on.stderr);
    assert!(on.status.success(), "{stderr}");
    assert!(!stderr.contains("TransformMeta"), "{stderr}");
    assert_eq!(off.stderr, on.stderr);
    assert_eq!(cached(&cache), Vec::<String>::new());
}

#[test]
fn a_file_that_is_not_a_bundle_is_refused_by_name() {
    let scratch = Scratch::new("refused");
    let model = scratch.write("garage.sysml", MODEL);
    let cache = scratch.path("cache");
    for (name, text, why) in [
        (
            "model.sysml",
            MODEL,
            "--lib takes a library directory or a bundle file",
        ),
        (
            "empty-name.json",
            r#"[{"name": "", "text": "package P;"}]"#,
            "unit 0 has an empty name",
        ),
        (
            "no-text.json",
            r#"[{"name": "P.sysml"}]"#,
            "unit 0 has no string name and text",
        ),
    ] {
        let lib = scratch.write(name, text);
        let out = check(&lib, &model, &cache, &[]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!out.status.success(), "{name}");
        assert!(stderr.contains("cannot load library"), "{stderr}");
        assert!(stderr.contains(why), "{stderr}");
    }
}

#[test]
fn a_verb_that_loads_a_session_takes_the_bundle_as_its_library() {
    let scratch = Scratch::new("session");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    scratch.write("sysml-library.prepared", snapshot(&units));
    let model = scratch.write("garage.sysml", MODEL);
    let cache = scratch.path("cache");
    let convert = |input: &Path, to: &str| {
        Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .arg("convert")
            .arg(input)
            .args(["--to", to, "--lib"])
            .arg(&lib)
            .env("SYSMLV2_CACHE_DIR", &cache)
            .env_remove("SYSMLV2_LIB_CACHE")
            .output()
            .unwrap()
    };
    let compact = convert(&model, "compact-json");
    assert!(compact.status.success());
    let payload = scratch.write("garage.json", &compact.stdout);
    // The payload is loaded into a session over the bundle's library, and
    // answers as the text built into a model over it does.
    let from_session = convert(&payload, "full-json");
    let from_text = convert(&model, "full-json");
    assert!(
        from_session.status.success(),
        "{}",
        String::from_utf8_lossy(&from_session.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&from_session.stdout),
        String::from_utf8_lossy(&from_text.stdout)
    );
    assert_eq!(cached(&cache), Vec::<String>::new());
}

#[test]
fn without_a_cache_directory_the_snapshot_beside_the_bundle_still_serves() {
    let scratch = Scratch::new("no-cache");
    let units = library();
    let lib = bundle(&scratch, "sysml-library.json", &units);
    let model = scratch.write("garage.sysml", MODEL);
    let expected = check(&lib, &model, &scratch.path("cache"), &[]);
    let uncached = || {
        Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .args(["check", "--lib"])
            .arg(&lib)
            .arg(&model)
            .env_remove("SYSMLV2_CACHE_DIR")
            .env_remove("XDG_CACHE_HOME")
            .env_remove("HOME")
            .env_remove("SYSMLV2_LIB_CACHE")
            .output()
            .unwrap()
    };
    // No snapshot fits and there is nowhere to keep one: the run says so
    // once, and answers from the units.
    let unprepared = uncached();
    let stderr = String::from_utf8_lossy(&unprepared.stderr);
    assert!(unprepared.status.success(), "{stderr}");
    assert_eq!(stderr.matches("no cache directory").count(), 1, "{stderr}");
    assert!(
        stderr.ends_with(&*String::from_utf8_lossy(&expected.stderr)),
        "{stderr}"
    );
    // The snapshot beside the bundle needs no cache directory.
    scratch.write("sysml-library.prepared", snapshot(&units));
    let decoded = uncached();
    assert_eq!(decoded.stderr, expected.stderr);
    assert!(decoded.status.success());
}
