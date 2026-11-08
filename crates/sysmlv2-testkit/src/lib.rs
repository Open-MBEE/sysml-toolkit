//! Dev-only helpers shared by the workspace's tests and examples: locating
//! the vendored OMG corpus (`spec-refs/` at the workspace root) and
//! collecting model files. Not published.

use std::fs;
use std::path::{Path, PathBuf};

pub mod xmi_props;

/// The normative property closure for one metaclass, from the vendored
/// metamodel XMI: `(is_abstract, [(property, flags, redefined names)])`
/// with the [`xmi_props::XMI_DERIVED`] / [`xmi_props::XMI_HAS_DEFAULT`]
/// flags.
pub fn xmi_metaclass(name: &str) -> Option<(bool, &'static [xmi_props::XmiProp])> {
    xmi_props::XMI_PROPS
        .binary_search_by(|(n, _, _)| n.cmp(&name))
        .ok()
        .map(|i| {
            let (_, is_abstract, props) = xmi_props::XMI_PROPS[i];
            (is_abstract, props)
        })
}

/// The published `SysML.schema.json` under `spec-refs/`, parsed.
pub fn published_schema() -> serde_json::Value {
    let path = workspace_root().join("spec-refs/SysML.schema.json");
    serde_json::from_str(&fs::read_to_string(&path).expect("the published schema is vendored"))
        .expect("the published schema is JSON")
}

/// Validate every full-form element of `elements` against the
/// *exact-type* variant of its metaclass definition in `schema` (the
/// published schema, [`published_schema`]): detailed per-property errors,
/// at most four per element, stopping after 25 in all. Empty when every
/// element validates.
pub fn validate_elements(
    schema: &serde_json::Value,
    elements: &[serde_json::Value],
) -> Vec<String> {
    let mut validators: std::collections::HashMap<String, jsonschema::Validator> =
        Default::default();
    let mut failures = Vec::new();
    for el in elements {
        let t = el["@type"].as_str().unwrap_or("").to_string();
        let validator = validators.entry(t.clone()).or_insert_with(|| {
            let def = &schema["$defs"][&t];
            let exact = if def.get("anyOf").is_some() {
                def["anyOf"][0].clone()
            } else {
                def.clone()
            };
            let mut mini = exact;
            mini["$defs"] = schema["$defs"].clone();
            jsonschema::validator_for(&mini).expect("the published schema compiles")
        });
        for err in validator.iter_errors(el).take(4) {
            failures.push(format!("{t} @ {}: {err}", err.instance_path()));
        }
        if failures.len() > 25 {
            break;
        }
    }
    failures
}

/// The workspace root (parent of `crates/`).
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/sysmlv2-testkit sits two levels below the root")
        .to_path_buf()
}

/// A pinned normative file under `spec-refs/` (the metamodel XMI and the
/// JSON schemas: `KerML.xmi`, `SysML.xmi`, `KerML.schema.json`,
/// `SysML.schema.json`). Their publication terms do not allow reposting
/// them, so the repository pins their digests and `tools/fetch-spec-refs`
/// downloads them; panics with that instruction when the file is absent.
pub fn spec_ref(name: &str) -> PathBuf {
    let path = workspace_root().join("spec-refs").join(name);
    assert!(
        path.is_file(),
        "{} not found — it is fetched against a pinned digest, not tracked: \
         run\n  python3 tools/fetch-spec-refs\nor see spec-refs/README.md",
        path.display()
    );
    path
}

/// `spec-refs/SysML-v2-Release` — the vendored corpus checkout (a git
/// submodule; a sparse checkout of the four gated directories is
/// enough). Panics with setup instructions when absent or empty — an
/// uninitialized submodule is an empty directory.
pub fn corpus_root() -> PathBuf {
    let root = workspace_root().join("spec-refs/SysML-v2-Release");
    assert!(
        root.join("sysml.library").exists(),
        "corpus not found at {} — initialize the submodule (sparse is \
         enough):\n  git submodule update --init --filter=blob:none \
         spec-refs/SysML-v2-Release\nor see spec-refs/README.md",
        root.display()
    );
    root
}

/// A stable source-unit name relative to a chosen corpus root.
///
/// Source names seed user document identities. Preserve the directory components
/// so files with the same basename remain distinct, and omit checkout-specific
/// prefixes so moving the checkout preserves those identities. The returned
/// separator is `/` on every platform. This helper does no filesystem I/O.
///
/// Panics if `path` is not below `root`, contains a parent traversal, or has a
/// non-UTF-8 component; lossy conversion would not preserve distinct names.
pub fn relative_source_name(root: &Path, path: &Path) -> String {
    let relative = path
        .strip_prefix(root)
        .expect("source lies below corpus root");
    let segments: Vec<_> = relative
        .components()
        .map(|component| match component {
            std::path::Component::Normal(name) => {
                name.to_str().expect("corpus source names are UTF-8")
            }
            _ => panic!("source path must have only normal relative components"),
        })
        .collect();
    assert!(
        !segments.is_empty(),
        "source path names a file below the root"
    );
    segments.join("/")
}

/// The OMG standard library directory within the corpus.
pub fn library_dir() -> PathBuf {
    corpus_root().join("sysml.library")
}

/// Recursively collect `.sysml` / `.kerml` files under `dir` into `out`.
pub fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, out);
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("sysml" | "kerml")
        ) {
            out.push(path);
        }
    }
}

/// Each crate's integration tests build as one binary: `tests/integration.rs`
/// declares every other `tests/*.rs` file as a module, except a file that
/// needs a process of its own, which the crate's `Cargo.toml` names as a
/// test target of its own. Cargo builds no file in neither place, so this
/// panics naming each one: a new test file cannot silently never run.
/// `root` is the source of `tests/integration.rs`.
pub fn assert_suite_declares_every_test_file(manifest_dir: &str, root: &str) {
    let manifest = fs::read_to_string(Path::new(manifest_dir).join("Cargo.toml"))
        .expect("the crate's manifest");
    let mut declared: Vec<String> = root
        .lines()
        .filter_map(|line| line.trim().strip_prefix("mod ")?.strip_suffix(';'))
        .map(|name| format!("tests/{name}.rs"))
        .collect();
    declared.extend(manifest.lines().filter_map(|line| {
        let path = line.trim().strip_prefix("path")?.trim_start();
        Some(path.strip_prefix('=')?.trim().trim_matches('"').to_owned())
    }));
    let mut missing = Vec::new();
    let tests = Path::new(manifest_dir).join("tests");
    for entry in fs::read_dir(&tests).expect("the crate has a tests directory") {
        let path = entry.expect("readable tests directory").path();
        if path.extension().is_some_and(|e| e == "rs") {
            let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if !declared.contains(&format!("tests/{name}")) {
                missing.push(name.to_owned());
            }
        }
    }
    missing.sort();
    assert!(
        missing.is_empty(),
        "neither a `mod` in tests/integration.rs nor a test target in Cargo.toml: {}",
        missing.join(", ")
    );
}

/// `f` over every item, spread across the machine's cores, with the
/// results in `items`' order: for fixture loops whose items are
/// independent, so a long loop costs its share of the cores rather than
/// one. Each item runs exactly once; a panic in `f` fails the caller
/// with its own message once the other items are done.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let next = AtomicUsize::new(0);
    let workers = std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .clamp(1, items.len().max(1));
    let mut done: Vec<(usize, R)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                scope.spawn(|| {
                    let mut out = Vec::new();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(i) else {
                            return out;
                        };
                        out.push((i, f(item)));
                    }
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    });
    done.sort_by_key(|(i, _)| *i);
    done.into_iter().map(|(_, r)| r).collect()
}

/// The gated corpus directories within the release checkout — exactly
/// the sparse-checkout cone. Collection is pinned to these so a *full*
/// submodule checkout (which carries extra model trees under `kerml/`)
/// yields the same 345-file corpus as the sparse one.
const CORPUS_DIRS: [&str; 4] = [
    "sysml.library",
    "sysml/src/examples",
    "sysml/src/training",
    "sysml/src/validation",
];

/// Every corpus model file (library + user), sorted; asserts the full
/// checkout is present.
pub fn corpus_files() -> Vec<PathBuf> {
    let root = corpus_root();
    let mut files = Vec::new();
    for dir in CORPUS_DIRS {
        collect_files(&root.join(dir), &mut files);
    }
    files.sort();
    assert!(files.len() > 340, "expected the full corpus checkout");
    files
}

/// The non-library corpus files, sorted.
pub fn user_files() -> Vec<PathBuf> {
    let root = corpus_root();
    let mut files = Vec::new();
    for dir in &CORPUS_DIRS[1..] {
        collect_files(&root.join(dir), &mut files);
    }
    files.sort();
    files
}

/// `spec-refs/apollo-11-sysml-v2` — the Airbus Apollo 11 external
/// validation model (git submodule). `None` when the
/// submodule is not initialized — callers *skip with a note* so plain
/// clones stay green (`git submodule update --init` enables the gates).
pub fn apollo_root() -> Option<PathBuf> {
    let root = workspace_root().join("spec-refs/apollo-11-sysml-v2");
    root.join("Apollo11Model.sysml").exists().then_some(root)
}

/// The Apollo model's `.sysml` files, sorted; `None` when the submodule
/// is not initialized.
pub fn apollo_files() -> Option<Vec<PathBuf>> {
    let root = apollo_root()?;
    let mut files = Vec::new();
    collect_files(&root, &mut files);
    files.retain(|f| f.extension().is_some_and(|e| e == "sysml"));
    files.sort();
    assert!(files.len() >= 28, "expected the full Apollo checkout");
    Some(files)
}

#[cfg(test)]
mod source_identity_tests {
    use super::relative_source_name;
    use std::path::Path;

    #[test]
    fn relative_source_names_preserve_directories_and_ignore_checkout_location() {
        let first = relative_source_name(
            Path::new("checkout-a"),
            Path::new("checkout-a/examples/model.sysml"),
        );
        let second = relative_source_name(
            Path::new("checkout-a"),
            Path::new("checkout-a/validation/model.sysml"),
        );
        assert_eq!(first, "examples/model.sysml");
        assert_eq!(second, "validation/model.sysml");
        assert_ne!(first, second);
        assert_eq!(
            first,
            relative_source_name(
                Path::new("checkout-b"),
                Path::new("checkout-b/examples/model.sysml")
            )
        );
    }

    #[test]
    #[should_panic(expected = "source lies below corpus root")]
    fn unrelated_paths_do_not_fall_back_to_a_basename() {
        relative_source_name(Path::new("checkout-a"), Path::new("checkout-b/model.sysml"));
    }

    #[test]
    #[should_panic(expected = "normal relative components")]
    fn parent_traversal_is_not_a_relative_identity() {
        relative_source_name(
            Path::new("checkout-a"),
            Path::new("checkout-a/../model.sysml"),
        );
    }
}
