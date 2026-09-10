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

/// The workspace root (parent of `crates/`).
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/sysmlv2-testkit sits two levels below the root")
        .to_path_buf()
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
