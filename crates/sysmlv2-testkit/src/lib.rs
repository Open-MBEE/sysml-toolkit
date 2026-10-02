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
