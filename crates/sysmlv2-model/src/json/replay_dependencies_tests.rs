//! A library resolution recording replays an outcome only while the root
//! names its resolution missed stay missing. Resolution also reads state
//! that outlives the reference being resolved — lookup caches, other
//! references' recorded outcomes, the recorded lookup graph — so an outcome
//! depends on the names missed while that state was computed, whichever
//! reference computed it. Each case builds a library whose later references
//! reach a root name only through such state, adds a model that supplies
//! the name, and compares every replaying path with a cold build. The last
//! cases vary whether resolution runs its later passes at all.

use super::derived::{Derived, DerivedValue, Reference};
use super::{ResolvedModel, library_to_compact_json, model_to_compact_json};
use crate::libcache::LibraryCache;
use crate::model::Model;
use serde_json::Value;
use std::path::{Path, PathBuf};

/// A library directory under a fresh temporary root, removed on drop.
struct LibraryDir {
    root: PathBuf,
}

impl LibraryDir {
    fn new(library: &str, extension: &str) -> Self {
        let root = std::env::temp_dir().join(format!("sysml-replay-deps-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir_all(root.join("library")).unwrap();
        std::fs::write(
            root.join("library").join(format!("Lib.{extension}")),
            library,
        )
        .unwrap();
        Self { root }
    }

    fn dir(&self) -> PathBuf {
        self.root.join("library")
    }

    fn recording(&self) -> PathBuf {
        self.root.join("cache").join("stdlib.libcache")
    }
}

impl Drop for LibraryDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

/// The library as the directory loader reads it: the file, then the
/// ambient units.
fn library_model(dir: &Path) -> Model {
    let mut model = Model::new();
    model.load_library_dir(dir).unwrap();
    crate::ambient::add_to(&mut model);
    model
}

/// What a build says about the model and the library.
#[derive(Debug)]
struct Outputs {
    user: Value,
    library: Value,
    /// Per probe, the derived `type` targets by interchange id (or the
    /// spelling a reference kept when it did not resolve).
    types: Vec<(String, Vec<String>)>,
}

fn outputs(model: &Model, probes: &[&str]) -> Outputs {
    let mut resolved = ResolvedModel::build(model);
    let types = probes
        .iter()
        .map(|&probe| {
            let e = resolved
                .resolve_qualified(probe)
                .unwrap_or_else(|| panic!("`{probe}` names an element"));
            let targets = match resolved.derived(e, "type") {
                Derived::Value(DerivedValue::References(targets)) => targets
                    .iter()
                    .map(|target| match target {
                        Reference::Element(t) => resolved.element_id(*t).to_string(),
                        other => format!("{other:?}"),
                    })
                    .collect(),
                other => vec![format!("{other:?}")],
            };
            (probe.to_string(), targets)
        })
        .collect();
    Outputs {
        user: model_to_compact_json(model),
        library: library_to_compact_json(model),
        types,
    }
}

/// Where `actual` departs from `cold`: the probed types, else the first
/// differing element of the user or library graph.
fn divergence(actual: &Outputs, cold: &Outputs) -> Option<String> {
    if actual.types != cold.types {
        return Some(format!("types {:?}, cold {:?}", actual.types, cold.types));
    }
    for (graph, a, c) in [
        ("user", &actual.user, &cold.user),
        ("library", &actual.library, &cold.library),
    ] {
        let (a, c) = (a.as_array().unwrap(), c.as_array().unwrap());
        if let Some(i) = (0..a.len().max(c.len())).find(|&i| a.get(i) != c.get(i)) {
            return Some(format!(
                "{graph} element {i}: {}\ncold: {}",
                a.get(i).map_or("none".into(), Value::to_string),
                c.get(i).map_or("none".into(), Value::to_string)
            ));
        }
    }
    None
}

/// Build `user` over `library` cold, replaying a recording of the library
/// alone (the in-memory sources-with-snapshot path), and on a prepared
/// directory library whose root misses force a joint build that replays
/// the recording it saved; all three must agree. Returns the cold outputs.
fn replaying_builds_agree(library: &str, user: &str, probes: &[&str]) -> Outputs {
    replaying_builds_agree_in("sysml", library, user, probes)
}

/// [`replaying_builds_agree`] for sources of the dialect `extension` names.
fn replaying_builds_agree_in(
    extension: &str,
    library: &str,
    user: &str,
    probes: &[&str],
) -> Outputs {
    builds_agree_in(extension, library, user, probes, DirectoryBuild::Joint)
}

/// How a model builds on a directory library that was prepared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DirectoryBuild {
    /// The model completes a root miss of the prepared library, so it
    /// resolves jointly with it, replaying the recording saved beside it.
    Joint,
    /// The model completes none: it resolves on the prepared library.
    Prepared,
}

/// Build `user` over `library` cold, replaying a recording of the library
/// alone, and on a prepared directory library, which the model must build
/// on as `directory_build` says; all three must agree. Returns the cold
/// outputs.
fn builds_agree_in(
    extension: &str,
    library: &str,
    user: &str,
    probes: &[&str],
    directory_build: DirectoryBuild,
) -> Outputs {
    let files = LibraryDir::new(library, extension);
    let user_unit = format!("user.{extension}");

    let mut cold = library_model(&files.dir());
    cold.add_source(&user_unit, user);
    let cold = outputs(&cold, probes);

    let mut recorder = library_model(&files.dir());
    recorder.record_library_cache();
    ResolvedModel::build(&recorder);
    let recording = recorder.take_recorded_library_cache().unwrap();
    let recording = LibraryCache::from_bytes(&recording.to_bytes()).unwrap();
    let mut snapshot = library_model(&files.dir());
    snapshot.set_library_cache(recording);
    snapshot.add_source(&user_unit, user);
    if let Some(divergence) = divergence(&outputs(&snapshot, probes), &cold) {
        panic!(
            "replaying a recording diverged from a cold build\nlibrary: {library}\nuser: {user}\n{divergence}"
        );
    }
    assert_eq!(snapshot.lib_cache_kind(), "use");

    // A fresh content key per call: prepared libraries are shared per key.
    let key = uuid::Uuid::new_v4().as_u64_pair().0;
    let cache = || Some((key, files.recording()));
    let mut preparing = Model::new();
    crate::prepared::load_library_with_cache_at(&mut preparing, &files.dir(), cache()).unwrap();
    drop(preparing);
    assert!(files.recording().exists(), "preparing records the library");
    let mut directory = Model::new();
    crate::prepared::load_library_with_cache_at(&mut directory, &files.dir(), cache()).unwrap();
    directory.add_source(&user_unit, user);
    let prepared = ResolvedModel::build(&directory).b.library_facts.is_some();
    match directory_build {
        DirectoryBuild::Joint => {
            assert!(
                !prepared,
                "the model completes a root miss of the prepared library"
            );
            assert_eq!(
                directory.lib_cache_kind(),
                "use",
                "the joint build replays the recording"
            );
        }
        DirectoryBuild::Prepared => {
            assert!(prepared, "the model builds on the prepared library");
        }
    }
    if let Some(divergence) = divergence(&outputs(&directory, probes), &cold) {
        panic!(
            "a directory library's {directory_build:?} build diverged from a cold build\nlibrary: {library}\nuser: {user}\n{divergence}"
        );
    }

    // A library prepared in memory while recording keeps that recording,
    // and a build that cannot reuse its prepared graph replays it.
    let mut recording_alone = library_model(&files.dir());
    recording_alone.record_library_cache();
    let mut memory = Model::new();
    recording_alone
        .prepare_library()
        .unwrap()
        .install(&mut memory)
        .unwrap();
    memory.add_source(&user_unit, user);
    let prepared = ResolvedModel::build(&memory).b.library_facts.is_some();
    match directory_build {
        DirectoryBuild::Joint => {
            assert!(
                !prepared,
                "the model completes a root miss of the library prepared in memory"
            );
            assert_eq!(
                memory.lib_cache_kind(),
                "use",
                "the joint build replays the recording the library was prepared with"
            );
        }
        DirectoryBuild::Prepared => {
            assert!(
                prepared,
                "the model builds on the library prepared in memory"
            );
        }
    }
    if let Some(divergence) = divergence(&outputs(&memory, probes), &cold) {
        panic!(
            "an in-memory prepared library's {directory_build:?} build diverged from a cold build\nlibrary: {library}\nuser: {user}\n{divergence}"
        );
    }
    cold
}

fn resolved_types(outputs: &Outputs) -> bool {
    outputs
        .types
        .iter()
        .all(|(_, targets)| targets.len() == 1 && !targets[0].contains("Unresolved"))
}

/// `j` reaches `X` only through `A`'s specialization base, which the
/// scope's base cache resolved while `i` was resolving.
const BASE_CACHE_LIBRARY: &str = "package Other { part def X { part def Inner; part def Inner2; } }
package L { part def A :> X { part i : Inner; part j : Inner2; } }";

#[test]
fn outcomes_read_through_the_base_cache_replay_only_while_its_misses_stay_missing() {
    for user in [
        "private import Other::*; package P { part a : L::A; }",
        "part def X { part def Inner; part def Inner2; } package P { part a : L::A; }",
    ] {
        let cold = replaying_builds_agree(
            BASE_CACHE_LIBRARY,
            user,
            &["L::A::i", "L::A::j", "P::a::i", "P::a::j"],
        );
        assert!(resolved_types(&cold), "{user}: {:?}", cold.types);
    }
}

#[test]
fn outcomes_read_through_the_import_cache_replay_only_while_its_misses_stay_missing() {
    let cold = replaying_builds_agree(
        "package L { import X::*; part a : Inner; part b : Inner2; }",
        "package X { part def Inner; part def Inner2; }",
        &["L::a", "L::b"],
    );
    assert!(resolved_types(&cold), "{:?}", cold.types);
    assert!(
        !cold.library.to_string().contains(r#"{"@ref":"X"}"#),
        "the library import resolves once the model supplies its target"
    );
}

#[test]
fn outcomes_read_through_a_cache_replay_soundly_across_resolution_passes() {
    // A redefinition makes the build resolve in several passes; each pass
    // starts from empty caches and must attribute its misses again.
    let cold = replaying_builds_agree(
        "package Other { part def X { part def Inner; part def Inner2; part y; } }
package L { part def A :> X { part i : Inner; part j : Inner2; part :>> y; } }",
        "private import Other::*; package U { part a : L::A; }",
        &["L::A::i", "L::A::j", "U::a::j"],
    );
    assert!(resolved_types(&cold), "{:?}", cold.types);
}

#[test]
fn outcomes_read_through_another_references_outcome_depend_on_its_misses() {
    // `w :> y` meets `A`'s `:>> y` and `K::y`; whether the first shadows the
    // second is `A`'s recorded redefinition outcome, which resolves only
    // once the model supplies `X`. `w`'s own lookup never reaches `X`.
    let cold = replaying_builds_agree(
        "package Other { part def X :> L::K; }
package L {
    part def K { part y; }
    part def A :> X { part :>> y; }
    part def C :> A, K { part w :> y; }
}",
        "private import Other::*; package P { part c : L::C; }",
        &[],
    );
    assert!(
        !cold
            .library
            .to_string()
            .contains(r#""subsettedFeature":{"@ref":"y"}"#),
        "the model's import settles `w :> y`"
    );
}

#[test]
fn outcomes_read_through_the_recorded_lookup_graph_depend_on_its_inputs() {
    // A later resolution pass settles the anonymous feature's `:>> y` in its
    // header base `A`, reading `A`'s projection from the recorded lookup
    // graph — which rests on `A :> X`. The model supplies `X`, so a joint
    // build must resolve that redefinition again rather than replay it.
    replaying_builds_agree_in(
        "kerml",
        "package Other {
    feature :> L::A { feature y; feature y; feature :>> y; alias for K; }
}
package L {
    feature A :> X { feature :>> y; class Inner; }
    feature :> A, X { feature : Inner; }
}",
        "feature X { class Inner; }",
        &[],
    );
}

#[test]
fn a_cache_entry_does_not_take_the_mode_of_the_lookup_that_fills_it() {
    // `K :> X` finds `X` through the membership import, whose own target
    // `Other::X` looks up `Other` through the namespace imports of `L` —
    // computing them while that membership import resolves itself. The
    // entry must still see it: `import X::*` resolves, and `Inner` with it.
    // (`Extra` only makes the model resolve jointly with the library.)
    let cold = replaying_builds_agree(
        "package Other { part def X { part def Inner; } }
package L {
    import X::*;
    private import Other::X;
    part def K :> X;
    part i : Inner;
    part def J :> Extra;
}",
        "part def Extra; package P { part k : L::K; }",
        &["L::i"],
    );
    assert!(resolved_types(&cold), "{:?}", cold.types);
    assert!(
        !cold.library.to_string().contains(r#"{"@ref":"X"}"#),
        "the namespace import resolves"
    );
}

#[test]
fn a_redefinition_header_alone_makes_the_library_resolve_in_passes() {
    // `k`'s `:>> z` resolves in its header base `K` once the recorded lookup
    // graph is ready, where the lexical bootstrap takes the sibling `k::z`.
    // Nothing else in the library asks for later passes (the redefining
    // feature's typing does not resolve, so it is no complete graph node),
    // while the model's `p : L::K` does. A recording that stopped after
    // the bootstrap kept the sibling, which the joint build does not.
    builds_agree_in(
        "kerml",
        "package L { class K { feature z; } feature k : K { feature z; feature :>> z : Missing; } }",
        "package P { feature p : L::K; }",
        &[],
        DirectoryBuild::Prepared,
    );
}

#[test]
fn a_root_import_completes_the_absence_the_recorded_lookup_graph_took() {
    // Alone, the library resolves in passes: its classes are graph nodes,
    // which take their implied roots as absent because the root imports
    // nothing. Any root import withdraws those nodes, so the joint build
    // stops after the lexical bootstrap: `f0 : Inner2` takes `X`'s own
    // `Inner2`, where the graph selects both that `K` inherits. The import
    // brings in nothing the library missed, yet `f0`'s typing must resolve
    // again rather than replay.
    builds_agree_in(
        "kerml",
        "package L {
    class X :> Y { class Inner2; }
    class Y { class Inner2; }
    class K :> X { feature f0 : Inner2; }
}",
        "package Q { } private import Q::*;",
        &["L::K::f0"],
        DirectoryBuild::Joint,
    );
}
