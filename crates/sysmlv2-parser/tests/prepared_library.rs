//! The prepared path must preserve graph identity, diagnostics and evaluation.
use std::sync::Arc;
use sysmlv2_parser::{
    check,
    json::{self, ResolvedModel},
    model::Model,
    prepared::PreparedLibrary,
};
fn diags(model: &Model) -> Vec<(usize, String, String, u32, u32)> {
    let mut r = ResolvedModel::build(model);
    check::validate_model_with(&mut r, model)
        .into_iter()
        .chain(check::validate_semantics_with(&mut r, model))
        .map(|(u, d)| {
            (
                u,
                format!("{:?}", d.severity),
                d.message,
                d.span.start,
                d.span.end,
            )
        })
        .collect()
}
fn parity(library: &[(&str, &str)], users: &[(&str, &str)]) {
    let mut base = Model::new();
    for (n, s) in library {
        base.add_library_source(*n, s);
    }
    let prepared = base.prepare_library().unwrap();
    let bytes = prepared.to_bytes(42).unwrap();
    let prepared = Arc::new(PreparedLibrary::from_bytes(&bytes, 42).expect("snapshot decodes"));
    let bytes = prepared.to_bytes(42).unwrap();
    let mut cold = Model::new();
    for (n, s) in library {
        cold.add_library_source(*n, s);
    }
    let mut warm = Model::new();
    prepared.clone().install(&mut warm).unwrap();
    for (n, s) in users {
        cold.add_source(*n, s);
        warm.add_source(*n, s);
    }
    for _ in 0..2 {
        assert_eq!(
            json::model_to_compact_json(&cold),
            json::model_to_compact_json(&warm),
            "user graph"
        );
        assert_eq!(
            json::library_to_compact_json(&cold),
            json::library_to_compact_json(&warm),
            "library graph"
        );
        assert_eq!(diags(&cold), diags(&warm), "diagnostics");
    }
    assert_eq!(
        prepared.to_bytes(42).unwrap(),
        bytes,
        "models must not mutate their shared snapshot"
    );
}
#[test]
fn prepared_graph_handles_inheritance_chains_aliases_filters_and_user_completion() {
    let lib = [(
        "lib.kerml",
        "package L { datatype Number; class A { feature x : Number; } class B :> A { feature :>> x; } alias C for B; }",
    )];
    for src in [
        "package U { private import L::*; feature a : C; feature x chains a.x; }",
        "package U { private import L::*[true]; feature a : B { feature :>> x; } feature b : A; binding a.x = b.x; }",
        "package L { class A; } package U { feature a : L::A; }",
        "package U { private import Missing::*; feature x : Missing; }",
    ] {
        parity(&lib, &[("user.kerml", src)]);
    }
    parity(
        &[("lib.kerml", "package L { class A :> Later; }")],
        &[(
            "user.kerml",
            "class Later { feature x; } package U { feature a : L::A; feature y chains a.x; }",
        )],
    );
    parity(
        &[(
            "lib.kerml",
            "package Other { class X { feature x; } } package L { class A :> X; }",
        )],
        &[(
            "user.kerml",
            "private import Other::*; package U { feature a : L::A; feature x chains a.x; }",
        )],
    );
    parity(
        &[],
        &[("user.sysml", "package U { part def A; part a : A; }")],
    );
    // An unnamed root feature contributes its inferred name as well.
    parity(
        &[("lib.kerml", "package L { feature f :> x; }")],
        &[("user.kerml", "package P { feature x; } feature :>> P::x;")],
    );
    // A missing implicit library root can be supplied by the user as well.
    parity(
        &[("lib.sysml", "package L { part def A; }")],
        &[(
            "user.sysml",
            "package Parts { part def Part { attribute x; } } package U { part a : L::A; attribute y = a.x; }",
        )],
    );
}
#[test]
fn prepared_cache_rejects_stale_corrupt_and_truncated_data() {
    let mut model = Model::new();
    model.add_library_source("l.sysml", "package L { attribute x = 1.25; }");
    let prepared = model.prepare_library().unwrap();
    let bytes = prepared.to_bytes(19).unwrap();
    assert!(PreparedLibrary::from_bytes(&bytes, 19).is_some());
    assert!(PreparedLibrary::from_bytes(&bytes, 20).is_none());
    for i in (0..bytes.len()).step_by((bytes.len() / 31).max(1)) {
        assert!(PreparedLibrary::from_bytes(&bytes[..i], 19).is_none());
        let mut bad = bytes.clone();
        bad[i] ^= 1;
        assert!(PreparedLibrary::from_bytes(&bad, 19).is_none());
    }
    let mut recording = Model::new();
    prepared.clone().install(&mut recording).unwrap();
    recording.record_library_cache();
    ResolvedModel::build(&recording);
    let legacy = recording
        .take_recorded_library_cache()
        .expect("explicit recording overrides preparation");
    recording.set_library_cache(legacy);
    assert!(check::validate_model(&recording).is_empty());
    let mut occupied = Model::new();
    occupied.add_source("user.sysml", "package U;");
    assert!(prepared.clone().install(&mut occupied).is_err());
    assert!(PreparedLibrary::build(&occupied).is_err());
    let mut warm = Model::new();
    prepared.install(&mut warm).unwrap();
    warm.add_library_source("extra.sysml", "package Extra { part def X; }");
    warm.add_source("user.sysml", "package U { part x : Extra::X; }");
    assert!(
        check::validate_model(&warm).is_empty(),
        "adding libraries invalidates the prepared prefix"
    );
}
/// The snapshot's integrity trailer must be a hash fixed by this crate,
/// not one a toolchain is free to change between releases: a changed hash
/// would reject every snapshot on disk with no version to explain it.
/// Recomputing it here independently pins that.
#[test]
fn prepared_snapshot_trailer_is_a_fixed_hash() {
    use sysmlv2_parser::libcache::TOOLKIT_BUILD;
    let mut model = Model::new();
    model.add_library_source("l.sysml", "package L { attribute x = 1.25; }");
    let bytes = model.prepare_library().unwrap().to_bytes(19).unwrap();
    // Header: magic, the build identity, a newline, the content key, the
    // trailer, then the payload the trailer covers.
    let payload_at = bytes
        .windows(TOOLKIT_BUILD.len())
        .position(|w| w == TOOLKIT_BUILD.as_bytes())
        .expect("the snapshot names the build that wrote it")
        + TOOLKIT_BUILD.len()
        + 1
        + 16;
    let recorded = u64::from_le_bytes(bytes[payload_at - 8..payload_at].try_into().unwrap());
    // FNV-1a, 64-bit — the hash the resolution cache writes too.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for &byte in &bytes[payload_at..] {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100_0000_01b3);
    }
    assert_eq!(recorded, hash);
}

#[test]
fn prepared_official_and_apollo_graphs_and_diagnostics_match_fresh_builds() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    let prepared = base.prepare_library().unwrap();
    let bytes = prepared.to_bytes(91).unwrap();
    let prepared = Arc::new(
        PreparedLibrary::from_bytes(&bytes, 91).expect("complete standard library decodes"),
    );
    for corpus in [
        "spec-refs/SysML-v2-Release/sysml/src",
        "spec-refs/apollo-11-sysml-v2",
    ] {
        let path = sysmlv2_testkit::workspace_root().join(corpus);
        if !path.is_dir() {
            continue;
        }
        let mut paths = Vec::new();
        sysmlv2_testkit::collect_files(&path, &mut paths);
        paths.sort();
        for reverse in [false, true] {
            if reverse {
                paths.reverse();
            }
            let mut cold = Model::new();
            cold.load_library_dir(&library).unwrap();
            let mut warm = Model::new();
            prepared.clone().install(&mut warm).unwrap();
            for p in &paths {
                let source = std::fs::read_to_string(p).unwrap();
                cold.add_source(p.display().to_string(), &source);
                warm.add_source(p.display().to_string(), &source);
            }
            assert_eq!(
                json::model_to_compact_json(&cold),
                json::model_to_compact_json(&warm),
                "{corpus}, reverse={reverse}"
            );
            assert_eq!(diags(&cold), diags(&warm), "{corpus}, reverse={reverse}");
        }
    }
}

#[test]
fn prepared_root_level_imports_stay_on_the_prepared_path_for_the_standard_library() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    let bytes = base.prepare_library().unwrap().to_bytes(17).unwrap();
    let prepared = Arc::new(PreparedLibrary::from_bytes(&bytes, 17).unwrap());
    for source in [
        "private import ScalarValues::*; package P { attribute x : Real = 1; }",
        "package P { attribute x : ScalarValues::Real = 1; } dependency D from P to ScalarValues;",
    ] {
        let mut cold = Model::new();
        cold.load_library_dir(&library).unwrap();
        cold.add_source("user.sysml", source);
        let mut warm = Model::new();
        prepared.clone().install(&mut warm).unwrap();
        warm.add_source("user.sysml", source);
        assert_eq!(diags(&cold), diags(&warm), "{source}");
        assert_eq!(
            json::model_to_compact_json(&cold),
            json::model_to_compact_json(&warm),
            "{source}"
        );
        // Joint resolution would have reconstructed every library file.
        assert_eq!(
            warm.loaded_library_unit_count(),
            0,
            "{source}: the prepared graph must be reused"
        );
    }
}

#[test]
fn prepared_evaluation_preserves_units_calls_and_redefined_values() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        return;
    }
    let mut cold = Model::new();
    cold.load_library_dir(&library).unwrap();
    let prepared = PreparedLibrary::build(&cold).unwrap();
    let bytes = prepared.to_bytes(5).unwrap();
    let prepared = Arc::new(PreparedLibrary::from_bytes(&bytes, 5).unwrap());
    let mut warm = Model::new();
    prepared.install(&mut warm).unwrap();
    let source = "package U {
        private import ScalarValues::*; private import SI::*;
        calc def Twice { in x : Real; return result : Real = x * 2; }
        attribute distance = 1 [km] + 500 [m]; attribute answer = Twice(3);
        part def A { attribute x : Real = 2; }
        part a : A { attribute :>> x = 5; } attribute value = a.x;
    }";
    cold.add_source("user.sysml", source);
    warm.add_source("user.sysml", source);
    let mut a = ResolvedModel::build(&cold);
    let mut b = ResolvedModel::build(&warm);
    for name in ["U::distance", "U::answer", "U::value"] {
        let expected = a.evaluate_qualified(name).unwrap();
        let actual = b.evaluate_qualified(name).unwrap();
        assert_eq!(format!("{expected:?}"), format!("{actual:?}"), "{name}");
    }
    let cold_x = a.resolve_qualified("U::A::x").unwrap();
    let warm_x = b.resolve_qualified("U::A::x").unwrap();
    assert_eq!(
        format!("{:?}", a.references_to(cold_x)),
        format!("{:?}", b.references_to(warm_x))
    );
}

#[test]
fn prepared_negative_diagnostics_match_resolution_replay() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let bytes = base.prepare_library().unwrap().to_bytes(61).unwrap();
    let prepared = Arc::new(PreparedLibrary::from_bytes(&bytes, 61).unwrap());
    let mut fixtures = Vec::new();
    sysmlv2_testkit::collect_files(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml"),
        &mut fixtures,
    );
    fixtures.sort();
    assert_eq!(fixtures.len(), 462);
    for path in fixtures {
        let source = std::fs::read_to_string(&path).unwrap();
        let mut replay = Model::new();
        replay.load_library_dir(&library).unwrap();
        replay.set_library_cache(cache.clone());
        let mut warm = Model::new();
        prepared.clone().install(&mut warm).unwrap();
        replay.add_source(path.display().to_string(), &source);
        warm.add_source(path.display().to_string(), &source);
        assert_eq!(diags(&replay), diags(&warm), "{}", path.display());
    }
}

#[test]
fn prepared_connector_featuring_preserves_chain_and_one_hop_accessibility() {
    let library = [("lib.sysml", "package L { part def D; }")];
    let declarations = "package P {
        part def A { part x : L::D; }
        part def B { part y : L::D; }
        action def Steps { action firstStep; action lastStep; }
    }";
    for connector in [
        "part def C { part a : A; connect a.x to B::y; }",
        "part def C { part a : A; part b : B; connect a.x to b.y; }",
        "part def C { part a : A; connect a.missing to B::y; }",
        "part sys { action run : Steps; succession first run.firstStep then run.lastStep; }",
        "part def C { part a : A; }",
    ] {
        let user = format!("package U {{ private import P::*; {connector} }}");
        for sources in [
            [("defs.sysml", declarations), ("user.sysml", user.as_str())],
            [("user.sysml", user.as_str()), ("defs.sysml", declarations)],
        ] {
            parity(&library, &sources);
        }
    }
}
