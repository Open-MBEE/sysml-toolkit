//! Shared libraries preserve the source-library API's graph and edit behavior.
use sysmlv2_wasm::{PreparedLibrary, Session};

fn sources(units: &[(&str, &str)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| serde_json::json!({"name":name,"text":text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}
fn parity(lib: &[(&str, &str)], users: &[(&str, &str)], snapshot: Option<Vec<u8>>) {
    let library = sources(lib);
    let users = sources(users);
    let prepared = PreparedLibrary::new(&library, snapshot.clone()).unwrap();
    let mut cold = Session::from_sources_with_library(&users, Some(library), snapshot).unwrap();
    let mut warm = Session::from_sources_with_prepared_library(&users, &prepared).unwrap();
    for policy in ["passthrough", "closure", "closure-implied"] {
        cold.set_closure_policy(policy).unwrap();
        warm.set_closure_policy(policy).unwrap();
        assert_eq!(cold.to_compact_json(), warm.to_compact_json());
        assert_eq!(cold.to_full_json(true), warm.to_full_json(true));
        assert_eq!(cold.check(), warm.check());
        assert_eq!(cold.units(), warm.units());
        for kind in ["Feature", "Class", "PartUsage"] {
            let a = cold.elements_of_metaclass(kind);
            let b = warm.elements_of_metaclass(kind);
            assert_eq!(a.len(), b.len());
            for (a, b) in a.iter().zip(&b) {
                for name in ["name", "qualifiedName", "type", "inheritedMembership"] {
                    assert_eq!(cold.derived(a, name), warm.derived(b, name));
                }
            }
        }
    }
}

#[test]
fn shared_library_preserves_graphs_diagnostics_closures_and_fallbacks() {
    let lib = [(
        "lib.KerML",
        "package L { class A { feature x; } class B :> A { feature :>> x; } alias C for B; }",
    )];
    for user in [
        "package U { private import L::*; feature a : C; feature x chains a.x; }",
        "package U { private import L::*[true]; feature a : B; feature b : A; binding a.x = b.x; }",
        "package L { class A; } package U { feature a : L::A; }",
        "package U { feature x : Missing; }",
    ] {
        parity(&lib, &[("user.kerml", user)], None);
    }
    parity(
        &[("lib.kerml", "package L { class A :> Later; }")],
        &[(
            "user.kerml",
            "class Later { feature x; } package U { feature a : L::A; feature y chains a.x; }",
        )],
        None,
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
        None,
    );
    parity(
        &[("lib.kerml", "package L { feature f :> x; }")],
        &[("user.kerml", "feature : L::f; feature x;")],
        None,
    );
    parity(
        &[],
        &[("user.sysml", "package U { part def A; part a : A; }")],
        None,
    );
    parity(
        &[
            ("lib.KerML", "package L { class A; }"),
            ("extra.sysml", "package Extra { part def B :> L::A; }"),
        ],
        &[("user.sysml", "package U { part b : Extra::B; }")],
        None,
    );
}

#[test]
fn prepared_sources_reject_stale_corrupt_and_truncated_recordings() {
    let lib = [("lib.kerml", "package L { class A; class B :> A; }")];
    let mut model = sysmlv2_model::model::Model::new();
    for (name, text) in lib {
        model.add_library_source(name, text);
    }
    model.record_library_cache();
    let _ = sysmlv2_model::json::ResolvedModel::build(&model);
    let bytes = model.take_recorded_library_cache().unwrap().to_bytes();
    let user = [("user.sysml", "package U { part a : L::B; }")];
    let mut corrupt = bytes.clone();
    *corrupt.last_mut().unwrap() ^= 1;
    for snapshot in [
        bytes.clone(),
        bytes[..bytes.len() - 1].to_vec(),
        corrupt,
        vec![1, 2, 3],
    ] {
        parity(&lib, &user, Some(snapshot));
    }
    parity(
        &[(
            "lib.kerml",
            "package L { class A; class B { feature added; } }",
        )],
        &user,
        Some(bytes.clone()),
    );
    parity(
        &[
            lib[0],
            ("extra.sysml", "package Extra { part def C :> L::B; }"),
        ],
        &user,
        Some(bytes),
    );
}

#[test]
fn sessions_retain_shared_library_and_isolate_edits() {
    let text = "package L { part def A; attribute value = 3; }";
    let library = PreparedLibrary::new(&sources(&[("lib.sysml", text)]), None).unwrap();
    let user = sources(&[(
        "user.sysml",
        "package U { part a : L::A; attribute n = L::value + 1; }",
    )]);
    let mut first = Session::from_sources_with_prepared_library(&user, &library).unwrap();
    let mut second = Session::from_sources_with_prepared_library(&user, &library).unwrap();
    let original = second.to_compact_json();
    drop(library);
    assert_eq!(first.query("U::n").unwrap(), "4");
    first.set_closure_policy("closure").unwrap();
    first
        .edit(r#"[{"op":"rename","target":"U::a","newName":"renamed"}]"#)
        .unwrap();
    assert!(first.resolve("U::renamed").is_some());
    assert_eq!(first.closure_policy(), "closure");
    assert_eq!(second.to_compact_json(), original);
    assert!(second.resolve("U::a").is_some());
    assert_eq!(second.query("U::n").unwrap(), "4");
}

#[test]
fn prepared_library_supports_interchange_and_attachment() {
    let lib = sources(&[("lib.sysml", "package L { part def A; }")]);
    let prepared = PreparedLibrary::new(&lib, None).unwrap();
    let user = sources(&[("user.sysml", "package U { part a : L::A; }")]);
    let original = Session::from_sources_with_prepared_library(&user, &prepared).unwrap();
    let json = original.to_compact_json();
    let bytes = original.to_compact_cbor();
    let mut old_json =
        Session::from_interchange_json(&json, Some(lib.clone()), None, None).unwrap();
    let mut new_json =
        Session::from_interchange_json_with_prepared_library(&json, &prepared, None).unwrap();
    assert_eq!(old_json.to_compact_json(), new_json.to_compact_json());
    assert_eq!(old_json.check(), new_json.check());
    let old_cbor = Session::from_compact_cbor(&bytes, Some(lib), None, None).unwrap();
    let new_cbor =
        Session::from_compact_cbor_with_prepared_library(&bytes, &prepared, None).unwrap();
    assert_eq!(old_cbor.to_compact_json(), new_cbor.to_compact_json());
    let mut attached = Session::from_sources(&user).unwrap();
    let stale = attached.resolve("U::a").unwrap();
    attached.load_prepared_library(&prepared).unwrap();
    assert!(attached.metaclass(&stale).is_err());
    assert_eq!(attached.to_compact_json(), original.to_compact_json());
}
