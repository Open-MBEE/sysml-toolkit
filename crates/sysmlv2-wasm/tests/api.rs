//! Native tests over the wasm binding surface. The binding's boundary
//! is JSON strings and plain handles — no JS types — so everything here
//! runs on the host; the wasm target changes the ABI, not the logic
//! (the wasm32 build is gated by `cargo check --target
//! wasm32-unknown-unknown -p sysmlv2-wasm`).

use sysmlv2_wasm::{
    Session, canonical_name_js, canonicalize_compact, check, graph_normalize_compact,
    spell_reference_js, state_digest_of, version,
};

fn sources(pairs: &[(&str, &str)]) -> String {
    serde_json::to_string(
        &pairs
            .iter()
            .map(|(n, t)| serde_json::json!({"name": n, "text": t}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

/// A byte offset reported as a JSON number, as an index.
fn offset(v: &serde_json::Value) -> usize {
    usize::try_from(v.as_u64().expect("offset is a number")).expect("offset indexes this host")
}

const FLASHLIGHT: &str = "package Flashlight {\n    part def Body;\n    part def Battery {\n        attribute voltage = 3;\n    }\n    part flashlight {\n        part body : Body;\n        part battery : Battery;\n    }\n}\n";

#[test]
fn session_navigation_and_query() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let pkg = s.resolve("Flashlight").expect("package resolves");
    assert_eq!(s.metaclass(&pkg).unwrap(), "Package");
    assert_eq!(
        s.qualified_name(&pkg).unwrap().as_deref(),
        Some("Flashlight")
    );
    let members = s.members(&pkg).unwrap();
    assert_eq!(members.len(), 3);
    let battery = s.resolve("Flashlight::flashlight::battery").unwrap();
    let typings = s.typings(&battery).unwrap();
    assert_eq!(typings.len(), 1);
    assert_eq!(
        s.qualified_name(&typings[0]).unwrap().as_deref(),
        Some("Flashlight::Battery")
    );
    let owner = s.owner(&battery).unwrap().expect("owned");
    assert_eq!(
        s.qualified_name(&owner).unwrap().as_deref(),
        Some("Flashlight::flashlight")
    );
    assert!(!s.is_library_element(&battery).unwrap());
    assert_eq!(s.elements_of_metaclass("PartDefinition").len(), 2);

    let voltage = s.resolve("Flashlight::Battery::voltage").unwrap();
    assert_eq!(s.evaluate(&voltage).unwrap(), "3");
    let q: serde_json::Value =
        serde_json::from_str(&s.query("Flashlight::Battery::voltage + 1").unwrap()).unwrap();
    assert_eq!(q, serde_json::json!(4));
}

#[test]
fn roots_walk_the_outline() {
    let mut s = Session::from_sources(&sources(&[
        ("flashlight.sysml", FLASHLIGHT),
        ("extra.sysml", "package Extra { part def Case; }"),
    ]))
    .unwrap();
    let roots = s.roots();
    let names: Vec<Option<String>> = roots.iter().map(|e| s.name(e).unwrap()).collect();
    assert_eq!(
        names,
        vec![Some("Flashlight".to_string()), Some("Extra".to_string())]
    );
    // Outline recursion: members of a root are reachable and named.
    let members = s.members(&roots[0]).unwrap();
    assert_eq!(members.len(), 3);
    assert_eq!(s.metaclass(&members[0]).unwrap(), "PartDefinition");
}

#[test]
fn units_and_interchange_roundtrip() {
    let s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let units: serde_json::Value = serde_json::from_str(&s.units()).unwrap();
    assert_eq!(units.as_array().unwrap().len(), 1);
    assert_eq!(units[0]["name"], "flashlight.sysml");
    assert!(
        units[0]["text"]
            .as_str()
            .unwrap()
            .contains("part def Battery")
    );

    let full = s.to_full_json(true);
    let mut back = Session::from_interchange_json(&full, None, None, None).unwrap();
    assert!(back.resolve("Flashlight::flashlight::battery").is_some());
    assert_eq!(back.unresolved_count(), 0);
    let warnings: serde_json::Value = serde_json::from_str(&back.warnings()).unwrap();
    assert_eq!(warnings, serde_json::json!([]));

    let compact = s.to_compact_json();
    assert!(compact.contains("\"@type\""));
}

#[test]
fn annotation_targets_are_navigable() {
    let src = "package P {
        part def A;
        metadata def M;
        metadata record : M about A;
        metadata dangling : M about Missing;
    }";
    let mut s = Session::from_sources(&sources(&[("annotations.sysml", src)])).unwrap();
    let record = s.resolve("P::record").unwrap();
    let targets = s.annotated_elements(&record).unwrap();
    assert_eq!(targets.len(), 1);
    assert_eq!(
        s.qualified_name(&targets[0]).unwrap().as_deref(),
        Some("P::A")
    );
    let dangling = s.resolve("P::dangling").unwrap();
    assert!(s.annotated_elements(&dangling).unwrap().is_empty());
}

#[test]
fn canonicalize_compact_bridges_default_elision() {
    let s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let compact = s.to_compact_json();
    let spelled = canonicalize_compact(&compact).unwrap();

    // Simulate the service's wire elision: drop the default-valued
    // spellings a session document carries explicitly.
    let mut doc: serde_json::Value = serde_json::from_str(&compact).unwrap();
    let mut dropped = 0usize;
    for el in doc.as_array_mut().unwrap() {
        let id = el["@id"].clone();
        let obj = el.as_object_mut().unwrap();
        for (k, d) in [
            ("isUnique", serde_json::json!(true)),
            ("isAbstract", serde_json::json!(false)),
            ("visibility", serde_json::json!("public")),
            ("elementId", id),
        ] {
            if obj.get(k) == Some(&d) && obj.remove(k).is_some() {
                dropped += 1;
            }
        }
    }
    assert!(dropped > 0, "the elision simulation bites");
    let from_wire = canonicalize_compact(&doc.to_string()).unwrap();
    assert_eq!(spelled, from_wire, "elision split is bridged");
    assert_eq!(
        canonicalize_compact(&spelled).unwrap(),
        spelled,
        "idempotent"
    );
    assert!(canonicalize_compact("[{\"@type\": \"Nope\", \"@id\": \"x\"}]").is_err());
}

#[test]
fn graph_normalize_compact_lands_in_the_stored_digest_cell() {
    // The mirror twin: a session document (kernel spelling) and its
    // canonicalized (maximally spelled) form graph-normalize to the
    // SAME document — the stored spelling a graph-backed service
    // reconstructs — so one state digest covers both spellings.
    let s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let compact = s.to_compact_json();
    let normal = graph_normalize_compact(&compact).unwrap();
    let spelled = canonicalize_compact(&compact).unwrap();
    assert_eq!(
        graph_normalize_compact(&spelled).unwrap(),
        normal,
        "spelling domains collapse"
    );
    assert_eq!(
        graph_normalize_compact(&normal).unwrap(),
        normal,
        "idempotent"
    );
    assert_eq!(
        state_digest_of(&graph_normalize_compact(&spelled).unwrap()).unwrap(),
        state_digest_of(&normal).unwrap(),
        "one digest cell"
    );
    // The stored spelling elides defaults the kernel spells, and pins
    // elements to id order.
    let doc: serde_json::Value = serde_json::from_str(&normal).unwrap();
    let arr = doc.as_array().unwrap();
    let ids: Vec<&str> = arr.iter().map(|e| e["@id"].as_str().unwrap()).collect();
    let mut sorted = ids.clone();
    sorted.sort_unstable();
    assert_eq!(ids, sorted, "id-sorted listing order");
    assert!(
        arr.iter().all(|e| e["elementId"].is_string()),
        "elementId always spelled"
    );
    assert!(
        arr.iter()
            .all(|e| e.as_object().unwrap().get("isUnique") != Some(&serde_json::json!(true))),
        "true-default isUnique elided"
    );
    assert!(graph_normalize_compact("[{\"@type\": \"Nope\", \"@id\": \"x\"}]").is_err());
}

#[test]
fn plantuml_views_and_options() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let uml = s.to_plantuml(None).unwrap();
    assert!(uml.starts_with("@startuml"));
    assert!(uml.contains("Battery"));
    let ic = s
        .to_plantuml(Some(
            r#"{"view": "ic", "element": "Flashlight::flashlight", "horizontal": true}"#.into(),
        ))
        .unwrap();
    assert!(ic.starts_with("@startuml"));
    assert!(s.to_plantuml(Some(r#"{"view": "nope"}"#.into())).is_err());
    assert!(
        s.to_plantuml(Some(r#"{"element": "No::Such"}"#.into()))
            .is_err()
    );
    assert!(s.to_plantuml(Some(r#"{"vieww": "tree"}"#.into())).is_err());
}

#[test]
fn stale_handles_error_after_library_load() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let pkg = s.resolve("Flashlight").unwrap();
    s.load_library_sources(
        &sources(&[(
            "MiniLib.kerml",
            "standard library package MiniLib { class Thing; }",
        )]),
        None,
    )
    .unwrap();
    assert!(s.qualified_name(&pkg).is_err());
    let thing = s
        .resolve("MiniLib::Thing")
        .expect("library element resolves");
    assert!(s.is_library_element(&thing).unwrap());
}

#[test]
fn check_findings_shape() {
    // Clean parse: no findings without a library.
    let clean = check(&sources(&[("flashlight.sysml", FLASHLIGHT)]), None, None).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&clean).unwrap(),
        serde_json::json!([])
    );

    // A parse error is a finding with a 1-based position.
    let bad = check(&sources(&[("bad.sysml", "part def {")]), None, None).unwrap();
    let bad: serde_json::Value = serde_json::from_str(&bad).unwrap();
    let f = &bad.as_array().unwrap()[0];
    assert_eq!(f["severity"], "error");
    assert_eq!(f["unit"], "bad.sysml");
    assert!(f["line"].as_u64().unwrap() >= 1);

    // In-memory library: an unresolved reference is only diagnosed when
    // referential checks run, and the library satisfies it.
    let lib = sources(&[(
        "MiniLib.kerml",
        "standard library package MiniLib { class Thing; }",
    )]);
    let user = sources(&[(
        "uses.sysml",
        "package Uses { part def Widget; part w : Widget; }",
    )]);
    let with_lib = check(&user, Some(lib.clone()), None).unwrap();
    let with_lib: serde_json::Value = serde_json::from_str(&with_lib).unwrap();
    assert_eq!(with_lib, serde_json::json!([]));

    // Findings carry an end position spanning the whole diagnosed
    // construct, not just its start.
    let user = sources(&[("dangling.sysml", "package Dangling { part w : Missing; }")]);
    let dangling = check(&user, Some(lib), None).unwrap();
    let dangling: serde_json::Value = serde_json::from_str(&dangling).unwrap();
    let f = &dangling.as_array().unwrap()[0];
    assert_eq!(f["severity"], "warning");
    assert_eq!(f["endLine"], f["line"]);
    assert_eq!(
        f["endCol"].as_u64().unwrap(),
        f["col"].as_u64().unwrap() + "Missing".len() as u64
    );
}

/// A user root package named like a standard-library root: `check`
/// reports the collision at the user declaration, and `resolve` keeps
/// landing on the library package (the behavior the warning describes).
#[test]
fn check_reports_user_roots_shadowing_library_roots() {
    let lib = sources(&[(
        "MiniLib.sysml",
        "standard library package Requirements { requirement def Base; }",
    )]);
    let user = sources(&[(
        "shadow.sysml",
        "package Requirements {\n    requirement def Speed;\n}\n",
    )]);
    let findings = check(&user, Some(lib.clone()), None).unwrap();
    let findings: serde_json::Value = serde_json::from_str(&findings).unwrap();
    assert_eq!(
        findings,
        serde_json::json!([{
            "severity": "warning",
            "stage": "referential",
            "message": "root package `Requirements` shadows the standard library package \
                        `Requirements`; references resolve to the library",
            "unit": "shadow.sysml",
            "line": 1,
            "col": 9,
            "endLine": 1,
            "endCol": 9 + "Requirements".len(),
        }])
    );
    // Without a library there is nothing to shadow.
    let alone = check(&user, None, None).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&alone).unwrap(),
        serde_json::json!([])
    );

    let mut s = Session::from_sources(&user).unwrap();
    s.load_library_sources(&lib, None).unwrap();
    let pkg = s.resolve("Requirements").expect("the root name resolves");
    assert_eq!(s.metaclass(&pkg).unwrap(), "LibraryPackage");
    assert!(s.is_library_element(&pkg).unwrap());
    assert!(s.resolve("Requirements::Speed").is_none());
}

#[test]
fn version_matches_crate() {
    assert_eq!(version(), env!("CARGO_PKG_VERSION"));
}

/// The LSP surface over the wasm boundary: a push conversation through
/// the exported class (string transport, no threads).
#[test]
fn lsp_server_push_conversation() {
    let mut lsp = sysmlv2_wasm::LspServer::new();
    let out = lsp
        .handle(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#)
        .unwrap();
    assert!(out[0].contains("sysmlv2-lsp"));
    let out = lsp
        .handle(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///w/m.sysml","languageId":"sysml","version":1,"text":"package P { part def X; }"}}}"#,
        )
        .unwrap();
    assert!(out.iter().any(|m| m.contains("publishDiagnostics")));
    let out = lsp
        .handle(
            r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///w/m.sysml"}}}"#,
        )
        .unwrap();
    assert!(
        out[0].contains("\"P\""),
        "symbol tree names the package: {}",
        out[0]
    );

    // The library shape through the factory: completions offer library
    // names.
    let mut lib_lsp = sysmlv2_wasm::LspServer::with_library(
        &sources(&[(
            "MiniLib.kerml",
            "standard library package MiniLib { class Widget; }",
        )]),
        None,
    )
    .unwrap();
    lib_lsp
        .handle(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#)
        .unwrap();
    lib_lsp
        .handle(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///w/m.sysml","languageId":"sysml","version":1,"text":"package P { }"}}}"#,
        )
        .unwrap();
    let out = lib_lsp
        .handle(
            r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/completion","params":{"textDocument":{"uri":"file:///w/m.sysml"},"position":{"line":0,"character":10}}}"#,
        )
        .unwrap();
    assert!(
        out[0].contains("Widget"),
        "library member offered: {}",
        out[0]
    );
}

/// The snapshot path: a sealed snapshot recorded against library
/// sources replays through `loadLibrarySources`, and the warm build is
/// byte-identical to the cold one (the equivalence gate, over the
/// wasm surface). Foreign/stale snapshot bytes fall back to a cold
/// build instead of corrupting resolution.
#[test]
fn library_snapshot_replays_and_rejects_garbage() {
    let lib_units = vec![
        (
            "MiniLib.kerml".to_string(),
            "standard library package MiniLib { class Thing; class Widget specializes Thing; }"
                .to_string(),
        ),
        (
            "MiniLib2.kerml".to_string(),
            "standard library package MiniLib2 { class Gadget specializes MiniLib::Widget; }"
                .to_string(),
        ),
    ];
    // Record the snapshot the way gen-stdlib-bundle does: same units,
    // same order, recording armed before the build.
    let mut model = sysmlv2_model::model::Model::new();
    for (name, src) in &lib_units {
        model.add_library_source(name.clone(), src);
    }
    model.record_library_cache();
    let _ = sysmlv2_model::json::ResolvedModel::build(&model);
    let snapshot = model
        .take_recorded_library_cache()
        .expect("recording armed before the build")
        .to_bytes();

    // Bytes survive the round-trip.
    assert!(sysmlv2_model::libcache::LibraryCache::from_bytes(&snapshot).is_some());
    assert!(
        sysmlv2_model::libcache::LibraryCache::from_bytes(&snapshot[..snapshot.len() - 1])
            .is_none()
    );

    let lib_json = sources(&[
        (
            "MiniLib.kerml",
            "standard library package MiniLib { class Thing; class Widget specializes Thing; }",
        ),
        (
            "MiniLib2.kerml",
            "standard library package MiniLib2 { class Gadget specializes MiniLib::Widget; }",
        ),
    ]);
    let user = sources(&[("uses.sysml", "package Uses { part g : MiniLib2::Gadget; }")]);

    let mut cold = Session::from_sources(&user).unwrap();
    cold.load_library_sources(&lib_json, None).unwrap();
    let mut warm = Session::from_sources(&user).unwrap();
    warm.load_library_sources(&lib_json, Some(snapshot.clone()))
        .unwrap();
    assert_eq!(cold.unresolved_count(), 0);
    assert_eq!(warm.unresolved_count(), 0);
    assert_eq!(
        cold.to_compact_json(),
        warm.to_compact_json(),
        "replayed build diverged from cold build"
    );

    // Garbage and truncated snapshots: rejected, cold-build fallback.
    let mut junk = Session::from_sources(&user).unwrap();
    junk.load_library_sources(&lib_json, Some(vec![0xde, 0xad, 0xbe, 0xef]))
        .unwrap();
    assert_eq!(cold.to_compact_json(), junk.to_compact_json());

    // A snapshot recorded against DIFFERENT library content: the
    // fingerprint mismatch disables replay, output stays correct.
    let other = sources(&[(
        "MiniLib.kerml",
        "standard library package MiniLib { class Thing; class Widget; }",
    )]);
    let mut stale = Session::from_sources(&user).unwrap();
    stale.load_library_sources(&other, Some(snapshot)).unwrap();
    // Widget no longer specializes Thing and MiniLib2 is gone entirely —
    // the user typing must now be unresolved, proving no stale replay.
    assert!(stale.unresolved_count() > 0);
}

#[test]
fn edit_batch_renames_and_reports_splices() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let battery = s.resolve("Flashlight::Battery").unwrap();
    let result = s
        .edit(
            &serde_json::json!([
                {"op": "rename", "target": "Flashlight::flashlight::battery", "newName": "powerCell"},
                {"op": "insertMember", "owner": "Flashlight::flashlight", "text": "part case2 : Body;"},
            ])
            .to_string(),
        )
        .expect("edit commits");
    let report: serde_json::Value = serde_json::from_str(&result).unwrap();

    // Splices replay over the pre-edit source to the post-edit source.
    let splices = report["splices"].as_array().unwrap();
    assert!(!splices.is_empty());
    let mut replayed = String::new();
    let mut cursor = 0usize;
    for sp in splices {
        assert_eq!(sp["unit"].as_str().unwrap(), "flashlight.sysml");
        replayed.push_str(&FLASHLIGHT[cursor..offset(&sp["start"])]);
        replayed.push_str(sp["text"].as_str().unwrap());
        cursor = offset(&sp["end"]);
    }
    replayed.push_str(&FLASHLIGHT[cursor..]);
    let post = s.source(0).unwrap();
    assert_eq!(replayed, post);
    assert!(post.contains("part powerCell : Battery;"));
    assert!(post.contains("part case2 : Body;"));
    assert!(!post.contains("part battery"));

    // The rename moved the usage's ownership path: idMap records it.
    assert!(report["idMap"].as_array().is_some_and(|m| !m.is_empty()));

    // The session was rebuilt: pre-edit handles are stale, re-resolving
    // sees the new state.
    assert!(s.metaclass(&battery).is_err());
    assert!(s.resolve("Flashlight::flashlight::powerCell").is_some());
    assert!(s.resolve("Flashlight::flashlight::battery").is_none());
}

#[test]
fn edit_batch_failures_leave_the_session_unchanged() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();

    // Unknown target fails before planning.
    let err = s
        .edit(r#"[{"op": "remove", "target": "Flashlight::Nope"}]"#)
        .unwrap_err();
    assert!(err.contains("element not found"), "{err}");

    // A remove blocked by outside references rolls back.
    let err = s
        .edit(r#"[{"op": "remove", "target": "Flashlight::Battery"}]"#)
        .unwrap_err();
    assert!(!err.is_empty());
    assert_eq!(s.source(0).unwrap(), FLASHLIGHT);
    // Handles minted before the failed batch still work (no rebuild).
    let body = s.resolve("Flashlight::Body").unwrap();
    assert_eq!(s.metaclass(&body).unwrap(), "PartDefinition");

    // Malformed ops are rejected with a parse error.
    let err = s.edit(r#"[{"op": "levitate"}]"#).unwrap_err();
    assert!(err.contains("bad edit ops"), "{err}");
    let err = s.edit("[]").unwrap_err();
    assert!(err.contains("empty edit batch"), "{err}");
}

#[test]
fn edit_batch_moves_members() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    // Reorder: `battery` before `body` (newOwner omitted = same owner).
    let result = s
        .edit(r#"[{"op": "moveMember", "target": "Flashlight::flashlight::battery", "index": 0}]"#)
        .expect("reorder commits");
    let report: serde_json::Value = serde_json::from_str(&result).unwrap();
    let post = s.source(0).unwrap();
    let battery_at = post.find("part battery : Battery;").unwrap();
    let body_at = post.find("part body : Body;").unwrap();
    assert!(battery_at < body_at, "not reordered:\n{post}");
    // Named members chain past their membership's ordinal (IDS.md,
    // id scheme 1): reordering named siblings moves no ids, so
    // the report's id map is empty and host selections survive as-is.
    assert!(
        report["idMap"].as_array().is_some_and(|m| m.is_empty()),
        "{report}"
    );

    // Re-parent: move `Body` (referenced) into the flashlight part —
    // `part body : Body;` still resolves it in the enclosing scope.
    s.edit(r#"[{"op": "moveMember", "target": "Flashlight::Body", "newOwner": "Flashlight::flashlight"}]"#)
        .expect("in-scope re-parent commits");
    assert!(s.resolve("Flashlight::flashlight::Body").is_some());
}

#[test]
fn edit_batch_sets_feature_types_and_grows_typed_values() {
    const SRC: &str = "package Lamp {\n    attribute def Volt;\n    attribute def Watt;\n    part def Bulb {\n        attribute watts : Watt;\n        attribute rating : Volt = 3;\n        attribute spare;\n    }\n}\n";
    let mut s = Session::from_sources(&sources(&[("lamp.sysml", SRC)])).unwrap();
    s.edit(
        &serde_json::json!([
            // The diagram editor's original defect: add a value to a
            // TYPED value-less feature.
            {"op": "setFeatureValue", "target": "Lamp::Bulb::watts", "expr": "60"},
            // Change a declared type in place; add one where none is.
            {"op": "setFeatureType", "target": "Lamp::Bulb::rating", "type": "Watt"},
            {"op": "setFeatureType", "target": "Lamp::Bulb::spare", "type": "Volt"},
        ])
        .to_string(),
    )
    .expect("edit commits");
    let post = s.source(0).unwrap();
    assert!(post.contains("attribute watts : Watt = 60;"), "{post}");
    assert!(post.contains("attribute rating : Watt = 3;"), "{post}");
    assert!(post.contains("attribute spare : Volt;"), "{post}");
}

#[test]
fn check_edit_dry_runs_without_touching_the_session() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let battery = s.resolve("Flashlight::Battery").unwrap();

    // Would commit: full report, session untouched, handles stay valid.
    let ops = r#"[{"op": "insertMember", "owner": "Flashlight::flashlight", "text": "part case2 : Body;"}]"#;
    let v: serde_json::Value = serde_json::from_str(&s.check_edit(ops).unwrap()).unwrap();
    assert_eq!(v["wouldCommit"], serde_json::json!(true));
    assert!(!v["splices"].as_array().unwrap().is_empty());
    assert_eq!(s.source(0).unwrap(), FLASHLIGHT);
    assert_eq!(s.metaclass(&battery).unwrap(), "PartDefinition");

    // The real edit produces the splices the check predicted.
    let committed: serde_json::Value = serde_json::from_str(&s.edit(ops).unwrap()).unwrap();
    assert_eq!(committed["splices"], v["splices"]);

    // Would refuse: the exact engine refusal, still no state change.
    let before = s.source(0).unwrap();
    let v: serde_json::Value = serde_json::from_str(
        &s.check_edit(r#"[{"op": "remove", "target": "Flashlight::Battery"}]"#)
            .unwrap(),
    )
    .unwrap();
    assert_eq!(v["wouldCommit"], serde_json::json!(false));
    assert!(v["refusal"].as_str().is_some_and(|r| !r.is_empty()));
    assert_eq!(s.source(0).unwrap(), before);

    // An unresolvable op target is a refusal too (the drag cue treats
    // it as a forbidden drop), not a transport error.
    let v: serde_json::Value = serde_json::from_str(
        &s.check_edit(r#"[{"op": "remove", "target": "Flashlight::Nope"}]"#)
            .unwrap(),
    )
    .unwrap();
    assert_eq!(v["wouldCommit"], serde_json::json!(false));
    assert!(v["refusal"].as_str().unwrap().contains("element not found"));

    // Malformed ops JSON is still an error.
    assert!(s.check_edit(r#"[{"op": "levitate"}]"#).is_err());
    assert!(s.check_edit("[]").is_err());
}

#[test]
fn to_graph_emits_identity_nodes() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let g: serde_json::Value = serde_json::from_str(&s.to_graph(None).unwrap()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    assert!(
        nodes
            .iter()
            .any(|n| n["label"] == "Battery" && n["file"] == "flashlight.sysml")
    );
    assert!(g["edges"].as_array().is_some_and(|e| !e.is_empty()));
    assert!(s.to_graph(Some(r#"{"view":"sequence"}"#.into())).is_err());
}

#[test]
fn edit_removes_anonymous_connector_by_graph_edge_id() {
    const SRC: &str =
        "package Rig {\n    part pump;\n    part tank;\n    connect pump to tank;\n}\n";
    let mut s = Session::from_sources(&sources(&[("rig.sysml", SRC)])).unwrap();
    let g: serde_json::Value = serde_json::from_str(
        &s.to_graph(Some(r#"{"view":"interconnection"}"#.into()))
            .unwrap(),
    )
    .unwrap();
    let edge = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["kind"] == "connect")
        .expect("connect edge");
    assert!(edge["qname"].is_null(), "anonymous connector");
    let target = format!("@{}", edge["id"].as_str().unwrap());
    s.edit(&serde_json::json!([{ "op": "remove", "target": target }]).to_string())
        .expect("remove by id commits");
    let post = s.source(0).unwrap();
    assert!(!post.contains("connect pump to tank;"), "{post}");
    assert!(post.contains("part pump;") && post.contains("part tank;"));
}

#[test]
fn edits_reject_library_elements_and_member_source_round_trips() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    s.load_library_sources(
        &sources(&[("lib.sysml", "package Lib { part def L; }")]),
        None,
    )
    .unwrap();

    // Library elements are read-only for every edit path.
    let err = s
        .edit(r#"[{"op": "rename", "target": "Lib::L", "newName": "M"}]"#)
        .unwrap_err();
    assert!(err.contains("read-only"), "{err}");
    let err = s.member_source("Lib::L").unwrap_err();
    assert!(err.contains("read-only"), "{err}");

    // Copy: the member's exact declaration text, body included…
    let text = s.member_source("Flashlight::Battery").unwrap();
    assert!(text.starts_with("part def Battery {"), "{text}");
    assert!(
        text.contains("attribute voltage = 3;") && text.ends_with('}'),
        "{text}"
    );

    // …pastes through insertMember (multi-line member text).
    s.edit(
        &serde_json::json!([{ "op": "insertMember", "owner": "Flashlight::flashlight",
            "text": text.replace("Battery", "SpareBattery") }])
        .to_string(),
    )
    .expect("paste commits");
    assert!(s.resolve("Flashlight::flashlight::SpareBattery").is_some());
}

#[test]
fn value_source_reports_the_bound_expression() {
    let mut s = Session::from_sources(&sources(&[(
        "m.sysml",
        "package M {\n    enum def Kind { low; high; }\n    part def P {\n        attribute k : Kind = Kind::high;\n        attribute v = 3 + 4;\n        attribute bare : Kind;\n    }\n}\n",
    )]))
    .unwrap();
    let v = s.resolve("M::P::v").unwrap();
    assert_eq!(s.value_source(&v).unwrap().as_deref(), Some("3 + 4"));
    let k = s.resolve("M::P::k").unwrap();
    assert_eq!(s.value_source(&k).unwrap().as_deref(), Some("Kind::high"));
    // No value part → no prefill (and no error).
    let bare = s.resolve("M::P::bare").unwrap();
    assert_eq!(s.value_source(&bare).unwrap(), None);
    // The evaluated value of a literal reference is the literal element
    // itself — how a value editor learns the current enum choice.
    let val: serde_json::Value = serde_json::from_str(&s.evaluate(&k).unwrap()).unwrap();
    let high = s.resolve("M::Kind::high").unwrap();
    assert_eq!(
        val["@element"],
        serde_json::json!(s.element_id(&high).unwrap())
    );
    // Declaration sites report unit + byte span — the name span the
    // rename op splices at, so a caller can place a cursor exactly on
    // the declared name.
    let site: serde_json::Value =
        serde_json::from_str(&s.declaration_site(&v).unwrap().expect("v has a site")).unwrap();
    let unit = offset(&site["unit"]);
    let src = s.source(unit).unwrap();
    let text = &src[offset(&site["start"])..offset(&site["end"])];
    assert_eq!(text, "v");
}

#[test]
fn verify_reports_verdicts_and_narrowed_ranges() {
    // One undecided constraint that propagation narrows, one violated
    // outright, one violated through a bound feature (bindings carry
    // the "why") — the solverless `verify --ranges` pipeline.
    let src = "package P {\n\
               \x20   attribute def Real;\n\
               \x20   attribute wingSpan : Real;\n\
               \x20   attribute margin : Real = 1;\n\
               \x20   assert constraint span { wingSpan >= 10 }\n\
               \x20   assert constraint bad { 1 > 2 }\n\
               \x20   assert constraint short { margin >= 2 }\n\
               }\n";
    let mut s = Session::from_sources(&sources(&[("t.sysml", src)])).unwrap();
    let report: serde_json::Value = serde_json::from_str(&s.verify(None).unwrap()).unwrap();

    let constraints = report["constraints"].as_array().unwrap();
    assert_eq!(constraints.len(), 3);
    let by_name = |n: &str| {
        constraints
            .iter()
            .find(|c| c["name"] == n)
            .unwrap_or_else(|| panic!("no constraint `{n}`"))
    };
    // Asserted ⇒ the constraint narrows the domain and then holds for
    // every value in it: propagation upgrades undecided → satisfied.
    let span = by_name("span");
    assert_eq!(span["status"], "satisfied");
    assert_eq!(span["method"], "propagation");
    assert!(
        span["detail"].as_str().unwrap().contains("propagation"),
        "{}",
        span["detail"]
    );
    assert_eq!(span["unitName"], "t.sysml");
    assert_eq!(span["elementType"], "AssertConstraintUsage");
    assert_eq!(span["line"], 5); // the result expression's line
    assert_eq!(span["features"], serde_json::json!(["wingSpan"]));
    let bad = by_name("bad");
    assert_eq!(bad["status"], "violated");
    assert_eq!(bad["method"], "evaluation");
    assert_eq!(bad["detail"], "VIOLATED"); // no references, no suffix

    // A violated constraint over a bound feature explains itself: the
    // detail carries the CLI's `(with …)` suffix and the bindings carry
    // the value plus the declaration position of `margin` (line 4).
    let short = by_name("short");
    assert_eq!(short["status"], "violated");
    assert_eq!(short["detail"], "VIOLATED (with margin = 1)");
    let b = &short["bindings"].as_array().unwrap()[0];
    assert_eq!(b["feature"], "margin");
    assert_eq!(b["value"], "1");
    assert_eq!(b["unitName"], "t.sysml");
    assert_eq!(b["line"], 4);

    let ranges = report["ranges"].as_array().unwrap();
    let ws = ranges
        .iter()
        .find(|r| r["feature"] == "wingSpan")
        .expect("wingSpan range");
    assert_eq!(ws["range"], "[10, +∞]");
    assert_eq!(ws["narrowed"], true);

    assert_eq!(report["summary"]["violated"], 2);
    assert_eq!(report["summary"]["satisfied"], 1);

    // Options plumb through; unknown keys are rejected.
    assert!(s.verify(Some(r#"{"maxIters": 5}"#.into())).is_ok());
    assert!(s.verify(Some(r#"{"nope": 1}"#.into())).is_err());
}

#[test]
fn lint_reports_configurable_findings_with_positions_and_fixes() {
    // A dead calc input (unused-parameter, default warn, deleting fix)
    // and a snake_case definition (naming-convention, default warn) —
    // the lint surface over the engine.
    let src = "package P {\n\
               \x20   attribute def Real;\n\
               \x20   part def dead_wheel;\n\
               \x20   calc def T { in force : Real; in radius : Real; return t : Real = force * 2; }\n\
               }\n";
    let mut s = Session::from_sources(&sources(&[("t.sysml", src)])).unwrap();
    // A config-less lint carries only the default-on nudges: the
    // snake_case definition at naming-convention's info default.
    let quiet: serde_json::Value = serde_json::from_str(&s.lint(None).unwrap()).unwrap();
    let quiet_findings = quiet["findings"].as_array().unwrap();
    assert_eq!(quiet_findings.len(), 1, "{quiet}");
    assert_eq!(quiet_findings[0]["rule"], "naming-convention");
    assert_eq!(quiet_findings[0]["severity"], "info");
    let on = r#"{ "rules": { "naming-convention": "warn", "unused-parameter": "warn" } }"#;
    let report: serde_json::Value =
        serde_json::from_str(&s.lint(Some(on.into())).unwrap()).unwrap();
    let findings = report["findings"].as_array().unwrap();
    assert_eq!(findings.len(), 2, "{findings:?}");
    let naming = &findings[0];
    assert_eq!(naming["rule"], "naming-convention");
    assert_eq!(naming["severity"], "warn");
    assert_eq!(naming["unitName"], "t.sysml");
    assert_eq!(naming["line"], 3);
    assert!(naming["message"].as_str().unwrap().contains("`dead_wheel`"));
    // The quick-fix hooks: edit-target spelling + style suggestion.
    assert_eq!(naming["element"], "P::dead_wheel");
    assert_eq!(naming["suggest"], "DeadWheel");
    let unused = &findings[1];
    assert_eq!(unused["rule"], "unused-parameter");
    assert_eq!(unused["line"], 4);
    let fix = &unused["fix"];
    assert_eq!(fix["deletes"], true);
    let edit = &fix["edits"].as_array().unwrap()[0];
    let unit = offset(&edit["unit"]);
    let cut = &s.source(unit).unwrap()[offset(&edit["start"])..offset(&edit["end"])];
    assert_eq!(cut, "in radius : Real;");
    assert_eq!(report["summary"]["warnings"], 2);
    assert_eq!(report["summary"]["errors"], 0);
    assert_eq!(report["summary"]["infos"], 0);
    assert_eq!(report["summary"]["hints"], 0);

    // The full severity ladder surfaces: info and hint levels parse
    // and tally into their own buckets.
    let soft = r#"{ "rules": { "naming-convention": "hint", "unused-parameter": "info" } }"#;
    let soft: serde_json::Value =
        serde_json::from_str(&s.lint(Some(soft.into())).unwrap()).unwrap();
    assert_eq!(soft["summary"]["hints"], 1, "{soft}");
    assert_eq!(soft["summary"]["infos"], 1);
    assert_eq!(soft["findings"][0]["severity"], "hint");
    assert_eq!(soft["findings"][1]["severity"], "info");

    // Config plumbs through: silence one rule, escalate the other;
    // unknown ids surface as lint-config findings with null positions.
    let cfg = r#"{ "rules": {
        "naming-convention": "off",
        "unused-parameter": "error",
        "no-such-rule": "warn" } }"#;
    let report: serde_json::Value =
        serde_json::from_str(&s.lint(Some(cfg.into())).unwrap()).unwrap();
    let findings = report["findings"].as_array().unwrap();
    assert_eq!(findings.len(), 2, "{findings:?}");
    assert_eq!(findings[0]["rule"], "lint-config");
    assert!(findings[0]["unit"].is_null() && findings[0]["line"].is_null());
    assert_eq!(findings[1]["rule"], "unused-parameter");
    assert_eq!(findings[1]["severity"], "error");
    assert_eq!(report["summary"]["errors"], 1);

    // Unreadable JSON is the only error.
    assert!(s.lint(Some("{nope".into())).is_err());

    // The rule inventory serves configuration UIs from the engine's
    // own registry: severities, scopes, styles, families, and typed
    // rule options.
    let rules: serde_json::Value = serde_json::from_str(&sysmlv2_wasm::lint_rules()).unwrap();
    let rules = rules.as_array().unwrap();
    assert!(rules.len() >= 5);
    let chain = rules
        .iter()
        .find(|r| r["id"] == "multiline-conditions")
        .unwrap();
    let min = &chain["options"][0];
    assert_eq!(min["key"], "min");
    assert_eq!(min["kind"], "int");
    assert_eq!(min["default"], 3);
    assert_eq!(min["min"], 2);
    assert!(min["zero"].as_str().unwrap().contains("inline"));
    let style = rules.iter().find(|r| r["id"] == "unit-spelling").unwrap()["options"][0].clone();
    assert_eq!(style["kind"], "choice");
    assert!(
        style["values"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v == "expression")
    );
    let naming = rules
        .iter()
        .find(|r| r["id"] == "naming-convention")
        .unwrap();
    assert_eq!(naming["default"], "info");
    assert!(!naming["description"].as_str().unwrap().is_empty());
    assert!(
        naming["styles"]
            .as_array()
            .unwrap()
            .iter()
            .any(|s| s == "snake_case")
    );
    let fam = naming["families"].as_array().unwrap();
    assert_eq!(fam[0]["key"], "definitions");
    assert_eq!(fam[0]["defaultStyle"], "PascalCase");
    assert!(
        naming["scopes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|s| s["key"] == "EnumerationUsage")
    );
    let untyped = rules.iter().find(|r| r["id"] == "untyped-usage").unwrap();
    let transition = untyped["scopes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["key"] == "TransitionUsage")
        .expect("transition scope advertised")
        .clone();
    assert_eq!(transition["default"], "off");
    assert_eq!(transition["label"], "transition");
    let param = rules
        .iter()
        .find(|r| r["id"] == "unused-parameter")
        .unwrap();
    assert_eq!(param["scopes"].as_array().unwrap().len(), 3);
    assert!(param["styles"].as_array().unwrap().is_empty());
    // The textual tier's rule advertises its two typed options.
    let indent = rules.iter().find(|r| r["id"] == "indentation").unwrap();
    assert_eq!(indent["default"], "off");
    let opts = indent["options"].as_array().unwrap();
    assert_eq!(opts[0]["key"], "style");
    assert_eq!(opts[0]["kind"], "choice");
    assert_eq!(opts[0]["default"], "tabs");
    assert_eq!(opts[1]["key"], "size");
    assert_eq!(opts[1]["default"], 4);
    assert!(indent["scopes"].as_array().unwrap().is_empty());

    // …and it reaches this surface with the session's own text: the
    // four-space source above is off the tabs default on every indented
    // line, each with a re-indent fix over the leading whitespace.
    let tabs = r#"{ "rules": { "indentation": "warn", "naming-convention": "off" } }"#;
    let report: serde_json::Value =
        serde_json::from_str(&s.lint(Some(tabs.into())).unwrap()).unwrap();
    let findings = report["findings"].as_array().unwrap();
    assert_eq!(findings.len(), 3, "{findings:?}");
    assert_eq!(findings[0]["rule"], "indentation");
    assert_eq!(findings[0]["line"], 2);
    assert_eq!(findings[0]["col"], 1);
    assert_eq!(findings[0]["endCol"], 5);
    assert!(findings[0]["element"].is_null());
    let edit = &findings[0]["fix"]["edits"].as_array().unwrap()[0];
    assert_eq!(edit["replacement"], "\t");
    assert_eq!(findings[0]["fix"]["deletes"], false);

    // The style option flips the whole judgment: spaces of that width
    // are then the conforming form and this source is silent.
    let spaces = r#"{ "rules": { "naming-convention": "off",
                     "indentation": { "severity": "warn", "style": "spaces",
                     "size": 4 } } }"#;
    let report: serde_json::Value =
        serde_json::from_str(&s.lint(Some(spaces.into())).unwrap()).unwrap();
    assert_eq!(report["findings"].as_array().unwrap().len(), 0, "{report}");
}

#[test]
fn delta_between_rebases_independent_derivations() {
    use sysmlv2_wasm::{delta_cbor_between, describe_cbor};
    // The same text built under two unit names assigns ids from two
    // different unit-root seeds — a raw diff sees full churn, the
    // rebased diff sees the empty delta.
    let a = Session::from_sources(&sources(&[("a.sysml", FLASHLIGHT)])).unwrap();
    let b = Session::from_sources(&sources(&[("b.sysml", FLASHLIGHT)])).unwrap();
    let base = a.to_compact_json();
    let target = b.to_compact_json();

    let rebased = delta_cbor_between(&base, &target, false, true, None, None).unwrap();
    let d: serde_json::Value = serde_json::from_str(&describe_cbor(&rebased).unwrap()).unwrap();
    assert_eq!(d["delta"]["changes"]["creates"], 0, "rebased: no creates");
    assert_eq!(d["delta"]["changes"]["updates"], 0, "rebased: no updates");
    assert_eq!(d["delta"]["changes"]["deletes"], 0, "rebased: no deletes");

    let raw = delta_cbor_between(&base, &target, false, false, None, None).unwrap();
    let dr: serde_json::Value = serde_json::from_str(&describe_cbor(&raw).unwrap()).unwrap();
    assert!(
        dr["delta"]["changes"]["creates"].as_u64().unwrap() > 0,
        "raw diff of independent derivations churns"
    );

    // Portable mode carries text identities and allows lenient apply.
    let portable = delta_cbor_between(&base, &target, true, true, None, None).unwrap();
    let dp: serde_json::Value = serde_json::from_str(&describe_cbor(&portable).unwrap()).unwrap();
    assert_eq!(dp["delta"]["identityMode"], "portable");
}

#[test]
fn codec_tables_expose_the_wire_vocabulary() {
    use sysmlv2_wasm::codec_tables;
    let t: serde_json::Value = serde_json::from_str(&codec_tables(false)).unwrap();
    assert_eq!(t["tablesVersion"], 1);
    let metaclasses = t["metaclasses"].as_array().unwrap();
    // Position = wire type code; spot-check a known metaclass.
    let fre = metaclasses
        .iter()
        .position(|m| m["name"] == "FeatureReferenceExpression")
        .expect("FeatureReferenceExpression in the table");
    assert!(fre < metaclasses.len());
    let fields = metaclasses[fre]["fields"].as_array().unwrap();
    assert!(fields.iter().any(|f| f["prop"] == "declaredName"));
    // Enum vocabularies ride along.
    assert!(
        t["enums"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["name"] == "VisibilityKind")
    );
    // Full-form space is a superset per metaclass.
    let tf: serde_json::Value = serde_json::from_str(&codec_tables(true)).unwrap();
    assert!(tf["metaclasses"].as_array().unwrap().len() == metaclasses.len());
}

#[test]
fn foreign_payload_base_digests_and_applies_raw() {
    use sysmlv2_wasm::{delta_cbor_between, describe_cbor, state_digest_of};
    // A payload produced elsewhere: a session under its own unit name,
    // exported to compact JSON. The receiving session loads it keeping
    // the document's ids (explicit ids), so the loaded session *is* the
    // file's identity: its state digest equals the raw digest, and a
    // strict delta recorded against the file applies to the session as
    // well as to the caller-held base document.
    let producer = Session::from_sources(&sources(&[("v1.sysml", FLASHLIGHT)])).unwrap();
    let base_json = producer.to_compact_json();
    let target = Session::from_sources(&sources(&[(
        "v1.sysml",
        "package Flashlight {\n    part def Body;\n    part def Battery {\n        attribute voltage = 3;\n    }\n    part def Bulb;\n    part flashlight {\n        part body : Body;\n        part battery : Battery;\n    }\n}\n",
    )]))
    .unwrap();
    let delta = delta_cbor_between(
        &base_json,
        &target.to_compact_json(),
        false,
        true,
        None,
        None,
    )
    .unwrap();
    let d: serde_json::Value = serde_json::from_str(&describe_cbor(&delta).unwrap()).unwrap();
    let base_digest = d["delta"]["baseDigest"].as_str().unwrap();

    // Raw digest of the payload document = the delta's base digest = the
    // loaded session's digest.
    assert_eq!(state_digest_of(&base_json).unwrap(), base_digest);
    let receiver = Session::from_interchange_json(&base_json, None, None, None).unwrap();
    assert_eq!(
        receiver.state_digest(),
        base_digest,
        "a loaded payload keeps its ids, so the session is the file's identity"
    );

    // Strict apply: clean against the receiver's loaded model and
    // against the caller-held base document alike.
    let against_session: serde_json::Value =
        serde_json::from_str(&receiver.apply_delta_cbor(&delta, false).unwrap()).unwrap();
    assert_eq!(against_session["report"]["baseMatched"], true);
    let applied: serde_json::Value = serde_json::from_str(
        &receiver
            .apply_delta_cbor_to(&delta, &base_json, false)
            .unwrap(),
    )
    .unwrap();
    assert_eq!(applied["report"]["baseMatched"], true);
    assert_eq!(
        state_digest_of(&applied["result"].to_string()).unwrap(),
        d["delta"]["resultDigest"].as_str().unwrap(),
        "applying to the raw base reproduces the declared result state"
    );
}

/// The raw-result apply surface: replay chains must carry state
/// documents as emitted strings — a host JSON parser re-canonicalizes
/// number spellings (`3.0` → `3`), silently changing the compact-CBOR
/// encoding and the state digest. `applyDeltaCborToRaw` returns the
/// applied document as a string field so the host never parses it.
#[test]
fn raw_apply_result_is_digest_faithful() {
    use sysmlv2_wasm::{delta_cbor_between, describe_cbor, state_digest_of};
    let float_model = "package P {\n    part def D {\n        attribute mass = 3.0;\n    }\n}\n";
    let base = Session::from_sources(&sources(&[("m.sysml", float_model)])).unwrap();
    let base_json = base.to_compact_json();
    let target = Session::from_sources(&sources(&[(
        "m.sysml",
        "package P {\n    part def D {\n        attribute mass = 3.0;\n        attribute count;\n    }\n}\n",
    )]))
    .unwrap();
    let delta = delta_cbor_between(
        &base_json,
        &target.to_compact_json(),
        false,
        true,
        None,
        None,
    )
    .unwrap();
    let d: serde_json::Value = serde_json::from_str(&describe_cbor(&delta).unwrap()).unwrap();

    let raw = base
        .apply_delta_cbor_to_raw(&delta, &base_json, false)
        .unwrap();
    let wrapper: serde_json::Value = serde_json::from_str(&raw).unwrap();
    let result_json = wrapper["resultJson"].as_str().unwrap();
    assert_eq!(
        state_digest_of(result_json).unwrap(),
        d["delta"]["resultDigest"].as_str().unwrap(),
        "the string result digests to the declared result state"
    );
    assert!(wrapper["report"]["baseMatched"].as_bool().unwrap());
    // The hazard is real: the float spelling survives in the string
    // (a value round trip through a normalizing parser would not).
    assert!(
        result_json.contains("3.0"),
        "float spelling preserved verbatim"
    );
}

/// `formatQuery` — the `.kq` document formatter: fits stay inline,
/// long chains wrap, broken input is refused with its diagnostic.
#[test]
fn format_query_wraps_long_chains() {
    use sysmlv2_wasm::format_query;
    assert_eq!(format_query("a.b + 1", None, None).unwrap(), "a.b + 1");

    let long = "ownedFeature(Pkg::Program)->select { in p; p @ SysML::PartUsage }\
                ->collect { in m; (m meta SysML::PartUsage).declaredName }\
                ->reject { in n; n == \"skip\" }";
    let out = format_query(long, None, None).unwrap();
    assert!(out.contains("\n    ->select"), "chain wrapped:\n{out}");
    assert_eq!(format_query(&out, None, None).unwrap(), out, "idempotent");

    // An explicit narrow width wraps more; tabs indent with tabs.
    let tabbed = format_query(long, Some("tabs".into()), Some(40)).unwrap();
    assert!(tabbed.contains("\n\t->select"), "tab indent:\n{tabbed}");

    assert!(format_query("a +", None, None).is_err());
    assert!(format_query("part def X;", None, None).is_err());
}

/// `formatSource` — canonical model-text formatting under a project's
/// lint configuration: defaults format with tabs, the `indentation`
/// rule's style/size options carry through, output is idempotent, and
/// broken input is refused with a positioned message.
#[test]
fn format_source_follows_lint_config() {
    use sysmlv2_wasm::format_source_js;

    let messy =
        "package  P {\n      requirement <'REQ-1'>   illuminate   {\n   doc /* shine */\n }\n}";
    let out = format_source_js(messy, None).unwrap();
    assert!(
        out.contains("\n\trequirement <'REQ-1'> illuminate {"),
        "tab-indented canonical head:\n{out}"
    );
    assert_eq!(
        format_source_js(&out, None).unwrap(),
        out,
        "idempotent under defaults"
    );

    // Project style: two-space indentation via the indentation rule.
    let spaces =
        r#"{"rules": {"indentation": {"severity": "warn", "style": "spaces", "size": 2}}}"#;
    let spaced = format_source_js(messy, Some(spaces.into())).unwrap();
    assert!(
        spaced.contains("\n  requirement <'REQ-1'> illuminate {"),
        "two-space indent from config:\n{spaced}"
    );
    assert_eq!(
        format_source_js(&spaced, Some(spaces.into())).unwrap(),
        spaced,
        "idempotent under config"
    );

    // Broken input: refused with a 1-based line:col prefix.
    let err = format_source_js("part def {", None).unwrap_err();
    assert!(err.starts_with("1:"), "positioned refusal, got: {err}");
}

/// The canonical-name surface a generator relies on: reserved words
/// and non-basic names quote, basic names stay bare,
/// the dialect selects the reserved set, and the empty string is refused
/// — all without the caller seeing a keyword table.
#[test]
fn canonical_name_spells_like_the_printer() {
    let spell = |n: &str, d: Option<&str>| -> (String, bool) {
        let v: serde_json::Value =
            serde_json::from_str(&canonical_name_js(n, d.map(String::from)).unwrap()).unwrap();
        (
            v["spelling"].as_str().unwrap().to_string(),
            v["quoted"].as_bool().unwrap(),
        )
    };
    assert_eq!(spell("Node", None), ("Node".into(), false));
    assert_eq!(spell("part", None), ("'part'".into(), true));
    assert_eq!(spell("part", Some("kerml")), ("part".into(), false));
    assert_eq!(
        spell("no-referrer", Some("sysml")),
        ("'no-referrer'".into(), true)
    );
    assert_eq!(spell("it's", None), ("'it\\'s'".into(), true));
    assert!(canonical_name_js("", None).unwrap_err().contains("empty"));
    assert!(
        canonical_name_js("x", Some("cobol".into()))
            .unwrap_err()
            .contains("dialect")
    );
    // The quoted spelling is accepted by the parser as that very name.
    let src = format!("package P {{ part def {}; }}\n", spell("part", None).0);
    let findings = check(&sources(&[("p.sysml", &src)]), None, None).unwrap();
    assert_eq!(findings, "[]");
    let mut s = Session::from_sources(&sources(&[("p.sysml", &src)])).unwrap();
    let e = s
        .resolve("P::part")
        .expect("quoted reserved word resolves by value");
    assert_eq!(s.name(&e).unwrap().as_deref(), Some("part"));
}

/// The generated Web platform library, as committed.
const WEB_LIBRARY: &str = include_str!("../../../local-packages/Web.sysml");
const TEMPLATE_LIBRARY: &str = include_str!("../../../local-packages/Template.sysml");
const SVELTE_LIBRARY: &str = include_str!("../../../local-packages/Svelte.sysml");

/// An imported document stores structural
/// ownership only; the DOM navigation API is constructed from it on
/// query. Order is membership order, `children` is element-only, `Attr`
/// parts feed `attributes` and never the tree, and the parent/sibling
/// views come from the owner's membership.
#[test]
fn dom_navigation_is_constructed_from_ownership() {
    let abox = r#"package View {
    private import Web::HTML::Elements::*;

    part <n1> shell : Div {
        :>> id = "shell";

        part <n1_data_qn> : Web::DOM::Attr {
            :>> localName = "data-qn";
            :>> value = "q";
        }

        part <n2> : Web::DOM::Text {
            :>> data = "lead";
        }

        part <n3> : Main {
            part <n4> : Section;
        }

        part <n5> : Web::DOM::Comment {
            :>> data = "c";
        }

        part <n6> : Span;
    }
}
"#;
    let src = sources(&[("Web.sysml", WEB_LIBRARY), ("view.sysml", abox)]);
    let mut s = Session::from_sources(&src).unwrap();
    let names = |json: String| -> Vec<String> {
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let one = |x: &serde_json::Value| match x {
            serde_json::Value::String(s) => s.clone(),
            _ => x["qualifiedName"]
                .as_str()
                .map(|q| q.rsplit("::").next().unwrap().to_string())
                .unwrap_or_else(|| x.to_string()),
        };
        match v.as_array() {
            Some(items) => items.iter().map(one).collect(),
            None => vec![one(&v)],
        }
    };
    let q = |s: &mut Session, e: &str| names(s.query(e).unwrap());
    assert_eq!(
        q(&mut s, "View::shell.childNodes"),
        ["n2", "n3", "n5", "n6"]
    );
    assert_eq!(q(&mut s, "View::shell.children"), ["n3", "n6"]);
    assert_eq!(q(&mut s, "View::shell.firstChild"), ["n2"]);
    assert_eq!(q(&mut s, "View::shell.lastChild"), ["n6"]);
    assert_eq!(q(&mut s, "View::shell.firstElementChild"), ["n3"]);
    assert_eq!(q(&mut s, "View::shell.lastElementChild"), ["n6"]);
    assert_eq!(q(&mut s, "View::shell.childElementCount"), ["2"]);
    assert_eq!(q(&mut s, "View::shell.attributes"), ["n1_data_qn"]);
    assert_eq!(q(&mut s, "View::shell::n3.parentNode"), ["shell"]);
    assert_eq!(q(&mut s, "View::shell::n3.parentElement"), ["shell"]);
    assert_eq!(q(&mut s, "View::shell::n3.previousSibling"), ["n2"]);
    assert_eq!(q(&mut s, "View::shell::n3.nextSibling"), ["n5"]);
    assert_eq!(
        q(&mut s, "View::shell::n3.previousElementSibling"),
        [] as [String; 0]
    );
    assert_eq!(q(&mut s, "View::shell::n3.nextElementSibling"), ["n6"]);
    assert_eq!(q(&mut s, "View::shell::n3.children"), ["n4"]);
    assert_eq!(
        q(&mut s, "View::shell::n3::n4.childNodes"),
        [] as [String; 0]
    );
    assert_eq!(
        q(&mut s, "View::shell::n3::n4.parentNode.parentNode"),
        ["shell"]
    );
    // A package-level node has no DOM parent; an Attr is never a child.
    assert_eq!(q(&mut s, "View::shell.parentNode"), [] as [String; 0]);
    assert_eq!(
        q(&mut s, "View::shell::n1_data_qn.parentNode"),
        [] as [String; 0]
    );
    // Nested chains compose with the constructed views.
    assert_eq!(
        q(&mut s, "View::shell.children.localName"),
        ["main", "span"]
    );
    assert_eq!(q(&mut s, "View::shell.firstChild.data"), ["lead"]);
}

/// Template nodes: block slots and a component's `props` are transparent
/// to the constructed views, a template
/// element's redefined `attributes` view is constructed like the DOM
/// one, and a node's parent is the block owning the slot it sits in.
#[test]
fn dom_navigation_projects_through_template_slots() {
    let abox = r#"package View {
    private import Svelte::*;
    private import Web::HTML::Elements::*;

    part <r> root : Root {
        part <r_env> :>> environment : Environment {
            :>> implementation = "svelte";
        }

        part <e1> : EachBlock {
            attribute :>> expression : TypeScript = "items";

            part <e1_body> :>> body {
                part <h> heading : RegularElement, H3 {
                    :>> id = "heading";

                    part <h_t> : ExpressionTag {
                        attribute :>> expression : TypeScript = "name";
                    }
                }

                part <s> : RegularElement, Section {
                    part <s_id> : Attribute {
                        :>> localName = "id";

                        part <s_id_e> : ExpressionTag {
                            attribute :>> expression : TypeScript = "item.id";
                        }
                    }

                    part <s_p> : RegularElement, P;
                }
            }

            part <e1_fb> :>> fallback {
                part <fb_p> : RegularElement, P;
            }
        }

        part <c> : Component {
            :>> name = "Card";

            part <c_props> :>> props {
                part <c_title> : Attribute {
                    :>> localName = "title";
                    :>> value = "T";
                }
            }

            part <c_p> : RegularElement, P;
        }
    }
}
"#;
    let src = sources(&[
        ("Web.sysml", WEB_LIBRARY),
        ("Template.sysml", TEMPLATE_LIBRARY),
        ("Svelte.sysml", SVELTE_LIBRARY),
        ("view.sysml", abox),
    ]);
    let mut s = Session::from_sources(&src).unwrap();
    let names = |json: String| -> Vec<String> {
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        let one = |x: &serde_json::Value| match x {
            serde_json::Value::String(s) => s.clone(),
            _ => x["qualifiedName"]
                .as_str()
                .map(|q| q.rsplit("::").next().unwrap().to_string())
                .unwrap_or_else(|| x.to_string()),
        };
        match v.as_array() {
            Some(items) => items.iter().map(one).collect(),
            None => vec![one(&v)],
        }
    };
    let q = |s: &mut Session, e: &str| names(s.query(e).unwrap());
    // Root: the environment is not a node; the block and component are.
    assert_eq!(q(&mut s, "View::root.childNodes"), ["e1", "c"]);
    // Block traversal flattens body then fallback; the named slots
    // themselves answer with their owned nodes.
    assert_eq!(
        q(&mut s, "View::root.e1.childNodes"),
        ["heading", "s", "fb_p"]
    );
    assert_eq!(q(&mut s, "View::root.e1.firstChild"), ["heading"]);
    assert_eq!(q(&mut s, "View::root.e1.lastChild"), ["fb_p"]);
    assert_eq!(q(&mut s, "View::root.e1.body"), ["heading", "s"]);
    assert_eq!(q(&mut s, "View::root.e1.fallback"), ["fb_p"]);
    // A slot is a fragment: the element-only views live there.
    assert_eq!(
        q(&mut s, "View::root.e1.e1_body.children"),
        ["heading", "s"]
    );
    assert_eq!(q(&mut s, "View::root.e1.e1_body.childElementCount"), ["2"]);
    assert_eq!(
        q(&mut s, "View::root.e1.e1_body.firstElementChild"),
        ["heading"]
    );
    // Parent and siblings see through the slot.
    assert_eq!(q(&mut s, "View::root.e1.e1_body.s.parentNode"), ["e1"]);
    assert_eq!(
        q(&mut s, "View::root.e1.e1_body.s.previousSibling"),
        ["heading"]
    );
    assert_eq!(q(&mut s, "View::root.e1.e1_body.s.nextSibling"), ["fb_p"]);
    assert_eq!(
        q(&mut s, "View::root.e1.e1_body.heading.previousSibling"),
        [] as [String; 0]
    );
    // A template element's attributes view: reified attribute-likes only, never children.
    assert_eq!(q(&mut s, "View::root.e1.e1_body.s.attributes"), ["s_id"]);
    assert_eq!(q(&mut s, "View::root.e1.e1_body.s.childNodes"), ["s_p"]);
    assert_eq!(
        q(&mut s, "View::root.e1.e1_body.s.attributes.localName"),
        ["id"]
    );
    // The gates: ordered traversal, `H3.localName`, the static
    // reflected id, and the dynamic id as an unevaluated typed source.
    assert_eq!(q(&mut s, "View::root.e1.e1_body.heading.localName"), ["h3"]);
    assert_eq!(q(&mut s, "View::root.e1.e1_body.heading.id"), ["heading"]);
    assert_eq!(
        q(
            &mut s,
            "View::root.e1.e1_body.s.attributes.s_id_e.expression"
        ),
        ["item.id"]
    );
    let expr = s
        .resolve("View::root::e1::e1_body::s::s_id::s_id_e")
        .unwrap();
    let members = s.members(&expr).unwrap();
    let mut typed = None;
    for m in members {
        let typings = s.typings(&m).unwrap();
        let mut is_ts = false;
        for t in &typings {
            if s.qualified_name(t).unwrap().as_deref() == Some("Svelte::TypeScript") {
                is_ts = true;
            }
        }
        if is_ts {
            typed = Some(m);
        }
    }
    let tag_expr = typed.expect("the expression attribute is typed Svelte::TypeScript");
    assert_eq!(s.evaluate(&tag_expr).unwrap(), "\"item.id\"");
    // A component's props slot answers with its attribute-likes, its content is the tree.
    assert_eq!(q(&mut s, "View::root.c.props"), ["c_title"]);
    assert_eq!(q(&mut s, "View::root.c.props.localName"), ["title"]);
    assert_eq!(q(&mut s, "View::root.c.childNodes"), ["c_p"]);
    assert_eq!(
        q(&mut s, "View::root.c.c_props.c_title.parentNode"),
        [] as [String; 0]
    );
}

/// The ambient libraries load with any directory library (interim
/// mechanism) — no file needs naming.
#[test]
fn ambient_libraries_load_with_a_directory_library() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("Tiny.sysml"),
        "library package Tiny { part def T; }\n",
    )
    .unwrap();
    let user = "package M {\n    private import Web::HTML::Elements::*;\n    part d : Div;\n    part t : Template::Text;\n    part k : Svelte::KeyBlock;\n    part y : Tiny::T;\n}\n";
    let mut session =
        sysmlv2_transform::Session::from_sources(vec![("m.sysml".into(), user.into())])
            .unwrap()
            .with_library(&dir)
            .unwrap();
    let r = session.resolved();
    for qn in [
        "Web::DOM::Node",
        "Web::HTML::Elements::Div",
        "Template::Root",
        "Svelte::RegularElement",
        "TransformMeta::Generated",
        "Tiny::T",
    ] {
        assert!(r.resolve_qualified(qn).is_some(), "{qn} resolves ambiently");
    }
    let d = r.resolve_qualified("M::d").unwrap();
    let node = r.resolve_qualified("Web::DOM::Node").unwrap();
    assert!(r.is_library_element(node));
    assert!(!r.is_library_element(d));
    std::fs::remove_dir_all(&dir).ok();
}

/// Semantic mode: a view usage's exposed slice renders
/// through the rendering definition's template; the model is untouched.
#[test]
fn render_view_evaluates_a_template_over_the_exposed_slice() {
    let component = r#"package Listing {
    private import Svelte::*;
    private import Web::HTML::Elements::*;

    rendering def ListingRendering {
        part <r> root : Root {
            part <r_env> :>> environment : Environment {
                :>> implementation = "svelte";
                part <r_inputs> :>> inputs {
                    part <r_in1> : InputBinding {
                        :>> name = "things";
                    }
                }
            }

            part <e1> : EachBlock {
                attribute :>> expression : JavaScript = "things";
                attribute :>> kerml : KerML = "things";
                attribute :>> context : JavaScript = "t";
                attribute :>> kermlContext : KerML = "t = 'item'";

                part <e1_body> :>> body {
                    part <li> : RegularElement, Li {
                        :>> className = "thing";

                        part <li_t> : ExpressionTag {
                            attribute :>> expression : JavaScript = "t.name";
                            attribute :>> kerml : KerML = "declaredName(t)";
                        }
                    }
                }

                part <e1_fb> :>> fallback {
                    part <p> : RegularElement, P {
                        part <p_t> : Text {
                            :>> data = "nothing";
                        }
                    }
                }
            }

            part <input> : RegularElement, Input {
                :>> id = "false";
                :>> title = "true";
                :>> draggable = false;
                :>> disabled = false;
                :>> checked = true;
            }
        }
    }

    view def ListingView {
        rendering 'rendering' : ListingRendering;
        render 'rendering';
    }
}
"#;
    let model = "package Meta {\n    metadata def Hidden;\n}\npackage M {\n    part def A;\n    part def B;\n    part def C;\n}\n";
    // A resolvable filter nothing satisfies exposes an empty slice.
    let site = "package S {\n    private import Listing::*;\n    view every : ListingView {\n        expose M::*;\n    }\n    view none : ListingView {\n        expose M::*;\n        filter @Meta::Hidden;\n    }\n}\n";
    let src = sources(&[
        ("Web.sysml", WEB_LIBRARY),
        ("Template.sysml", TEMPLATE_LIBRARY),
        ("Svelte.sysml", SVELTE_LIBRARY),
        ("listing.sysml", component),
        ("m.sysml", model),
        ("s.sysml", site),
    ]);
    let mut s = Session::from_sources(&src).unwrap();
    let before = s.to_compact_json();
    let html = s.render_view("S::every", Some("html".into())).unwrap();
    assert_eq!(
        html,
        "<li class=\"thing\">A</li><li class=\"thing\">B</li><li class=\"thing\">C</li><input id=\"false\" title=\"true\" draggable=\"false\" checked>"
    );
    let json: serde_json::Value =
        serde_json::from_str(&s.render_view("S::every", None).unwrap()).unwrap();
    assert_eq!(json.as_array().unwrap().len(), 4);
    assert_eq!(json[0]["properties"]["className"], "thing");
    assert_eq!(json[0]["children"][0]["data"], "A");
    assert_eq!(
        s.render_view("S::none", Some("html".into())).unwrap(),
        "<p>nothing</p><input id=\"false\" title=\"true\" draggable=\"false\" checked>"
    );
    assert_eq!(
        s.to_compact_json(),
        before,
        "rendering writes nothing into the model"
    );
    assert!(s.render_view("S::missing", None).is_err());
}

/// A rendering written in plain DOM parts — `Web::HTML::Elements` types,
/// anonymous, no template `Root` — renders like a template: the
/// rendering definition is the root and its element parts are elements.
#[test]
fn render_view_accepts_plain_dom_parts_without_a_template_root() {
    let view = r#"package BrowserViews {
    private import Web::DOM::*;
    private import Web::HTML::Elements::*;

    rendering def SummaryRendering {
        part : Article {
            part : H2 {
                part : Text {
                    :>> data = "Overview";
                }
            }

            part : P {
                :>> className = "lead";
                part : Text {
                    :>> data = "A rendered view.";
                }
            }
        }
    }

    view def SummaryView {
        rendering 'rendering' : SummaryRendering;
        render 'rendering';
    }

    view summary : SummaryView {
        expose M::*;
    }
}
"#;
    let model = "package M {\n    part def A;\n}\n";
    let src = sources(&[
        ("Web.sysml", WEB_LIBRARY),
        ("Template.sysml", TEMPLATE_LIBRARY),
        ("Svelte.sysml", SVELTE_LIBRARY),
        ("views.sysml", view),
        ("m.sysml", model),
    ]);
    let mut s = Session::from_sources(&src).unwrap();
    assert_eq!(
        s.render_view("BrowserViews::summary", Some("html".into()))
            .unwrap(),
        "<article><h2>Overview</h2><p class=\"lead\">A rendered view.</p></article>"
    );
}

#[test]
fn anonymous_graph_elements_are_reachable_by_id() {
    let source = "package P { action a; action b; succession first a then b; constraint { true } }";
    let mut s = Session::from_sources(&sources(&[("anonymous.sysml", source)])).unwrap();
    let graph: serde_json::Value =
        serde_json::from_str(&s.to_graph(Some(r#"{"view":"tree"}"#.into())).unwrap()).unwrap();
    for kind in ["ConstraintUsage", "SuccessionAsUsage"] {
        let node = graph["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .find(|n| n["metaclass"] == kind)
            .unwrap();
        let id = node["id"].as_str().unwrap();
        assert!(node.get("qname").is_none_or(serde_json::Value::is_null));
        assert!(s.resolve(&format!("@{id}")).is_none());
        let e = s.element_by_id(id).expect("graph ID resolves");
        assert_eq!(s.metaclass(&e).unwrap(), kind);
        assert_eq!(s.element_id(&e).unwrap(), id);
        assert_eq!(s.qualified_name(&e).unwrap(), None);
        assert!(s.declaration_site(&e).unwrap().is_some());
        assert!(s.member_source(&format!("@{id}")).is_ok());
    }
    assert_eq!(s.source(0).unwrap(), source);
    for id in [
        "",
        "not-an-id",
        "P::a",
        "00000000-0000-0000-0000-000000000000",
    ] {
        assert!(s.element_by_id(id).is_none());
    }
    let a = s.resolve("P::a").unwrap();
    let id = s.element_id(&a).unwrap();
    let a_by_id = s.element_by_id(&id).unwrap();
    s.edit(r#"[{"op":"rename","target":"P::a","newName":"renamed"}]"#)
        .unwrap();
    assert!(s.metaclass(&a_by_id).is_err());
    assert!(s.element_by_id(&id).is_none());
    let renamed = s.resolve("P::renamed").unwrap();
    let new_id = s.element_id(&renamed).unwrap();
    assert!(s.element_by_id(&new_id).is_some());
}

#[test]
fn id_lookup_preserves_library_read_only_and_handle_generation() {
    let mut s = Session::from_sources(&sources(&[("main.sysml", "package P;")])).unwrap();
    let p = s.resolve("P").unwrap();
    let id = s.element_id(&p).unwrap();
    let old = s.element_by_id(&id).unwrap();
    s.load_library_sources(
        &sources(&[(
            "mini.kerml",
            "standard library package Mini { class Thing; }",
        )]),
        None,
    )
    .unwrap();
    assert!(s.metaclass(&old).is_err());
    assert!(s.element_by_id(&id).is_some());
    let lib = s.resolve("Mini::Thing").unwrap();
    let lib_id = s.element_id(&lib).unwrap();
    let found = s.element_by_id(&lib_id).unwrap();
    assert!(s.is_library_element(&found).unwrap());
    let before = s.units();
    let error = s
        .edit(&serde_json::json!([{"op":"remove","target":format!("@{lib_id}")}]).to_string())
        .unwrap_err();
    assert!(error.contains("read-only"), "{error}");
    assert_eq!(s.units(), before);
}

/// A stand-in for the standard `Views` library package, loaded as a
/// library so that `asElementTable` is a library element — referenced
/// by spelling, never by id, exactly as the shipped library is.
const VIEWS_LIBRARY: &str = "standard library package Views {\n    rendering def Rendering;\n    rendering def TabularRendering :> Rendering;\n    rendering asElementTable : TabularRendering;\n}\n";

/// A matrix-view fixture over [`VIEWS_LIBRARY`]: the generated support
/// package, a model, and two views — one per tabular rendering — plus
/// a non-view.
fn matrix_view_session() -> Session {
    let mut s = Session::from_sources(&matrix_view_sources()).unwrap();
    s.load_library_sources(&sources(&[("Views.sysml", VIEWS_LIBRARY)]), None)
        .unwrap();
    s
}

fn matrix_view_sources() -> String {
    sources(&[
        (
            "matrix.sysml",
            "package MatrixViews {\n    import Views::*;\n    metadata def MatrixConfig {\n        attribute attributes[0..*];\n        attribute relationship[0..1];\n    }\n    rendering def RelationshipMatrix :> TabularRendering;\n    rendering asRelationshipMatrix : RelationshipMatrix;\n}\n",
        ),
        (
            "m.sysml",
            "package M {\n    part def A;\n    part def B;\n    part a : A;\n    part b : B;\n    part c {\n        part d;\n    }\n}\n",
        ),
        (
            "s.sysml",
            "package S {\n    import Views::*;\n    import MatrixViews::*;\n    view 'Part allocations' {\n        @MatrixConfig { relationship = \"allocation\"; }\n        expose M::a;\n        expose M::b;\n        view columns {\n            expose M::c::**;\n        }\n        render asRelationshipMatrix;\n    }\n    view masses {\n        @MatrixConfig { attributes = (\"mass\", \"voltage\"); }\n        expose M::*;\n        render asElementTable;\n    }\n    view nobody;\n    part notAView;\n}\n",
        ),
    ])
}

fn exposed_names(info: &serde_json::Value) -> Vec<&str> {
    info["exposed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| e["qualifiedName"].as_str().unwrap())
        .collect()
}

#[test]
fn view_info_reports_exposure_rendering_and_metadata() {
    let mut s = matrix_view_session();
    let before = s.to_compact_json();
    let info: serde_json::Value =
        serde_json::from_str(&s.view_info("S::'Part allocations'").unwrap()).unwrap();
    assert_eq!(info["qualifiedName"], "S::'Part allocations'");
    assert_eq!(info["rendering"], "asRelationshipMatrix");
    assert_eq!(exposed_names(&info), ["M::a", "M::b"]);
    assert_eq!(info["exposed"][0]["metaclass"], "PartUsage");
    assert!(info["exposed"][0]["id"].as_str().unwrap().len() == 36);
    assert_eq!(info["views"][0]["name"], "columns");
    assert_eq!(
        info["views"][0]["qualifiedName"],
        "S::'Part allocations'::columns"
    );
    assert_eq!(info["metadata"][0]["type"], "MatrixViews::MatrixConfig");
    assert_eq!(info["metadata"][0]["values"]["relationship"], "allocation");
    // The recursive expose names its target and everything under it.
    let columns: serde_json::Value =
        serde_json::from_str(&s.view_info("S::'Part allocations'::columns").unwrap()).unwrap();
    assert_eq!(exposed_names(&columns), ["M::c", "M::c::d"]);
    assert_eq!(columns["rendering"], serde_json::Value::Null);
    assert!(columns["views"].as_array().unwrap().is_empty());
    let masses: serde_json::Value =
        serde_json::from_str(&s.view_info("S::masses").unwrap()).unwrap();
    // The standard rendering is a library element: found by its spelling.
    assert_eq!(masses["rendering"], "asElementTable");
    // The reported name is the model's canonical spelling, whatever the
    // caller quoted.
    assert_eq!(masses["qualifiedName"], "S::masses");
    let quoted: serde_json::Value =
        serde_json::from_str(&s.view_info("S::'masses'").unwrap()).unwrap();
    assert_eq!(quoted["qualifiedName"], "S::masses");
    assert_eq!(quoted["id"], masses["id"]);
    assert_eq!(
        masses["metadata"][0]["values"]["attributes"],
        serde_json::json!(["mass", "voltage"])
    );
    assert_eq!(
        exposed_names(&masses),
        ["M::A", "M::B", "M::a", "M::b", "M::c"]
    );
    assert!(s.view_info("S::notAView").is_err());
    assert!(s.view_info("S::missing").is_err());
    assert_eq!(s.to_compact_json(), before, "reading a view writes nothing");
}

#[test]
fn view_directed_diagrams_show_the_exposure() {
    let mut s = matrix_view_session();
    let graph: serde_json::Value = serde_json::from_str(
        &s.to_graph(Some(
            r#"{"view": "tree", "element": "S::'Part allocations'"}"#.into(),
        ))
        .unwrap(),
    )
    .unwrap();
    let names: Vec<&str> = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| n["qname"].as_str())
        .collect();
    assert!(
        names.contains(&"M::a") && names.contains(&"M::b"),
        "{names:?}"
    );
    assert!(!names.iter().any(|n| n.starts_with("S::")), "{names:?}");
    assert!(!names.contains(&"M::c"), "{names:?}");
    // A non-view element still scopes the diagram to its own subtree.
    let graph: serde_json::Value = serde_json::from_str(
        &s.to_graph(Some(r#"{"view": "tree", "element": "M::c"}"#.into()))
            .unwrap(),
    )
    .unwrap();
    let names: Vec<&str> = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| n["qname"].as_str())
        .collect();
    assert!(
        names.contains(&"M::c") && names.contains(&"M::c::d"),
        "{names:?}"
    );
    let uml = s
        .to_plantuml(Some(r#"{"element": "S::'Part allocations'"}"#.into()))
        .unwrap();
    assert!(uml.starts_with("@startuml"));
    assert!(!uml.contains("Part allocations"), "{uml}");
    // A view exposing nothing draws nothing — never the whole model.
    let graph: serde_json::Value = serde_json::from_str(
        &s.to_graph(Some(r#"{"view": "tree", "element": "S::nobody"}"#.into()))
            .unwrap(),
    )
    .unwrap();
    assert!(graph["nodes"].as_array().unwrap().is_empty(), "{graph}");
    let uml = s
        .to_plantuml(Some(r#"{"element": "S::nobody"}"#.into()))
        .unwrap();
    assert!(!uml.contains("M::a") && !uml.contains("\"a\""), "{uml}");
}

/// A reserved word used as a name: `qualifiedName` keeps the
/// specification's bare spelling, `referenceSpelling` and
/// `spellReference` quote it, and only the quoted form parses when a
/// host splices it into an `expose`.
#[test]
fn reference_spelling_re_parses_in_an_expose() {
    const MODEL: &str =
        "package 'part' {\n    part def 'action';\n    part 'view' : 'action';\n}\n";
    let mut s = Session::from_sources(&sources(&[("m.sysml", MODEL)])).unwrap();
    let view = s.resolve("'part'::'view'").expect("quoted lookup");
    assert_eq!(
        s.qualified_name(&view).unwrap().as_deref(),
        Some("part::view")
    );
    assert_eq!(
        s.reference_spelling(&view).unwrap().as_deref(),
        Some("'part'::'view'")
    );
    assert_eq!(
        spell_reference_js("part::view", None).unwrap(),
        "'part'::'view'"
    );
    // The dialect selects the reserved set: neither word is KerML's.
    assert_eq!(
        spell_reference_js("part::view", Some("kerml".into())).unwrap(),
        "part::view"
    );
    assert_eq!(
        spell_reference_js("'My Views'::x", None).unwrap(),
        "'My Views'::x"
    );
    assert!(
        spell_reference_js("x", Some("cobol".into()))
            .unwrap_err()
            .contains("dialect")
    );
    let expose = |target: &str| -> serde_json::Value {
        let views =
            format!("package Views {{\n    view v {{\n        expose {target};\n    }}\n}}\n");
        let out = check(
            &sources(&[("m.sysml", MODEL), ("v.sysml", &views)]),
            None,
            None,
        )
        .unwrap();
        serde_json::from_str(&out).unwrap()
    };
    assert_eq!(expose("'part'::'view'"), serde_json::json!([]));
    let bare = expose("part::view");
    assert_eq!(bare[0]["severity"], "error", "{bare}");
    assert_eq!(
        bare[0]["stage"], "parse",
        "the bare form fails to parse: {bare}"
    );
}

#[test]
fn derived_properties_by_specification_name() {
    let mut s = Session::from_sources(&sources(&[("flashlight.sysml", FLASHLIGHT)])).unwrap();
    let flashlight = s.resolve("Flashlight::flashlight").unwrap();
    // A composition: element handles, and `{"@id"}` references as JSON.
    let features = s.derived_elements(&flashlight, "ownedFeature").unwrap();
    assert_eq!(features.len(), 2);
    let json: serde_json::Value =
        serde_json::from_str(&s.derived(&flashlight, "ownedFeature").unwrap()).unwrap();
    assert_eq!(json.as_array().unwrap().len(), 2);
    assert_eq!(
        json[0]["@id"].as_str(),
        Some(s.element_id(&features[0]).unwrap().as_str())
    );
    // A string and a null.
    assert_eq!(s.derived(&flashlight, "name").unwrap(), "\"flashlight\"");
    assert_eq!(s.derived(&flashlight, "shortName").unwrap(), "null");
    assert!(s.derived_elements(&flashlight, "name").unwrap().is_empty());
    // A reference-typed property: the typing's target as a handle and as JSON.
    let battery = s.resolve("Flashlight::flashlight::battery").unwrap();
    let types = s.derived_elements(&battery, "type").unwrap();
    assert_eq!(types.len(), 1);
    assert_eq!(
        s.qualified_name(&types[0]).unwrap().as_deref(),
        Some("Flashlight::Battery")
    );
    // Fidelity and the owned side, without a model.
    assert_eq!(Session::derives("PartUsage", "ownedFeature"), "exact");
    assert_eq!(Session::derives("PartUsage", "feature"), "passthrough");
    assert_eq!(Session::derives("PartUsage", "mayTimeVary"), "not-computed");
    assert_eq!(
        Session::derives("PartUsage", "declaredName"),
        "not-declared"
    );
    assert!(Session::is_owned_property("PartUsage", "declaredName"));
    assert!(
        Session::computed_names()
            .iter()
            .any(|n| n == "owningNamespace")
    );
    // A name the metaclass does not derive throws.
    assert!(s.derived(&flashlight, "declaredName").is_err());
    // A name the toolkit does not compute yet throws too.
    assert!(s.derived(&battery, "mayTimeVary").is_err());
    // A target outside the model: in the JSON, not among the handles.
    let mut s = Session::from_sources(&sources(&[(
        "m.sysml",
        "package P { part w : Missing; part def A { part x; } part def B :> A; }",
    )]))
    .unwrap();
    let w = s.resolve("P::w").unwrap();
    let json: serde_json::Value = serde_json::from_str(&s.derived(&w, "type").unwrap()).unwrap();
    assert_eq!(json[0]["outside"], true);
    assert_eq!(json[0]["spelling"], "Missing");
    assert!(json[0]["danglingId"].is_string());
    assert!(s.derived_elements(&w, "type").unwrap().is_empty());
    // The closure policy switches the inheritance-aware families, and
    // survives an edit of the session.
    let b = s.resolve("P::B").unwrap();
    assert_eq!(s.closure_policy(), "passthrough");
    assert!(s.derived_elements(&b, "feature").unwrap().is_empty());
    s.set_closure_policy("closure").unwrap();
    assert_eq!(s.closure_policy(), "closure");
    assert_eq!(s.derived_elements(&b, "feature").unwrap().len(), 1);
    s.edit(r#"[{"op": "moveMember", "target": "P::w", "index": 0}]"#)
        .expect("edit commits");
    assert_eq!(s.closure_policy(), "closure");
    let b = s.resolve("P::B").unwrap();
    assert_eq!(s.derived_elements(&b, "feature").unwrap().len(), 1);
    assert!(s.set_closure_policy("nonsense").is_err());
    s.set_closure_policy("passthrough").unwrap();
}

/// A rename clashing with a sibling's name is dropped from the batch
/// and reported; the rest of the batch (an ancestor-qualified respell
/// included) still commits.
#[test]
fn edit_batch_drops_colliding_renames_and_reports_them() {
    let src = "package 'A B' {\n    part def X;\n    part def x;\n}\npackage Q {\n    part def other_def;\n    part a : 'A B'::X;\n    part b : 'A B'::x;\n}\n";
    let mut s = Session::from_sources(&sources(&[("ab.sysml", src)])).unwrap();
    let result = s
        .edit(
            &serde_json::json!([
                {"op": "rename", "target": "'A B'", "newName": "AB"},
                {"op": "rename", "target": "'A B'::x", "newName": "X"},
                {"op": "rename", "target": "Q::other_def", "newName": "OtherDef"},
            ])
            .to_string(),
        )
        .expect("the batch commits without the clashing rename");
    let report: serde_json::Value = serde_json::from_str(&result).unwrap();
    let findings = report["findings"].as_array().unwrap();
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = findings[0].as_str().unwrap();
    assert!(f.contains("rename of `'A B'::x` to `X` skipped"), "{f}");
    assert!(f.contains("`'A B'::X` is already named `X`"), "{f}");
    let post = s.source(0).unwrap();
    assert!(post.contains("package AB {"), "{post}");
    assert!(post.contains("part def x;"), "{post}");
    assert!(post.contains("part a : AB::X;"), "{post}");
    assert!(post.contains("part b : AB::x;"), "{post}");
    assert!(post.contains("part def OtherDef;"), "{post}");
}

/// A session opened with its library reports the same check findings
/// as the free `check` over the same sources (minus the parse stage,
/// which `checkSyntax` carries) — one resolution instead of two.
#[test]
fn session_check_matches_free_check() {
    use sysmlv2_wasm::check_syntax;
    let lib = sources(&[(
        "MiniLib.kerml",
        "standard library package MiniLib { class Thing; datatype Num; }",
    )]);
    let user = sources(&[
        (
            "dangling.sysml",
            "package Dangling { part def W; part w : Missing; attribute a : W; }",
        ),
        (
            "ctx.sysml",
            "package Ctx { attribute def A { part p : Thing; } }",
        ),
    ]);
    let free: serde_json::Value =
        serde_json::from_str(&check(&user, Some(lib.clone()), None).unwrap()).unwrap();
    let mut s = Session::from_sources_with_library(&user, Some(lib), None).unwrap();
    let unresolved_before = s.unresolved_count();
    let session: serde_json::Value = serde_json::from_str(&s.check()).unwrap();
    assert_eq!(session, free, "session findings match the free check");
    let stages: Vec<&str> = free
        .as_array()
        .unwrap()
        .iter()
        .map(|f| f["stage"].as_str().unwrap())
        .collect();
    assert!(
        stages.contains(&"referential") && stages.contains(&"semantic"),
        "{stages:?}"
    );
    // The syntax stages alone: a parse-broken unit's findings, no model.
    let mixed = sources(&[
        ("bad.sysml", "part def {"),
        (
            "ctx.sysml",
            "package Ctx { attribute def A { part p : Thing; } }",
        ),
    ]);
    let syntax: serde_json::Value = serde_json::from_str(&check_syntax(&mixed).unwrap()).unwrap();
    let stages: Vec<&str> = syntax
        .as_array()
        .unwrap()
        .iter()
        .map(|f| f["stage"].as_str().unwrap())
        .collect();
    assert!(
        stages.iter().all(|s| *s == "parse" || *s == "context"),
        "{stages:?}"
    );
    assert!(stages.contains(&"parse"), "{stages:?}");
    // The session stays usable after checking: navigation and the
    // unresolved count read the same model.
    assert!(s.resolve("Dangling::w").is_some());
    assert!(unresolved_before >= 1);
    assert_eq!(
        s.unresolved_count(),
        unresolved_before,
        "checking drains nothing"
    );
    // Without a library the resolution stages are skipped, as in `check`.
    let mut bare = Session::from_sources(&user).unwrap();
    let bare: serde_json::Value = serde_json::from_str(&bare.check()).unwrap();
    let free_bare: serde_json::Value =
        serde_json::from_str(&check(&user, None, None).unwrap()).unwrap();
    assert_eq!(bare, free_bare);
}

/// Checking a session must not change what lint reports afterwards
/// (the import-visibility rule reads the resolver's import provenance).
#[test]
fn session_check_leaves_lint_findings_unchanged() {
    let lib = sources(&[(
        "MiniLib.kerml",
        "standard library package MiniLib { class Thing; datatype Num; }",
    )]);
    let user = sources(&[(
        "u.sysml",
        "package U { import MiniLib::*; part def W; part w : Thing; attribute n : Num = 3; }",
    )]);
    let rules = |s: &mut Session| -> Vec<String> {
        let v: serde_json::Value = serde_json::from_str(&s.lint(None).unwrap()).unwrap();
        v["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| f["rule"].as_str().unwrap().to_string())
            .collect()
    };
    let mut fresh = Session::from_sources_with_library(&user, Some(lib.clone()), None).unwrap();
    let before = rules(&mut fresh);
    let mut checked = Session::from_sources_with_library(&user, Some(lib), None).unwrap();
    let _ = checked.check();
    let after = rules(&mut checked);
    assert!(
        before.iter().any(|r| r == "import-visibility"),
        "{before:?}"
    );
    assert_eq!(after, before, "lint after check == lint without check");
}

#[test]
fn sources_with_an_empty_unit_name_are_refused_at_the_boundary() {
    let bad = r#"[{"name": "ok.sysml", "text": "package A;"}, {"name": "", "text": "package B;"}]"#;
    let err = Session::from_sources(bad).err().expect("refused");
    assert!(err.contains("source 1 has an empty name"), "{err}");
    assert!(check(bad, None, None).unwrap_err().contains("empty name"));
    assert!(
        sysmlv2_wasm::check_syntax(bad)
            .unwrap_err()
            .contains("empty name")
    );
    assert!(
        sysmlv2_wasm::lenient_sources(bad)
            .unwrap_err()
            .contains("empty name")
    );
    // A library bundle is sources too.
    let err = Session::from_sources_with_library(
        &sources(&[("u.sysml", "package U;")]),
        Some(bad.to_string()),
        None,
    )
    .err()
    .expect("refused");
    assert!(err.contains("empty name"), "{err}");
}

#[test]
fn diagram_emitters_share_one_option_vocabulary() {
    let mut s = Session::from_sources(&sources(&[
        ("flashlight.sysml", FLASHLIGHT),
        ("extra.sysml", "package Extra { part def Case; }"),
    ]))
    .unwrap();
    // Unknown names are unknown on both paths, with the same message…
    let uml = s
        .to_plantuml(Some(r#"{"view": "nope"}"#.into()))
        .unwrap_err();
    assert!(uml.contains("unknown view: nope"), "{uml}");
    assert_eq!(
        s.to_graph(Some(r#"{"view": "nope"}"#.into())).unwrap_err(),
        uml
    );
    let uml = s
        .to_plantuml(Some(r#"{"lineStyle": "curvy"}"#.into()))
        .unwrap_err();
    assert!(uml.contains("unknown line style: curvy"), "{uml}");
    assert_eq!(
        s.to_graph(Some(r#"{"lineStyle": "curvy"}"#.into()))
            .unwrap_err(),
        uml
    );
    let uml = s
        .to_plantuml(Some(r#"{"element": "No::Such"}"#.into()))
        .unwrap_err();
    assert!(uml.contains("element not found: No::Such"), "{uml}");
    assert_eq!(
        s.to_graph(Some(r#"{"element": "No::Such"}"#.into()))
            .unwrap_err(),
        uml
    );
    let uml = s
        .to_plantuml(Some(r#"{"roots": ["No::Such"]}"#.into()))
        .unwrap_err();
    assert_eq!(
        s.to_graph(Some(r#"{"roots": ["No::Such"]}"#.into()))
            .unwrap_err(),
        uml
    );
    // …while a view the graph emitter lacks is a different refusal,
    // named canonically whatever alias the caller wrote.
    let err = s.to_graph(Some(r#"{"view": "seq"}"#.into())).unwrap_err();
    assert_eq!(err, "no structured-graph emitter for view: sequence");
    assert!(s.to_plantuml(Some(r#"{"view": "seq"}"#.into())).is_ok());
    // Every PlantUML option is accepted on the graph path, aliases included.
    let g: serde_json::Value = serde_json::from_str(
        &s.to_graph(Some(
            r#"{"view": "ic", "horizontal": true, "lineStyle": "ortho", "stdColor": true,
                "linkTemplate": "x://{file}:{line}", "showInherited": true, "roots": ["Extra"]}"#
                .into(),
        ))
        .unwrap(),
    )
    .unwrap();
    assert_eq!(g["view"], "interconnection");
    // `roots` scopes the graph exactly as it scopes the PlantUML.
    let g: serde_json::Value =
        serde_json::from_str(&s.to_graph(Some(r#"{"roots": ["Extra"]}"#.into())).unwrap()).unwrap();
    let labels: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| n["label"].as_str())
        .collect();
    assert!(
        labels.contains(&"Case") && !labels.contains(&"Battery"),
        "{labels:?}"
    );
    let uml = s
        .to_plantuml(Some(r#"{"roots": ["Extra"]}"#.into()))
        .unwrap();
    assert!(uml.contains("Case") && !uml.contains("Battery"), "{uml}");
}

#[test]
fn verify_positions_bindings_in_their_own_unit() {
    // The bound feature is declared in one unit and the constraints
    // that reference it in another: every position comes from its own
    // unit's line index, and one report shares the indexes.
    let defs = "package P {\n    attribute def Real;\n\n    attribute margin : Real = 1;\n}\n";
    let checks = "package Q {\n    private import P::*;\n    assert constraint short { margin >= 2 }\n    assert constraint wide { margin <= 2 }\n}\n";
    let mut s =
        Session::from_sources(&sources(&[("defs.sysml", defs), ("checks.sysml", checks)])).unwrap();
    let report: serde_json::Value = serde_json::from_str(&s.verify(None).unwrap()).unwrap();
    let constraints = report["constraints"].as_array().unwrap();
    assert_eq!(constraints.len(), 2);
    let short = constraints.iter().find(|c| c["name"] == "short").unwrap();
    assert_eq!(short["unitName"], "checks.sysml");
    assert_eq!(short["line"], 3);
    assert_eq!(short["status"], "violated");
    assert_eq!(short["detail"], "VIOLATED (with margin = 1)");
    let b = &short["bindings"].as_array().unwrap()[0];
    assert_eq!(b["feature"], "margin");
    assert_eq!(b["value"], "1");
    assert_eq!(b["unitName"], "defs.sysml");
    assert_eq!(b["line"], 4);
    let wide = constraints.iter().find(|c| c["name"] == "wide").unwrap();
    assert_eq!(wide["status"], "satisfied");
    assert_eq!(wide["unitName"], "checks.sysml");
    assert_eq!(wide["line"], 4);
    assert_eq!(report["summary"]["satisfied"], 1);
    assert_eq!(report["summary"]["violated"], 1);
}
