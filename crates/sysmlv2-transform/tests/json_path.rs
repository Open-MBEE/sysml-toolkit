//! JSON-sourced sessions: lift → edit → emit for interchange
//! payloads with no text behind them (the Flexo MMS path). Gates: edits
//! land in the re-emitted JSON, Flexo-named payloads keep their ids
//! byte-stable through the round trip, id_map_from covers exactly the
//! moved/foreign elements, and Flexo change-record wrapping unwraps.

use serde_json::{Value, json};
use sysmlv2_model::json::model_to_compact_json;
use sysmlv2_model::model::Model;
use sysmlv2_transform::Session;

const DEMO: &str = "package Demo {
    part def Wheel;
    part def Vehicle {
        part front : Wheel;
        part rear : Wheel;
    }
    part car : Vehicle;
}
";

/// Compact JSON for DEMO, emitted the way the CLI's `--flexo` does:
/// root namespace's qualifiedName carries the source file name.
fn demo_json(unit_name: &str) -> Value {
    let mut model = Model::new();
    let unit = model.add_source(unit_name.to_string(), DEMO);
    assert!(unit.diagnostics.is_empty());
    let mut value = model_to_compact_json(&model);
    stamp_root(&mut value, unit_name);
    value
}

/// Flexo convention: the root Namespace's qualifiedName names the file.
fn stamp_root(value: &mut Value, name: &str) {
    for e in value.as_array_mut().unwrap() {
        let is_root =
            e["@type"] == "Namespace" && e.get("owningRelationship").is_none_or(Value::is_null);
        if is_root {
            e["qualifiedName"] = Value::String(name.to_string());
        }
    }
}

fn ids(value: &Value) -> Vec<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|e| e["@id"].as_str().unwrap().to_string())
        .collect()
}

fn declared_names(value: &Value) -> Vec<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|e| e["declaredName"].as_str().map(str::to_string))
        .collect()
}

#[test]
fn flexo_named_payload_round_trips_id_stable() {
    let input = demo_json("m.sysml");
    let mut s = Session::from_interchange_json(&input).expect("lifts");
    assert!(s.warnings().is_empty(), "{:?}", s.warnings());
    // Unit named by the Flexo convention.
    assert_eq!(s.units().next().unwrap().1, "m.sysml");
    // Same unit name -> same ownership paths -> identical ids.
    let out = s.to_compact_json();
    assert_eq!(ids(&input), ids(&out));
    assert!(s.id_map_from(&input).is_empty(), "no ids moved");
}

#[test]
fn edit_a_payload_and_reemit() {
    let input = demo_json("m.sysml");
    let mut s = Session::from_interchange_json(&input).expect("lifts");
    let wheel = s.resolved().resolve_qualified("Demo::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(wheel, "RoadWheel");
    let report = edit.commit().expect("commit");

    let out = s.to_compact_json();
    let names = declared_names(&out);
    assert!(names.iter().any(|n| n == "RoadWheel"), "{names:?}");
    assert!(names.iter().all(|n| n != "Wheel"), "{names:?}");
    // The rename moved the def's id (name feeds the ownership path);
    // id_map_from(input) reports exactly the moved elements.
    assert!(!report.id_map.is_empty());
    let map = s.id_map_from(&input);
    // Wheel itself is renamed, so its old qualified name no longer maps —
    // but every OTHER element still maps, id-stable.
    assert!(map.is_empty(), "unmoved elements keep ids: {map:?}");

    // The emitted payload re-lifts into a working session.
    let mut s2 = Session::from_interchange_json(&out).expect("re-lifts");
    assert!(s2.resolved().resolve_qualified("Demo::RoadWheel").is_some());
    assert_eq!(s2.resolved().unresolved_count(), 0);
}

#[test]
fn anonymous_root_gets_numbered_unit_and_ids_map() {
    // No Flexo naming: the lifted unit is document-1.sysml, so the
    // ownership paths (and ids) differ from the original m.sysml
    // emission — id_map_from names every element's move.
    let input = demo_json_unstamped();
    let mut s = Session::from_interchange_json(&input).expect("lifts");
    assert_eq!(s.units().next().unwrap().1, "document-1.sysml");
    let out = s.to_compact_json();
    assert_ne!(ids(&input), ids(&out));
    let map = s.id_map_from(&input);
    // Every *named* element maps old -> new.
    assert!(!map.is_empty());
    for (old, _) in &map {
        assert!(ids(&input).contains(&old.to_string()));
    }
}

fn demo_json_unstamped() -> Value {
    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), DEMO);
    model_to_compact_json(&model)
}

#[test]
fn multi_document_payload_edits_across_units() {
    let defs = "package Defs {\n    part def Wheel;\n}\n";
    let uses = "package Uses {\n    private import Defs::*;\n    part w : Wheel;\n}\n";
    let mut model = Model::new();
    model.add_source("defs.sysml".to_string(), defs);
    model.add_source("uses.sysml".to_string(), uses);
    let mut value = model_to_compact_json(&model);
    // Stamp each root with its file name (what `--flexo` does).
    let mut names = ["defs.sysml", "uses.sysml"].iter();
    for e in value.as_array_mut().unwrap() {
        let is_root =
            e["@type"] == "Namespace" && e.get("owningRelationship").is_none_or(Value::is_null);
        if is_root {
            e["qualifiedName"] = Value::String(names.next().unwrap().to_string());
        }
    }

    let mut s = Session::from_interchange_json(&value).expect("lifts");
    let unit_names: Vec<&str> = s.units().map(|(_, n, _)| n).collect();
    assert_eq!(unit_names, ["defs.sysml", "uses.sysml"]);
    assert_eq!(s.resolved_ref().unresolved_count(), 0);

    // A rename in defs respells the reference in uses (the lift spells
    // cross-document references `$::`-rooted; the engine respells the
    // segment inside that spelling).
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(wheel, "RoadWheel");
    edit.commit().expect("commit");
    let uses_text = s.units().nth(1).unwrap().2.to_string();
    assert!(
        uses_text.contains("part w : $::Defs::RoadWheel;"),
        "{uses_text}"
    );

    // Re-emission still splits into the two named documents.
    let out = s.to_compact_json();
    let docs = sysmlv2_model::lift::split_documents(&out).expect("two documents");
    assert_eq!(docs.len(), 2);
}

#[test]
fn cross_document_dependency_and_membership_import_lift_named() {
    // Dependency ends and membership imports that point across
    // documents must lift to `$::`-rooted spellings — not drop the
    // reference (`dependency a to ;`) or the import.
    let defs = "package Defs {\n    part def Wheel;\n    requirement def <'R-1'> Spec;\n}\n";
    let uses = "package Uses {\n    private import Defs::Wheel;\n    part w : Wheel;\n    dependency w to Defs::Spec;\n}\n";
    let mut model = Model::new();
    model.add_source("defs.sysml".to_string(), defs);
    model.add_source("uses.sysml".to_string(), uses);
    let mut value = model_to_compact_json(&model);
    let mut names = ["defs.sysml", "uses.sysml"].iter();
    for e in value.as_array_mut().unwrap() {
        let is_root =
            e["@type"] == "Namespace" && e.get("owningRelationship").is_none_or(Value::is_null);
        if is_root {
            e["qualifiedName"] = Value::String(names.next().unwrap().to_string());
        }
    }

    let s = Session::from_interchange_json(&value).expect("lifts");
    assert!(s.warnings().is_empty(), "{:?}", s.warnings());
    let uses_text = s.units().nth(1).unwrap().2.to_string();
    assert!(
        uses_text.contains("dependency $::Uses::w to $::Defs::Spec;"),
        "{uses_text}"
    );
    assert!(
        uses_text.contains("private import $::Defs::Wheel;"),
        "{uses_text}"
    );
    // The lifted text is a working model again.
    assert_eq!(s.resolved_ref().unresolved_count(), 0);
}

#[test]
fn flexo_change_records_unwrap() {
    let input = demo_json("m.sysml");
    let wrapped = Value::Array(
        input
            .as_array()
            .unwrap()
            .iter()
            .map(|e| json!({ "payload": e, "identity": { "@id": e["@id"] } }))
            .collect(),
    );
    let mut s = Session::from_interchange_json(&wrapped).expect("unwraps and lifts");
    assert!(s.resolved().resolve_qualified("Demo::Vehicle").is_some());
    // And the ids still line up with the unwrapped originals.
    assert_eq!(ids(&s.to_compact_json()), ids(&input));
}

#[test]
fn full_form_input_is_accepted() {
    let input = demo_json("m.sysml");
    let s = Session::from_interchange_json(&input).expect("lifts");
    let mut full = s.to_full_json();
    assert!(full.as_array().unwrap().len() >= input.as_array().unwrap().len());
    // Full form (with its derived properties) lifts back to the same
    // model; the root name rides qualifiedName like any Flexo payload.
    stamp_root(&mut full, "m.sysml");
    let mut s2 = Session::from_interchange_json(&full).expect("full form lifts");
    assert!(s2.resolved().resolve_qualified("Demo::Vehicle").is_some());
    assert_eq!(s2.resolved().unresolved_count(), 0);
    assert_eq!(ids(&s2.to_compact_json()), ids(&input));
}

#[test]
fn recover_refs_full_form_survives_unresolved_references() {
    let src = "package P {\n    part def K;\n    part x : Missing;\n}\n";
    let s = Session::from_sources(vec![("p.sysml".to_string(), src.to_string())]).expect("parses");
    assert_eq!(s.resolved_ref().unresolved_count(), 1);

    // Full form is lossless by default for partial models.
    let plain = s.to_full_json();
    let lifted = Session::from_interchange_json(&plain).expect("lifts");
    let text = lifted.units().next().unwrap().2.to_string();
    assert!(text.contains("part x : Missing;"), "{text}");

    // The compatibility switch still exposes the legacy dangling-id form,
    // whose source spelling cannot survive read-back.
    let legacy = s.to_full_json_with(false);
    let lifted = Session::from_interchange_json(&legacy).expect("lifts");
    let text = lifted.units().next().unwrap().2.to_string();
    assert!(!text.contains("Missing"), "{text}");

    // Explicit recovery is equivalent to the new default.
    let recovered = s.to_full_json_with(true);
    let lifted = Session::from_interchange_json(&recovered).expect("lifts");
    let text = lifted.units().next().unwrap().2.to_string();
    assert!(text.contains("part x : Missing;"), "{text}");
}

#[test]
fn library_typed_payload_lifts_with_library() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.is_dir() {
        eprintln!("skipping: standard library not present");
        return;
    }
    let src = "package P {\n    attribute mass : ScalarValues::Real;\n}\n";
    let s = Session::from_sources(vec![("m.sysml".to_string(), src.to_string())])
        .expect("parses")
        .with_library(&lib)
        .expect("library loads");
    let mut payload = s.to_compact_json();
    stamp_root(&mut payload, "m.sysml");

    // With the library, the library-typed reference lifts back to its
    // qualified name, resolves, and the round trip stays id-stable.
    let lifted = Session::from_interchange_json_with_library(&payload, Some(&lib))
        .expect("lifts with library");
    let text = lifted.units().next().unwrap().2.to_string();
    assert!(text.contains("ScalarValues::Real"), "{text}");
    // The library's own unresolved tail is constant — the lifted user
    // unit must add nothing to it.
    assert_eq!(
        lifted.resolved_ref().unresolved_count(),
        s.resolved_ref().unresolved_count()
    );
    let mut reemitted = lifted.to_compact_json();
    stamp_root(&mut reemitted, "m.sysml");
    assert_eq!(ids(&payload), ids(&reemitted));

    // Without it, the library id has no name to lift to.
    if let Ok(libless) = Session::from_interchange_json(&payload) {
        let text = libless.units().next().unwrap().2.to_string();
        assert!(!text.contains("ScalarValues::Real"), "{text}");
    }
}

/// Lib-gated: interchange reconstruction fidelity for library-typed
/// payloads. The full-form derived relationships computed from a
/// *reconstructed* session (compact JSON re-lifted against the standard
/// library) must be identical to the ones computed from the original
/// text — the derived fields most likely to drift (`feature`,
/// `featureMembership`, `inheritedFeature`, `usage`, every Subsetting's
/// ends) are audited per element, metaclasses must survive (a
/// connection usage must not degrade to a plain usage), and loading the
/// same payload *without* the library must say so rather than silently
/// misresolve.
#[test]
fn library_typed_reconstruction_keeps_derived_relationships() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let src = "package Rig {
        private import ScalarValues::*;
        part def Motor { attribute torque : Real; }
        part def Frame;
        part left : Motor { attribute :>> torque = 5.0; }
        part mount : Frame;
        connection bond connect left to mount;
        attribute heft :> ISQ::mass;
    }";
    let a = Session::from_sources(vec![("rig.sysml".into(), src.into())])
        .unwrap()
        .with_library(&lib)
        .unwrap();
    let full_a = a.to_full_json_with(true);
    let mut compact = a.to_compact_json();
    // Name the payload root (the Flexo convention) so the reconstructed
    // session derives the same unit name — ids stay comparable.
    stamp_root(&mut compact, "rig.sysml");

    let b = sysmlv2_transform::Session::from_interchange_json_with_library(&compact, Some(&lib))
        .unwrap();
    assert!(b.warnings().is_empty(), "{:?}", b.warnings());
    let full_b = b.to_full_json_with(true);

    let index = |v: &Value| -> std::collections::HashMap<String, Value> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|e| (e["@id"].as_str().unwrap().to_string(), e.clone()))
            .collect()
    };
    let ia = index(&full_a);
    let ib = index(&full_b);
    assert_eq!(ia.len(), ib.len(), "element population changed");
    let audit = [
        "feature",
        "featureMembership",
        "inheritedFeature",
        "usage",
        "subsettedFeature",
        "subsettingFeature",
        "general",
        "relatedElement",
        "source",
        "target",
        "type",
        "typedFeature",
    ];
    for (id, ea) in &ia {
        let eb = ib
            .get(id)
            .unwrap_or_else(|| panic!("element {id} missing after reconstruction"));
        assert_eq!(ea["@type"], eb["@type"], "metaclass drift on {id}");
        for k in audit {
            assert_eq!(
                ea.get(k),
                eb.get(k),
                "derived `{k}` differs on {id} ({})",
                ea["@type"]
            );
        }
    }
    assert!(
        full_b
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "ConnectionUsage" && e["declaredName"] == "bond"),
        "the connection usage must keep its metaclass"
    );

    // Without the library seed, the same payload must complain, not
    // silently misresolve.
    let c = sysmlv2_transform::Session::from_interchange_json(&compact).unwrap();
    assert!(
        !c.warnings().is_empty(),
        "a library-typed payload without the library must report its lift problems"
    );
}

#[test]
fn lift_with_tab_indentation() {
    let input = demo_json("m.sysml");
    let s = sysmlv2_transform::Session::from_interchange_json_indented(
        &input,
        None,
        &[],
        sysmlv2_transform::Indent::Tabs,
    )
    .expect("lifts");
    let text = s.units().next().unwrap().2.to_string();
    assert!(text.contains("\n\tpart def Wheel;"), "{text}");
    assert!(text.contains("\n\t\tpart front :"), "{text}");
    // Identity is layout-independent: same ids as the spaces lift.
    let s2 = sysmlv2_transform::Session::from_interchange_json(&input).expect("lifts");
    let s1 = s;
    assert_eq!(ids(&s1.to_compact_json()), ids(&s2.to_compact_json()));
}

#[test]
fn multiline_doc_bodies_reflow_and_invert() {
    // Interchange bodies arrive dedented; the lifted text lays them
    // out as a `*`-guttered block at depth — and the emit-side
    // normalization strips that layout back to the identical body.
    let src = "package P {\n    part def K {\n        doc\n        /*\n        * line one\n        * line two\n        */\n    }\n}\n";
    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), src);
    let mut value = model_to_compact_json(&model);
    stamp_root(&mut value, "m.sysml");

    let body = |v: &Value| -> String {
        v.as_array()
            .unwrap()
            .iter()
            .find(|e| e["@type"] == "Documentation")
            .and_then(|e| e["body"].as_str())
            .unwrap()
            .to_string()
    };
    let s = Session::from_interchange_json(&value).expect("lifts");
    let text = s.units().next().unwrap().2.to_string();
    assert!(
        text.contains("        doc /*\n         * line one\n         * line two\n         */\n"),
        "{text}"
    );
    let out = s.to_compact_json();
    assert_eq!(body(&value), body(&out));
    // `rep` bodies emit raw — they stay verbatim, never reflowed.
    let rep = "package R {\n    rep language \"none\" /*a\nb*/\n}\n";
    let mut m2 = Model::new();
    m2.add_source("r.sysml".to_string(), rep);
    let mut v2 = model_to_compact_json(&m2);
    stamp_root(&mut v2, "r.sysml");
    let s2 = Session::from_interchange_json(&v2).expect("lifts");
    let t2 = s2.units().next().unwrap().2.to_string();
    assert!(t2.contains("/*a\nb*/"), "{t2}");
}
