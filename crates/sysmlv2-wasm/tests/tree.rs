//! The ownership tree across the boundary: `tree` is the model layer's
//! `inspect::tree` as JSON and `treeText` its text, over a selected root
//! or the whole model, with the options the CLI's flags set.
use sysmlv2_wasm::Session;

fn sources(pairs: &[(&str, &str)]) -> String {
    serde_json::to_string(
        &pairs
            .iter()
            .map(|(n, t)| serde_json::json!({"name": n, "text": t}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

const VEHICLE: &str = "package Demo {\n    attribute def Mass;\n    part def Vehicle {\n        attribute mass : Mass;\n    }\n    part v : Vehicle;\n    alias m for Vehicle::mass;\n}\n";

fn tree(s: &mut Session, opts: &str) -> serde_json::Value {
    serde_json::from_str(&s.tree(Some(opts.to_string())).unwrap()).unwrap()
}

#[test]
fn text_and_json_are_the_cli_s_over_a_selected_root() {
    let mut s = Session::from_sources(&sources(&[("demo.sysml", VEHICLE)])).unwrap();
    let by_name = s
        .tree_text(Some(r#"{"root": "Demo::Vehicle"}"#.to_string()))
        .unwrap();
    assert_eq!(
        by_name,
        "Demo::Vehicle [PartDefinition]
└─ FeatureMembership
   └─ mass [AttributeUsage]
      ├─ FeatureTyping
      │  └─ type → Demo::Mass [AttributeDefinition]
      └─ OwningMembership
         └─ (anonymous) [Multiplicity]
"
    );
    let vehicle = s.resolve("Demo::Vehicle").unwrap();
    let id = s.element_id(&vehicle).unwrap();
    let by_id = s
        .tree_text(Some(format!(r#"{{"root": {{"elementId": "{id}"}}}}"#)))
        .unwrap();
    assert_eq!(by_id, by_name, "an element id selects the same root");

    let json = tree(&mut s, r#"{"root": "Demo::Vehicle", "ids": true}"#);
    assert_eq!(json[0]["qualifiedName"], "Demo::Vehicle");
    assert_eq!(json[0]["id"], id);
    let typing = &json[0]["relationships"][0]["children"][0]["relationships"][0];
    assert_eq!(typing["metaclass"], "FeatureTyping");
    assert_eq!(typing["references"][0]["property"], "type");
    assert_eq!(
        typing["references"][0]["target"]["qualifiedName"],
        "Demo::Mass"
    );
    assert!(
        tree(&mut s, r#"{"root": "Demo::Vehicle"}"#)[0]["id"].is_null(),
        "ids ride along on request only"
    );
}

#[test]
fn the_whole_model_with_the_depth_reference_and_implied_options() {
    let mut s = Session::from_sources(&sources(&[("demo.sysml", VEHICLE)])).unwrap();
    let text = s.tree_text(None).unwrap();
    assert!(
        text.starts_with("Demo [Package]\n├─ OwningMembership\n│  └─ Mass [AttributeDefinition]\n"),
        "{text}"
    );
    assert!(
        text.contains("memberElement → Demo::Vehicle::mass [AttributeUsage]"),
        "{text}"
    );
    assert_eq!(
        s.tree_text(Some(String::new())).unwrap(),
        text,
        "empty options are the defaults"
    );

    let whole = tree(&mut s, r#"{"depth": 1, "references": false}"#);
    let demo = &whole[0];
    assert_eq!(demo["qualifiedName"], "Demo");
    assert_eq!(demo["relationships"].as_array().unwrap().len(), 4);
    assert!(
        demo["relationships"][0]["children"][0]["truncated"].is_null(),
        "a leaf is whole"
    );
    assert_eq!(
        demo["relationships"][1]["children"][0]["truncated"], true,
        "the depth cut the walk"
    );
    assert!(
        demo["relationships"][3]["references"].is_null(),
        "no references on request"
    );
    assert!(
        s.tree_text(Some(r#"{"depth": 1}"#.to_string()))
            .unwrap()
            .contains(" …\n")
    );
    assert!(s.tree(Some(r#"{"implied": true}"#.to_string())).is_ok());
}

#[test]
fn refusals_name_the_option_or_the_root() {
    let mut s = Session::from_sources(&sources(&[("demo.sysml", VEHICLE)])).unwrap();
    let err = s.tree(Some(r#"{"nope": 1}"#.to_string())).unwrap_err();
    assert!(err.starts_with("bad options"), "{err}");
    let err = s
        .tree(Some(r#"{"root": "Demo::Nope"}"#.to_string()))
        .unwrap_err();
    assert_eq!(err, "element not found: Demo::Nope");
    let err = s
        .tree_text(Some(r#"{"root": {"elementId": "not-an-id"}}"#.to_string()))
        .unwrap_err();
    assert_eq!(err, "element not found: not-an-id");
}
