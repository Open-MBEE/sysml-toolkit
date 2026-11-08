//! `Session::to_full_json_with_policy`: the default full-form export is the
//! passthrough level (the four closure names `[]`, the inheritance-aware
//! properties the owned side, whatever `isImpliedIncluded` says) and a
//! closure policy writes the specification's values (#55).

use serde_json::Value;
use sysmlv2_model::full::{EmissionError, EmissionPolicy, UnresolvedReferencePolicy};
use sysmlv2_model::json::ClosurePolicy;
use sysmlv2_transform::Session;

const MODEL: &str = "package Export {\n    port def Out { out attribute v : ScalarValues::Real; }\n    part def Box {\n        port i : ~Out;\n        attribute a : ScalarValues::Real = 1.0;\n        attribute sum : ScalarValues::Real = a + 2.0;\n    }\n    part def Big :> Box;\n}\n";

fn named<'a>(full: &'a Value, name: &str) -> &'a Value {
    full.as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == name)
        .unwrap_or_else(|| panic!("{name} in the export"))
}

/// The member names behind a list of membership references; a membership
/// the export does not hold (a library membership, under the implied
/// heritage) is `None`.
fn names_of(full: &Value, ids: &Value) -> Vec<Option<String>> {
    let by_id = |id: &str| full.as_array().unwrap().iter().find(|e| e["@id"] == id);
    ids.as_array()
        .unwrap()
        .iter()
        .map(|r| {
            let membership = by_id(r["@id"].as_str().unwrap())?;
            let member = by_id(membership["memberElement"]["@id"].as_str()?)?;
            Some(member["declaredName"].as_str().unwrap_or("").to_string())
        })
        .collect()
}

fn written(names: &[Option<String>]) -> Vec<&str> {
    names.iter().flatten().map(String::as_str).collect()
}

fn closure(include_implied: bool) -> EmissionPolicy {
    EmissionPolicy {
        unresolved: UnresolvedReferencePolicy::Preserve,
        closures: ClosurePolicy::Closure { include_implied },
    }
}

#[test]
fn the_default_export_is_the_passthrough_level_and_a_closure_policy_writes_the_closures() {
    let session = Session::from_sources(vec![("export.sysml".into(), MODEL.into())]).unwrap();
    // The default: `[]` for the closure names, the owned side for `feature`.
    let default = session.to_full_json();
    let big = named(&default, "Big");
    assert_eq!(big["inheritedMembership"], serde_json::json!([]));
    assert_eq!(big["inheritedFeature"], serde_json::json!([]));
    assert_eq!(big["feature"], serde_json::json!([]));
    assert_eq!(
        session
            .to_full_json_with_policy(EmissionPolicy::default())
            .unwrap(),
        session.to_full_json(),
        "the default policy is the compatibility export"
    );
    // The written heritage: Box's three features.
    let closed = session.to_full_json_with_policy(closure(false)).unwrap();
    let big = named(&closed, "Big");
    assert_eq!(
        written(&names_of(&closed, &big["inheritedMembership"])),
        ["i", "a", "sum"]
    );
    assert_eq!(big["inheritedFeature"].as_array().unwrap().len(), 3);
    assert_eq!(big["feature"].as_array().unwrap().len(), 3);
    // Every other row is as the default wrote it.
    let box_default = named(&default, "Box");
    let box_closed = named(&closed, "Box");
    assert_eq!(box_default["ownedFeature"], box_closed["ownedFeature"]);
    assert_eq!(box_default["@id"], box_closed["@id"]);
    assert_eq!(
        default.as_array().unwrap().len(),
        closed.as_array().unwrap().len(),
        "a closure policy adds values, never rows"
    );
}

#[test]
fn the_implied_heritage_joins_under_closure_implied_with_the_library() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let session = Session::from_sources(vec![("export.sysml".into(), MODEL.into())])
        .unwrap()
        .with_library(&lib)
        .unwrap();
    let default = session.to_full_json();
    let big = named(&default, "Big");
    assert_eq!(big["isImpliedIncluded"], true);
    assert_eq!(big["inheritedMembership"], serde_json::json!([]));
    let heritage = session.to_full_json_with_policy(closure(false)).unwrap();
    assert_eq!(
        written(&names_of(
            &heritage,
            &named(&heritage, "Big")["inheritedMembership"]
        )),
        ["i", "a", "sum"]
    );
    // With the implied heritage the library's memberships (`Parts::Part`
    // and above) join: references to elements outside the document.
    let implied = session.to_full_json_with_policy(closure(true)).unwrap();
    let inherited = names_of(&implied, &named(&implied, "Big")["inheritedMembership"]);
    assert!(
        inherited.len() > 50,
        "{} inherited memberships with the implied heritage",
        inherited.len()
    );
    assert_eq!(written(&inherited), ["i", "a", "sum"]);
    assert!(inherited.iter().filter(|n| n.is_none()).count() > 50);
    let big = named(&implied, "Big");
    assert_eq!(
        big["feature"].as_array().unwrap().len(),
        big["inheritedFeature"].as_array().unwrap().len()
    );
}

#[test]
fn a_payload_session_takes_the_policy_too_and_a_truncated_walk_refuses() {
    // A session over an interchange document keeps the ids it carried;
    // the policy applies on that path as well.
    let text = Session::from_sources(vec![("export.sysml".into(), MODEL.into())]).unwrap();
    let payload = text.to_compact_json();
    let loaded = Session::from_interchange_json(&payload).unwrap();
    let closed = loaded.to_full_json_with_policy(closure(false)).unwrap();
    let big = named(&closed, "Big");
    assert_eq!(big["@id"], named(&payload, "Big")["@id"]);
    assert_eq!(big["inheritedFeature"].as_array().unwrap().len(), 3);
    // An import chain past the resolver's depth budget: the closure
    // levels refuse rather than write a cut closure; the default never
    // refuses.
    let mut src = String::from("package P { package D0 { part leaf; }");
    for i in 1..=26 {
        src.push_str(&format!(" package D{i} {{ public import D{}::*; }}", i - 1));
    }
    src.push('}');
    let deep = Session::from_sources(vec![("deep.sysml".into(), src)]).unwrap();
    let err = deep.to_full_json_with_policy(closure(false)).unwrap_err();
    assert!(
        matches!(err, EmissionError::TruncatedClosures { ref elements } if !elements.is_empty())
    );
    assert!(
        deep.to_full_json_with_policy(EmissionPolicy::default())
            .is_ok()
    );
}
