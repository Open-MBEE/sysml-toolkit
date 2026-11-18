//! `Session::to_full_json_with_policy`: the default full-form export is the
//! passthrough level (the four closure names `[]`, the inheritance-aware
//! properties the owned side, whatever `isImpliedIncluded` says) and a
//! closure policy writes the specification's values (#55).

use serde_json::Value;
use sysmlv2_model::full::{EmissionError, EmissionPolicy, TextLayout, UnresolvedReferencePolicy};
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

/// The three closure levels, unresolved references preserved.
fn levels() -> [EmissionPolicy; 3] {
    [EmissionPolicy::default(), closure(false), closure(true)]
}

/// The text export against the value export, serialized: the same bytes in
/// both layouts at every level, or the same refusal.
fn assert_text_is_the_value(session: &Session, what: &str) {
    assert_text_is_the_value_in(session, what, &[TextLayout::Compact, TextLayout::Indented]);
}

fn assert_text_is_the_value_in(session: &Session, what: &str, layouts: &[TextLayout]) {
    for policy in levels() {
        let value = session.to_full_json_with_policy(policy);
        for &layout in layouts {
            let serialize = match layout {
                TextLayout::Compact => {
                    serde_json::to_string as fn(&Value) -> serde_json::Result<String>
                }
                TextLayout::Indented => serde_json::to_string_pretty,
            };
            let text = session.to_full_json_text_with_policy(policy, layout);
            match (&value, text) {
                (Ok(value), Ok(text)) => assert!(
                    serialize(value).unwrap() == text,
                    "{what}: the {layout:?} text under {:?} is not the value serialized",
                    policy.closures
                ),
                (Err(refused), Err(text)) => assert_eq!(refused, &text, "{what}"),
                (value, text) => panic!(
                    "{what}: under {:?} the value is {} and the text {}",
                    policy.closures,
                    if value.is_ok() { "written" } else { "refused" },
                    if text.is_ok() { "written" } else { "refused" },
                ),
            }
        }
    }
}

/// A session over `source` and one over its compact payload.
fn both_sessions(name: &str, source: &str, library: Option<&sysmlv2_transform::Library>) {
    let text = Session::from_sources_with_library(
        vec![(name.to_string(), source.to_string())],
        library.cloned(),
    )
    .unwrap();
    assert_text_is_the_value(&text, name);
    let payload = text.to_compact_json();
    let loaded = Session::from_interchange_json_with(&payload, library).unwrap();
    assert_text_is_the_value(&loaded, &format!("{name} (payload)"));
}

/// Rows the array-level rules complete, which read other rows: recovery
/// annotations for unresolved references, documentation and comments
/// (prefix and `about`), directed and end features, reference chains,
/// state subactions, requirement verification, view rendering, imports
/// of a membership.
const ARRAY_LEVEL: &str = r#"package Rules {
    doc /* about the package */
    comment note about Rules::Box /* a note */
    port def Out { out attribute v : Missing::Real; inout attribute w; in attribute u; }
    part def Box {
        doc /* a box */
        port i : ~Out;
        part inner { attribute deep; }
        attribute lead = inner.deep;
        attribute other :> Nowhere::thing;
    }
    part def Big :> Box { attribute :>> lead; }
    connection def Link { end a : Box; end b : Box; }
    state def Machine {
        action setup;
        entry setup;
        do action running;
        exit;
        state idle;
    }
    requirement def Light { doc /* stay light */ subject s : Box; }
    requirement light : Light;
    verification def Check {
        subject s : Box;
        objective { verify light; }
    }
    rendering asTable;
    view def Table { render asTable; }
    package Alias { public import Rules::Box; alias B for Box; }
}
"#;

#[test]
fn the_text_is_the_value_serialized() {
    both_sessions("export.sysml", MODEL, None);
    both_sessions("rules.sysml", ARRAY_LEVEL, None);
    let lib = sysmlv2_testkit::library_dir();
    if lib.exists() {
        let library = sysmlv2_transform::Library::dir(&lib);
        both_sessions("export.sysml", MODEL, Some(&library));
        both_sessions("rules.sysml", ARRAY_LEVEL, Some(&library));
    } else {
        eprintln!("skipping the library half: corpus not present");
    }
    // A refusal is the same refusal, and nothing of the text comes back.
    let mut src = String::from("package P { package D0 { part leaf; }");
    for i in 1..=26 {
        src.push_str(&format!(" package D{i} {{ public import D{}::*; }}", i - 1));
    }
    src.push('}');
    let deep = Session::from_sources(vec![("deep.sysml".into(), src)]).unwrap();
    assert!(matches!(
        deep.to_full_json_text_with_policy(closure(false), TextLayout::Compact),
        Err(EmissionError::TruncatedClosures { ref elements }) if !elements.is_empty()
    ));
    assert_text_is_the_value(&deep, "deep.sysml");
}

#[test]
fn the_text_is_the_value_serialized_over_the_corpus() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut files = sysmlv2_testkit::user_files();
    if let Some(more) = sysmlv2_testkit::apollo_files() {
        files.extend(more);
    }
    if files.is_empty() {
        eprintln!("skipping: corpus model files not present");
        return;
    }
    let library = sysmlv2_transform::Library::dir(&lib);
    // Prepare the library once, before the files share it.
    both_sessions("export.sysml", MODEL, Some(&library));
    sysmlv2_testkit::par_map(&files, |path| {
        let source = std::fs::read_to_string(path).unwrap();
        // A file the parser reports on opens as no session.
        let name = path.to_string_lossy().into_owned();
        let Ok(text) =
            Session::from_sources_with_library(vec![(name.clone(), source)], Some(library.clone()))
        else {
            return;
        };
        // The layouts differ in the writer alone, which the small models
        // hold to both; the rows are what the corpus varies.
        let compact = [TextLayout::Compact];
        assert_text_is_the_value_in(&text, &name, &compact);
        let payload = text.to_compact_json();
        if let Ok(loaded) = Session::from_interchange_json_with(&payload, Some(&library)) {
            assert_text_is_the_value_in(&loaded, &format!("{name} (payload)"), &compact);
        }
    });
}
