//! Reserved words used as names. The model's qualified name follows the
//! specification's `escapedName` derivation (KerML 8.3.2.1: a name with
//! the *form* of a basic name is returned as-is), which the pilot
//! implementation applies literally and which the normative library ids
//! hash — `ControlFunctions::if`, not `ControlFunctions::'if'`. That
//! spelling is a model property, not parseable text: the textual
//! notation refuses a bare reserved word (KerML 8.2.2.6), so reference
//! text quotes it. These gates pin both sides.

use sysmlv2_parser::ids::derive_ids;
use sysmlv2_parser::json::{ResolvedModel, library_element_name_map, model_to_compact_json};
use sysmlv2_parser::model::Model;

/// Every declared name is a SysML reserved word (`as` is reserved in
/// both dialects, `part`/`action`/`view` in SysML only).
const RESERVED: &str = "package 'part' {\n    \
    part def 'action';\n    \
    part 'view' : 'action';\n    \
    part 'if' : 'action' {\n        attribute 'as' = 1;\n    }\n}\n";

fn model(src: &str) -> Model {
    let mut model = Model::new();
    let unit = model.add_source("t.sysml", src);
    assert!(
        unit.diagnostics.is_empty(),
        "test source must parse cleanly: {:?}",
        unit.diagnostics[0]
    );
    model
}

#[test]
fn qualified_names_keep_reserved_words_bare_like_the_pilot() {
    let mut r = ResolvedModel::build(&model(RESERVED));
    let view = r
        .resolve_qualified("'part'::'view'")
        .expect("quoted lookup");
    assert_eq!(
        r.element_qualified_name(view).as_deref(),
        Some("part::view")
    );
    // Lookup accepts either spelling of a canonical name.
    assert_eq!(r.resolve_qualified("part::view"), Some(view));
    let as_ = r.resolve_qualified("part::if::as").expect("bare lookup");
    assert_eq!(
        r.element_qualified_name(as_).as_deref(),
        Some("part::if::as")
    );
}

#[test]
fn reference_spelling_quotes_reserved_words() {
    let mut r = ResolvedModel::build(&model(RESERVED));
    let view = r.resolve_qualified("part::view").unwrap();
    assert_eq!(
        r.element_reference_spelling(view).as_deref(),
        Some("'part'::'view'")
    );
    let as_ = r.resolve_qualified("part::if::as").unwrap();
    assert_eq!(
        r.element_reference_spelling(as_).as_deref(),
        Some("'part'::'if'::'as'")
    );
    // Anonymous elements have neither.
    let anon = r
        .user_elements()
        .find(|&e| r.element_type(e) == "FeatureValue")
        .expect("the value's owning membership");
    assert_eq!(r.element_qualified_name(anon), None);
    assert_eq!(r.element_reference_spelling(anon), None);
}

/// Graph-derived ids (IDS.md) hash `escape_name` segments — the bare
/// reserved word — and must not move with the reference spelling. The
/// constants were computed before reference spelling existed.
#[test]
fn graph_derived_ids_are_unchanged_by_reference_spelling() {
    let model = model(RESERVED);
    let mut r = ResolvedModel::build(&model);
    let pinned = [
        ("part::view", "effad461-6a16-542b-b395-69f9df3dba79"),
        ("part::if", "5eac2530-a9a9-5f44-a399-4f00704747b3"),
        ("part::if::as", "7ac80c17-5317-52bb-bb5d-70abfcfbc4f9"),
    ];
    for (qn, id) in pinned {
        let e = r.resolve_qualified(qn).unwrap();
        assert_eq!(r.element_id(e).to_string(), id, "{qn}");
    }
    // The value-side derivation agrees with the builder's assignment.
    let compact = model_to_compact_json(&model);
    let derived = derive_ids(&compact, &|s| panic!("unexpected external {s}")).unwrap();
    let elements = compact.as_array().unwrap();
    let mut checked = 0;
    for (e, d) in elements.iter().zip(derived) {
        if let Some(d) = d {
            assert_eq!(e["@id"].as_str().unwrap(), d.to_string());
            checked += 1;
        }
    }
    assert!(checked >= 8, "{checked} derived ids");
}

/// Normative library ids (KerML 9.1) hash the bare spelling: these are
/// the `elementId`s the pilot implementation publishes in its XMI for
/// three reserved-word-named library elements.
#[test]
fn library_ids_hash_the_bare_reserved_word() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    // Elements only: the map with memberships holds a second entry per
    // member (`…/owningMembership`) under the same segments.
    let names = library_element_name_map(&model);
    let id_of = |segments: &[&str]| -> Option<String> {
        names
            .iter()
            .find(|(_, s)| s.iter().map(String::as_str).eq(segments.iter().copied()))
            .map(|(id, _)| id.clone())
    };
    assert_eq!(
        id_of(&["ControlFunctions", "if"]).as_deref(),
        Some("396c01c4-4dc9-5cf6-8e62-742903a68137")
    );
    assert_eq!(
        id_of(&["BaseFunctions", "all"]).as_deref(),
        Some("f53a4d1a-b2da-5806-af64-2877e7bc4014")
    );
    assert_eq!(
        id_of(&["SysML", "Systems", "ViewDefinition", "view"]).as_deref(),
        Some("8d771b7d-7b73-55dc-9a62-d5236a482081")
    );
    let mut r = ResolvedModel::build(&model);
    let e = r
        .resolve_qualified("ControlFunctions::'if'")
        .expect("library function");
    assert_eq!(
        r.element_qualified_name(e).as_deref(),
        Some("ControlFunctions::if")
    );
    assert_eq!(
        r.element_reference_spelling(e).as_deref(),
        Some("ControlFunctions::'if'")
    );
    assert_eq!(
        r.element_id(e).to_string(),
        "396c01c4-4dc9-5cf6-8e62-742903a68137"
    );
}
