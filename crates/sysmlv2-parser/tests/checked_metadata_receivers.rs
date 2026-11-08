//! Metadata-annotated elements as receivers of the checked member lists:
//! plain metadata (`#Tag part p;`, `@Tag { … }`) adds no base and keeps
//! nothing out; semantic metadata (a definition conforming to
//! `Metaobjects::SemanticMetadata`) gives the annotated element an implied
//! specialization of the metadata's `baseType` value (KerML 9.2), planned
//! as a row: a feature subsets a feature base, a classifier subclassifies a
//! classifier base, and the member lists answer through it.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, ElementRef, ResolvedModel},
    model::Model,
};

const SOURCE: &str = "package Mt {
    import Metaobjects::SemanticMetadata;
    metadata def Tag { attribute t; }
    part def P { attribute m; }
    #Tag part tagged : P;
    part noted : P { @Tag { t = 1; } }
    part def Base { attribute b; }
    part bases : Base[*];
    metadata def Sem :> SemanticMetadata { :>> baseType = bases meta SysML::Usage; }
    #Sem part sem;
    metadata def SemDef :> SemanticMetadata { :>> baseType = Base meta SysML::Definition; }
    #SemDef part def Derived;
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("metadata.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn named(r: &mut ResolvedModel, path: &str) -> ElementRef {
    r.resolve_qualified(path)
        .unwrap_or_else(|| panic!("no {path}"))
}

fn names(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<String> {
    let what = r.element_qualified_name(e).unwrap_or_default();
    let value = r
        .property(e, property)
        .unwrap_or_else(|err| panic!("{what}.{property}: {err}"));
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            let id = v["@id"].as_str().unwrap().to_string();
            let e = r.element_by_id(&id).unwrap();
            r.element_qualified_name(e).unwrap_or_default()
        })
        .collect()
}

#[test]
fn plainly_annotated_elements_answer_the_member_lists() {
    let mut r = model();
    for path in ["Mt::tagged", "Mt::noted"] {
        let e = named(&mut r, path);
        let features = names(&mut r, e, "feature");
        assert!(
            features.contains(&"Mt::P::m".to_string()),
            "{path}: {features:?}"
        );
        let members = names(&mut r, e, "member");
        assert!(
            members.contains(&"Mt::P::m".to_string()),
            "{path}: {members:?}"
        );
    }
    // The annotating metadata usage is an owned member of its element and
    // none of its features.
    let noted = named(&mut r, "Mt::noted");
    let owned_members = r.property(noted, "ownedMember").unwrap();
    assert_eq!(
        owned_members.as_array().map(Vec::len),
        Some(1),
        "{owned_members}"
    );
    let owned_features = r.property(noted, "ownedFeature").unwrap();
    assert_eq!(
        owned_features.as_array().map(Vec::len),
        Some(0),
        "{owned_features}"
    );
}

#[test]
fn semantically_annotated_elements_specialize_their_base() {
    let mut r = model();
    // `#Sem part sem;` subsets `bases` (a feature base), so it inherits the
    // base's features and answers its lists.
    let sem = named(&mut r, "Mt::sem");
    let features = names(&mut r, sem, "feature");
    assert!(
        features.contains(&"Mt::Base::b".to_string()),
        "{features:?}"
    );
    let implied = implied_targets(&mut r, sem);
    assert!(implied.contains(&"Mt::bases".to_string()), "{implied:?}");
    // `#SemDef part def Derived;` subclassifies `Base` (a classifier base).
    let derived = named(&mut r, "Mt::Derived");
    let features = names(&mut r, derived, "feature");
    assert!(
        features.contains(&"Mt::Base::b".to_string()),
        "{features:?}"
    );
    let implied = implied_targets(&mut r, derived);
    assert!(implied.contains(&"Mt::Base".to_string()), "{implied:?}");
}

/// The targets of the implied relationships `e` owns, by qualified name.
fn implied_targets(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let mut out = Vec::new();
    for edge in r.implied_relationships(e) {
        for target in r.relationship_ends(edge).1 {
            if let sysmlv2_parser::json::Reference::Element(t) = target {
                out.push(r.element_qualified_name(t).unwrap_or_default());
            }
        }
    }
    out
}
