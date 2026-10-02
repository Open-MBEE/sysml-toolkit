#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ElementRef, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
const LIBRARY: &str = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Metaobjects {metaclass SemanticMetadata {feature baseType;}}";
fn models(user: &str) -> Vec<(Model, ResolvedModel)> {
    models_with(LIBRARY, user)
}
fn models_with(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    assert!(
        base.add_library_source("bases.kerml", library)
            .diagnostics
            .is_empty()
    );
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(71).unwrap(), 71).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("bases.kerml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            let p = m.add_source("about.kerml", user);
            assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
            let r = ResolvedModel::build(&m);
            (m, r)
        })
        .collect()
}
fn check_canonical(m: &Model, r: &mut ResolvedModel) {
    let meta = r
        .resolve_qualified("Metaobjects::SemanticMetadata")
        .unwrap();
    assert_eq!(
        sysmlv2_parser::json::library_element_name_map(m).get(&r.element_id(meta).to_string()),
        Some(&vec![
            "Metaobjects".to_owned(),
            "SemanticMetadata".to_owned()
        ])
    );
}
const BASE: &str = "metaclass U; class A {feature inherited;} metaclass Tagged :> Metaobjects::SemanticMetadata {:>> baseType=A meta U;}";
fn target(r: &mut ResolvedModel, e: ElementRef, key: &str) -> Option<String> {
    r.element_properties(e)
        .get(key)?
        .get("@id")?
        .as_str()
        .map(str::to_owned)
}
#[test]
fn explicit_about_matches_prefix_and_resolves_earlier_inherited_reference() {
    for about in [false, true] {
        let class = "class C {feature child subsets inherited;}";
        let suffix = if about {
            format!("{class} @Tagged about C;")
        } else {
            format!("#Tagged {class}")
        };
        for (m, mut r) in models(&format!("{BASE} {suffix}")) {
            check_canonical(&m, &mut r);
            let a = r.resolve_qualified("A").unwrap();
            let c = r.resolve_qualified("C").unwrap();
            let inherited = r.resolve_qualified("A::inherited").unwrap();
            assert_eq!(r.metadata_of(c).len(), 1);
            assert!(r.conforms_with_implied(c, a));
            let child = r.resolve_qualified("C::child").unwrap();
            let sub = r
                .owned_relationships(child)
                .into_iter()
                .find(|&e| r.element_type(e) == "Subsetting")
                .unwrap();
            assert_eq!(
                target(&mut r, sub, "subsettedFeature"),
                Some(r.element_id(inherited).to_string())
            );
        }
    }
}
#[test]
fn alias_target_and_repeated_explicit_targets_preserve_one_metadata_identity() {
    for (m, mut r) in models(&format!(
        "{BASE} class C; alias Alias for C; @Tagged about Alias,C;"
    )) {
        check_canonical(&m, &mut r);
        let c = r.resolve_qualified("C").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        assert_eq!(r.metadata_of(c).len(), 1);
        assert!(r.conforms_with_implied(c, a));
    }
}

#[test]
fn explicit_about_drives_metadata_filters_and_evaluation() {
    let library = format!("{LIBRARY} standard library package KerML {{metaclass Class;}}");
    let user = "metaclass Mark; package Items {class C; class D;} package Selected {public import Items::*[@Mark];} @Mark about Items::C;";
    for (_, mut r) in models_with(&library, user) {
        let c = r.resolve_qualified("Items::C").unwrap();
        assert!(r.resolve_qualified("Selected::C").is_some());
        assert!(r.resolve_qualified("Selected::D").is_none());
        let expected = r.metadata_of(c);
        assert_eq!(expected.len(), 1);
        let parsed = sysmlv2_parser::parser::parse_expression("Items::C.metadata");
        assert!(parsed.diagnostics.is_empty());
        let scope = r.root_scope();
        let value = r.query(scope, &parsed.expr.unwrap()).unwrap();
        let sysmlv2_parser::eval::Value::Sequence(items) = value else {
            panic!("{value:?}")
        };
        assert_eq!(items.len(), 2);
        assert!(matches!(&items[0],sysmlv2_parser::eval::Value::Element(e) if *e==expected[0]));
    }
}
#[test]
fn prepared_library_associations_and_user_annotations_on_library_types_are_preserved() {
    let library =
        format!("{LIBRARY} {BASE} class Existing; @Tagged about Existing; class NewTarget;");
    for (model, mut r) in models_with(&library, "@Tagged about NewTarget;") {
        let loaded = model.loaded_library_unit_count();
        let a = r.resolve_qualified("A").unwrap();
        for name in ["Existing", "NewTarget"] {
            let target = r.resolve_qualified(name).unwrap();
            assert_eq!(r.metadata_of(target).len(), 1, "{name}");
            assert!(r.conforms_with_implied(target, a), "{name}");
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
#[test]
fn warmed_source_id_binding_moves_about_association_and_preserves_prefix_metadata() {
    use std::collections::HashMap;
    const ID: &str = "88888888-8888-4888-8888-888888888888";
    let user = format!("metaclass Mark; #Mark class Actual; class '{ID}'; @Mark about '{ID}';");
    for (_, mut r) in models(&user) {
        let actual = r.resolve_qualified("Actual").unwrap();
        let lexical = r.resolve_qualified(ID).unwrap();
        let original = r.metadata_of(actual);
        let moved = r.metadata_of(lexical);
        assert_eq!(original.len(), 1);
        assert_eq!(moved.len(), 1);
        let ann = r.elements_of_metaclass("Annotation")[0];
        r.override_ids(&HashMap::from([(
            r.element_id(actual),
            ID.parse().unwrap(),
        )]));
        let mut hints = HashMap::from([(
            (r.element_id(ann), "annotatedElement".into()),
            ID.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        assert!(r.metadata_of(lexical).is_empty());
        assert_eq!(r.metadata_of(actual), [original, moved].concat());
        r.bind_id_spelled_references_with(&mut hints);
        assert_eq!(r.metadata_of(actual).len(), 2);
    }
}
#[test]
fn annotated_library_target_findings_belong_to_user_metadata_source() {
    let library = "standard library package KerML {metaclass Element; metaclass Type :> Element; metaclass Class :> Type; metaclass Feature :> Type;} standard library package Metaobjects {metaclass Metaobject {feature annotatedElement:KerML::Element;}} metaclass Tag :> Metaobjects::Metaobject {feature :>> annotatedElement:KerML::Feature;} class C;";
    for (model, mut r) in models_with(library, "@Tag about C;") {
        let findings = sysmlv2_parser::check::validate_semantics_with(&mut r, &model);
        let relevant = findings
            .iter()
            .filter(|(_, d)| {
                d.message
                    .contains("validateMetadataFeatureAnnotatedElement")
            })
            .collect::<Vec<_>>();
        assert_eq!(relevant.len(), 1, "{findings:?}");
        assert!(!model.is_library_unit(relevant[0].0));
        assert_eq!(model.unit(relevant[0].0).name, "about.kerml");
    }
}
