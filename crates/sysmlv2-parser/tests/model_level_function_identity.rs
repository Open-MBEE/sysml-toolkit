//! Designated model-level function identities from KerML Tables 5 and 7.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{Derived, DerivedValue, ElementRef, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
use uuid::Uuid;

// Normative table rows, independent of the implementation's dispatch.
const ELIGIBLE: &[(&str, &[&str])] = &[
    (
        "BaseFunctions",
        &[
            "istype", "hastype", "@", "@@", "as", "meta", "==", "!=", "===", "!==", "#", ",",
        ],
    ),
    (
        "DataFunctions",
        &[
            "xor", "not", "|", "&", "<", ">", "<=", ">=", "+", "-", "*", "/", "%", "^", "..",
        ],
    ),
    (
        "ControlFunctions",
        &["??", "if", "or", "and", "implies", ".", "collect", "select"],
    ),
];

fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    assert!(
        base.add_library_source("functions.kerml", library)
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
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("functions.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(model.add_source("calls.kerml", user).diagnostics.is_empty());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}
fn evaluable(r: &mut ResolvedModel, e: ElementRef) -> bool {
    match r.derived(e, "isModelLevelEvaluable") {
        Derived::Value(DerivedValue::Bool(value)) => value,
        other => panic!("unexpected evaluability result: {other:?}"),
    }
}
fn value(r: &mut ResolvedModel, owner: &str) -> ElementRef {
    let e = r.resolve_qualified(owner).unwrap();
    let fv = r
        .owned_relationships(e)
        .into_iter()
        .find(|&rel| r.element_type(rel) == "FeatureValue")
        .unwrap();
    match r.derived(fv, "value") {
        Derived::Value(value) => value.element().unwrap(),
        other => panic!("unexpected feature value: {other:?}"),
    }
}

#[test]
fn designated_function_table_and_exclusions_survive_all_library_representations() {
    let mut library = String::new();
    for &(package, names) in ELIGIBLE {
        library.push_str(&format!("package {package} {{"));
        for name in names {
            library.push_str(&format!(" function '{name}' {{ in x; return r; }}"));
        }
        library.push_str(" function custom { in x; return r; } package Nested { function '+' { in x; return r; } }");
        for name in match package {
            "BaseFunctions" => &["all", "["][..],
            "DataFunctions" => &["~"][..],
            _ => &[][..],
        } {
            library.push_str(&format!(" function '{name}' {{ in x; return r; }}"));
        }
        library.push('}');
    }
    let user = "package U { alias plus for DataFunctions::'+'; feature p=plus(1); feature arbitrary=DataFunctions::custom(1); feature n=~1; feature bracket=1[2]; class T; feature extent=all T; }";
    for (model, mut r) in models(&library, user) {
        let loaded = model.loaded_library_unit_count();
        for _ in 0..2 {
            for &(package, names) in ELIGIBLE {
                for name in names {
                    let qn = format!("{package}::'{name}'");
                    let e = r.resolve_qualified(&qn).unwrap();
                    assert!(evaluable(&mut r, e), "{qn}");
                }
                for tail in ["custom", "Nested::'+'"] {
                    let qn = format!("{package}::{tail}");
                    let e = r.resolve_qualified(&qn).unwrap();
                    assert!(!evaluable(&mut r, e), "{qn}");
                }
            }
            for qn in [
                "BaseFunctions::'all'",
                "BaseFunctions::'['",
                "DataFunctions::'~'",
            ] {
                let e = r.resolve_qualified(qn).unwrap();
                assert!(!evaluable(&mut r, e), "{qn}");
            }
            for (qn, expected) in [
                ("U::p", true),
                ("U::arbitrary", false),
                ("U::n", false),
                ("U::bracket", false),
                ("U::extent", false),
            ] {
                let expr = value(&mut r, qn);
                assert_eq!(evaluable(&mut r, expr), expected, "{qn}");
            }
        }
        let plus = r.resolve_qualified("DataFunctions::'+'").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(plus), Uuid::new_v4())]));
        let expr = value(&mut r, "U::p");
        assert!(evaluable(&mut r, expr));
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn external_operator_identities_use_exact_designated_names() {
    let mut model = Model::new();
    assert!(
        model
            .add_source(
                "external.kerml",
                "class T; feature p=1+2; feature n=~1; feature bracket=1[2]; feature extent=all T;"
            )
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&model);
    let plus = value(&mut r, "p");
    assert!(!evaluable(&mut r, plus));
    let names = [
        ("DataFunctions", "+"),
        ("DataFunctions", "~"),
        ("BaseFunctions", "["),
        ("BaseFunctions", "all"),
    ]
    .into_iter()
    .map(|(package, name)| {
        (
            Uuid::new_v4().to_string(),
            vec![package.to_string(), name.to_string()],
        )
    })
    .collect();
    r.set_library_names(&names);
    for (name, expected) in [
        ("p", true),
        ("n", false),
        ("bracket", false),
        ("extent", false),
    ] {
        let expr = value(&mut r, name);
        assert_eq!(evaluable(&mut r, expr), expected, "{name}");
    }
    r.set_library_names(&HashMap::from([(
        Uuid::new_v4().to_string(),
        vec!["DataFunctions".into(), "Nested".into(), "+".into()],
    )]));
    assert!(!evaluable(&mut r, plus));
}

#[test]
fn spelling_does_not_designate_user_functions_or_wrong_library_metaclasses() {
    let mut model = Model::new();
    assert!(model.add_source("user.kerml", "package DataFunctions { function '+' { in x; return r; } } feature p=DataFunctions::'+'(1);").diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let plus = r.resolve_qualified("DataFunctions::'+'").unwrap();
    assert!(!evaluable(&mut r, plus));
    let expr = value(&mut r, "p");
    assert!(!evaluable(&mut r, expr));
    for (_, mut r) in models("package DataFunctions { class '+'; }", "feature p=1+2;") {
        let expr = value(&mut r, "p");
        assert!(!evaluable(&mut r, expr));
    }
}

#[test]
fn exponentiation_spellings_resolve_to_the_same_designated_function() {
    for (_, mut r) in models(
        "package DataFunctions { function '^' { in x; in y; return r; } }",
        "feature caret=2^3; feature stars=2**3;",
    ) {
        let function = r.resolve_qualified("DataFunctions::'^'").unwrap();
        for name in ["caret", "stars"] {
            let expression = value(&mut r, name);
            assert!(evaluable(&mut r, expression));
            assert_eq!(
                r.derived(expression, "instantiatedType"),
                Derived::Value(DerivedValue::Reference(
                    sysmlv2_parser::json::Reference::Element(function)
                ))
            );
        }
    }
}

#[test]
fn conflicting_external_names_cannot_prove_operator_evaluability() {
    let mut model = Model::new();
    model.add_source("external.kerml", "feature p=1+2;");
    let mut r = ResolvedModel::build(&model);
    let expression = value(&mut r, "p");
    let first = Uuid::from_u128(0xabcdef00123456781234567812345678);
    let second = Uuid::from_u128(0xabcdef00123456781234567812345679);
    for _ in 0..4 {
        r.set_library_names(&HashMap::from([
            (first.to_string(), vec!["DataFunctions".into(), "+".into()]),
            (second.to_string(), vec!["DataFunctions".into(), "+".into()]),
        ]));
        assert!(!evaluable(&mut r, expression));
        r.set_library_names(&HashMap::from([(
            first.to_string(),
            vec!["DataFunctions".into(), "+".into()],
        )]));
        assert!(evaluable(&mut r, expression));
        // Distinct source keys can normalize to the same UUID. Conflicting
        // provenance must not depend on which spelling is visited last.
        r.set_library_names(&HashMap::from([
            (first.to_string(), vec!["DataFunctions".into(), "+".into()]),
            (
                first.to_string().to_uppercase(),
                vec!["Other".into(), "+".into()],
            ),
        ]));
        assert!(!evaluable(&mut r, expression));
    }
}

#[test]
fn ambiguous_loaded_function_does_not_fall_back_to_external_identity() {
    for (_, mut r) in models(
        "package DataFunctions { function '+' { in x; return r; } function '+' { in x; return r; } }",
        "feature p=1+2;",
    ) {
        assert!(r.resolve_qualified("DataFunctions::'+'").is_none());
        r.set_library_names(&HashMap::from([(
            Uuid::new_v4().to_string(),
            vec!["DataFunctions".into(), "+".into()],
        )]));
        let expression = value(&mut r, "p");
        assert!(!evaluable(&mut r, expression));
    }
}

#[test]
fn external_name_table_cannot_relabel_an_in_model_declaration() {
    for (_, mut r) in models(
        "package Other { class C; function F { in x; return r; } }",
        "feature p=1+2;",
    ) {
        for qn in ["Other::C", "Other::F"] {
            let target = r.resolve_qualified(qn).unwrap();
            r.set_library_names(&HashMap::from([(
                r.element_id(target).to_string(),
                vec!["DataFunctions".into(), "+".into()],
            )]));
            let expression = value(&mut r, "p");
            assert!(!evaluable(&mut r, expression));
            let replacement = Uuid::new_v4();
            r.override_ids(&HashMap::from([(r.element_id(target), replacement)]));
            assert!(!evaluable(&mut r, expression));
        }
    }
}
