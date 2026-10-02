//! Typed facade regressions across navigation, export and replay.
#![cfg(feature = "json")]
use serde_json::json;
use std::collections::HashMap;
use sysmlv2_parser::{
    full::model_to_full_json,
    json::{
        ClosurePolicy, Derived, DerivedValue, OperationError, Reference, ResolvedModel,
        model_to_compact_json,
    },
    loader::load_document,
    model::Model,
};
fn model(text: &str) -> Model {
    let mut m = Model::new();
    let result = m.add_source("facade.sysml", text);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    m
}
#[test]
fn flow_interface_compositions_preserve_the_declared_target_type() {
    let m =
        model("part def D { flow f; interface i; ref x; } part d { flow f; interface i; ref x; }");
    let mut r = ResolvedModel::build(&m);
    let full = model_to_full_json(&m);
    for (name, flow, interface) in [
        ("D", "ownedFlow", "ownedInterface"),
        ("d", "nestedFlow", "nestedInterface"),
    ] {
        let owner = r.resolve_qualified(name).unwrap();
        let row = full
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["@id"] == r.element_id(owner).to_string())
            .unwrap();
        for (prop, member) in [(flow, "f"), (interface, "i")] {
            let child = r.resolve_qualified(&format!("{name}::{member}")).unwrap();
            let expected = json!([{"@id": r.element_id(child).to_string()}]);
            assert_eq!(r.property(owner, prop).unwrap(), expected, "{name}.{prop}");
            assert_eq!(row[prop], expected, "export {name}.{prop}");
        }
    }
}
#[test]
fn generic_reference_subsetting_does_not_name_anonymous_features() {
    let m = model("part a; connection connect a to a;");
    let compact = model_to_compact_json(&m);
    let mut r = ResolvedModel::build(&m);
    let refs: Vec<_> = r
        .elements()
        .filter(|&e| r.element_type(e) == "ReferenceUsage")
        .collect();
    assert_eq!(refs.len(), 2);
    // Connector ends have positional names, never the generic subset target's name.
    for e in refs {
        assert_ne!(r.element_effective_name(e).as_deref(), Some("a"));
    }
    let (_, mut replay, _, warnings) = load_document(&compact, &HashMap::new()).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    for e in r.user_elements().collect::<Vec<_>>() {
        let id = r.element_id(e).to_string();
        let other = replay.element_by_id(&id).unwrap();
        assert_eq!(
            r.element_effective_name(e),
            replay.element_effective_name(other)
        );
    }
}
#[test]
fn shorthand_succession_keeps_source_and_target_roles() {
    for text in [
        "state s { entry; then off; state off; }",
        "action a { action firstAction; attribute n; then lastAction; action lastAction; }",
    ] {
        let m = model(text);
        let compact = model_to_compact_json(&m);
        let mut r = ResolvedModel::build(&m);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let succession = r
            .elements()
            .find(|&e| r.element_type(e) == "SuccessionAsUsage")
            .unwrap();
        let (source, target) = r.relationship_ends(succession);
        assert_eq!(source.len(), 1, "{text}");
        assert_eq!(target.len(), 1, "{text}");
        assert_ne!(source, target);
        assert_eq!(
            r.derived(succession, "sourceFeature"),
            Derived::Value(DerivedValue::Reference(source[0].clone()))
        );
        assert_eq!(
            r.derived(succession, "targetFeature"),
            Derived::Value(DerivedValue::References(target))
        );
        assert_eq!(compact, model_to_compact_json(&m));
        assert!(
            r.implied_relationships(match source[0] {
                Reference::Element(e) => e,
                _ => panic!(),
            })
            .iter()
            .all(|&e| r.element_type(e) != "ReferenceSubsetting")
        );
    }
}
#[test]
fn absent_succession_source_does_not_shift_the_target() {
    let m = model("action a { then lastAction; action lastAction; }");
    let mut r = ResolvedModel::build(&m);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let succession = r
        .elements()
        .find(|&e| r.element_type(e) == "SuccessionAsUsage")
        .unwrap();
    let (source, target) = r.relationship_ends(succession);
    assert!(source.is_empty());
    assert_eq!(target.len(), 1);
}
#[test]
fn effective_name_operations_dispatch_and_refuse_uncertified_inheritance() {
    let m = model("package <p> P { part <x> named; part :> named; }");
    let mut r = ResolvedModel::build(&m);
    let name = "Root-Elements-Element-effectiveName_";
    let short = "Root-Elements-Element-effectiveShortName_";
    let p = r.resolve_qualified("P").unwrap();
    let x = r.resolve_qualified("P::named").unwrap();
    assert_eq!(
        r.invoke_operation(p, name, &[]).unwrap().value,
        DerivedValue::Str("P".into())
    );
    assert_eq!(
        r.invoke_operation(p, short, &[]).unwrap().value,
        DerivedValue::Str("p".into())
    );
    let result = r.invoke_operation(x, name, &[]).unwrap();
    assert_eq!(result.effective, "Core-Features-Feature-effectiveName_");
    assert_eq!(result.value, DerivedValue::Str("named".into()));
    let anonymous = r
        .elements()
        .find(|&e| {
            r.element_type(e) == "PartUsage"
                && r.element_properties(e)
                    .get("declaredName")
                    .is_none_or(|v| v.is_null())
        })
        .unwrap();
    assert!(matches!(
        r.invoke_operation(anonymous, name, &[]),
        Err(OperationError::Incomplete { .. })
    ));
}

#[test]
fn generic_reference_naming_is_null_across_public_readers_and_reload() {
    let mut m = Model::new();
    assert!(m.add_source("names.kerml", "feature <short> x; package Referenced {feature references x;} package Redefined {feature :>> x;} package Short {feature <s> :>> x;}").diagnostics.is_empty());
    let compact = model_to_compact_json(&m);
    let ids = sysmlv2_parser::ids::derive_ids(&compact, &|_| None).unwrap();
    for (row, id) in compact.as_array().unwrap().iter().zip(ids) {
        if let Some(id) = id {
            assert_eq!(row["@id"], id.to_string());
        }
    }
    let full = model_to_full_json(&m);
    let mut r = ResolvedModel::build(&m);
    for (owner, name, short) in [
        ("Referenced", json!(null), json!(null)),
        ("Redefined", json!("x"), json!("short")),
        ("Short", json!(null), json!("s")),
    ] {
        let parent = r.resolve_qualified(owner).unwrap();
        let e = match r.derived(parent, "ownedMember") {
            Derived::Value(v) => v.elements()[0],
            x => panic!("{x:?}"),
        };
        assert_eq!(r.property(e, "name").unwrap(), name);
        if name.is_null() && short.is_null() {
            assert!(r.element_qualified_name(e).is_none());
        }

        assert_eq!(r.property(e, "shortName").unwrap(), short);
        assert_eq!(
            r.element_effective_name(e),
            name.as_str().map(str::to_owned)
        );
        let id = r.element_id(e).to_string();
        let row = full
            .as_array()
            .unwrap()
            .iter()
            .find(|v| v["@id"] == id)
            .unwrap();
        assert_eq!(row["name"], name);
        assert_eq!(row["shortName"], short);
        for document in [&compact, &full] {
            let (_, mut replay, _, warnings) = load_document(document, &HashMap::new()).unwrap();
            assert!(warnings.is_empty(), "{warnings:?}");
            let target = replay.element_by_id(&id).unwrap();
            assert_eq!(replay.property(target, "name").unwrap(), name);
            assert_eq!(replay.property(target, "shortName").unwrap(), short);
        }
    }
}

#[test]
fn anonymous_reference_locators_replay_without_becoming_semantic_names() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "owner.sysml",
            "package P { part def D {attribute x;} part a : D {attribute ::> x = 1;} }"
        )
        .diagnostics
        .is_empty()
    );
    assert!(
        m.add_source("reader.sysml", "package Q { attribute result = P::a.x; }")
            .diagnostics
            .is_empty()
    );
    let compact = model_to_compact_json(&m);
    let full = model_to_full_json(&m);
    let mut r = ResolvedModel::build(&m);
    let anonymous = r
        .user_elements()
        .find(|&e| {
            r.element_type(e) == "AttributeUsage"
                && r.element_properties(e)
                    .get("declaredName")
                    .is_none_or(|v| v.is_null())
        })
        .unwrap();
    let id = r.element_id(anonymous).to_string();
    assert!(r.element_effective_name(anonymous).is_none());
    for document in [&compact, &full] {
        // Both documented public replay helpers must retain cross-document locators.
        for names in [
            sysmlv2_parser::lift::document_name_map(document),
            sysmlv2_parser::lift::document_reference_name_map(document),
        ] {
            assert!(names.contains_key(&id));
            let docs = sysmlv2_parser::lift::split_documents(document).unwrap();
            assert_eq!(docs.len(), 2);
            let mut restored = Model::new();
            for (i, (_, doc)) in docs.iter().enumerate() {
                let lifted =
                    sysmlv2_parser::lift::from_compact_json_with_names(doc, &names).unwrap();
                assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
                let source = sysmlv2_parser::print::print_source(&lifted.unit);
                assert!(
                    restored
                        .add_source(["owner.sysml", "reader.sysml"][i], &source)
                        .diagnostics
                        .is_empty()
                );
            }
            let mut replay = ResolvedModel::build(&restored);
            let target = replay.element_by_id(&id).unwrap();
            assert!(replay.element_effective_name(target).is_none());
            assert!(!replay.references_to(target).is_empty());
        }
        let (_, mut replay, _, warnings) = load_document(document, &HashMap::new()).unwrap();
        assert!(warnings.is_empty(), "{warnings:?}");
        let target = replay.element_by_id(&id).unwrap();
        assert!(replay.element_effective_name(target).is_none());
        let before = r.references_to(anonymous);
        let after = replay.references_to(target);
        assert!(!before.is_empty());
        let mut before_ids: Vec<_> = before
            .iter()
            .map(|site| (r.element_id(site.owner), site.kind.clone()))
            .collect();
        let mut after_ids: Vec<_> = after
            .iter()
            .map(|site| (replay.element_id(site.owner), site.kind.clone()))
            .collect();
        before_ids.sort();
        after_ids.sort();
        assert_eq!(before_ids, after_ids);
    }
}
