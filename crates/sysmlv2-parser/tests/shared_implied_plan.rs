#![cfg(feature = "json")]

use std::collections::HashMap;
use sysmlv2_parser::{
    json::{ElementRef, ResolvedModel},
    model::Model,
};
use uuid::Uuid;

fn model(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_library_source(
        "parts.sysml",
        "standard library package Parts { part def Part; part parts; }",
    );
    model.add_source("user.sysml", source);
    assert!(!model.has_errors());
    ResolvedModel::build(&model)
}

fn target_ids(r: &mut ResolvedModel, e: ElementRef, key: &str) -> Vec<String> {
    r.implied_relationships(e)
        .into_iter()
        .filter_map(|rel| {
            r.element_properties(rel)
                .get(key)
                .and_then(|v| v.get("@id"))
                .and_then(|v| v.as_str())
                .map(str::to_owned)
        })
        .collect()
}

#[test]
fn shared_requirement_plan_rebuilds_after_explicit_id_override() {
    let mut r = model("package U { variation part def Choice { variant part option; } }");
    let choice = r.resolve_qualified("U::Choice").unwrap();
    let option = r.resolve_qualified("U::Choice::option").unwrap();
    r.inherited_memberships(option, true);
    let target = Uuid::parse_str("12340000-0000-4000-8000-000000000001").unwrap();
    r.override_ids(&HashMap::from([(r.element_id(choice), target)]));
    assert_eq!(target_ids(&mut r, option, "type"), [target.to_string()]);
}

#[test]
fn external_names_bypass_a_warm_loaded_library_requirement_plan() {
    let mut r = model("package U { part def P; }");
    let p = r.resolve_qualified("U::P").unwrap();
    r.inherited_memberships(p, true);
    let target = "12340000-0000-4000-8000-000000000002";
    r.set_library_names(&HashMap::from([(
        target.to_owned(),
        vec!["Parts".to_owned(), "Part".to_owned()],
    )]));
    assert_eq!(
        target_ids(&mut r, p, "superclassifier"),
        [target.to_owned()]
    );
}

#[test]
fn bound_references_recompute_requirement_reachability_after_a_warm_query() {
    let target = Uuid::parse_str("12340000-0000-4000-8000-000000000003").unwrap();
    let mut r = model(&format!(
        "package U {{ part def Base; part def Sub :> '{target}'; }}"
    ));
    let base = r.resolve_qualified("U::Base").unwrap();
    let sub = r.resolve_qualified("U::Sub").unwrap();
    r.override_ids(&HashMap::from([(r.element_id(base), target)]));
    r.inherited_memberships(sub, true);
    assert!(r.bind_id_spelled_references().contains(&target));
    assert!(
        target_ids(&mut r, sub, "superclassifier").is_empty(),
        "the now-resolved Base already reaches the required Part"
    );
    assert!(r.conforms_with_implied(sub, base));
}

#[test]
fn external_base_override_does_not_pair_against_the_loaded_library_base() {
    for warm in [false, true] {
        let mut source = Model::new();
        source.add_library_source(
            "parts.sysml",
            "standard library package Parts { part def Part { end part a; } part parts; }",
        );
        source.add_source("user.sysml", "package U { part def R { end part x; } }");
        assert!(!source.has_errors());
        let mut r = ResolvedModel::build(&source);
        let owner = r.resolve_qualified("U::R").unwrap();
        let x = r.resolve_qualified("U::R::x").unwrap();
        if warm {
            r.inherited_memberships(owner, true);
        }
        let target = "12340000-0000-4000-8000-000000000004";
        r.set_library_names(&HashMap::from([(
            target.to_owned(),
            vec!["Parts".to_owned(), "Part".to_owned()],
        )]));
        assert_eq!(
            target_ids(&mut r, owner, "superclassifier"),
            [target.to_owned()]
        );
        assert!(
            target_ids(&mut r, x, "redefinedFeature").is_empty(),
            "external base has unknown end ordering"
        );
    }
}

#[test]
fn in_model_base_override_supplies_the_positional_member_sequence() {
    let mut source = Model::new();
    source.add_library_source("parts.sysml", "standard library package Parts { part def Part { end part a; } part def Alternate { end part b; } part parts; }");
    source.add_source("user.sysml", "package U { part def R { end part x; } }");
    assert!(!source.has_errors());
    let mut r = ResolvedModel::build(&source);
    let owner = r.resolve_qualified("U::R").unwrap();
    let x = r.resolve_qualified("U::R::x").unwrap();
    let base = r.resolve_qualified("Parts::Alternate").unwrap();
    let b = r.resolve_qualified("Parts::Alternate::b").unwrap();
    r.set_library_names(&HashMap::from([(
        r.element_id(base).to_string(),
        vec!["Parts".to_owned(), "Part".to_owned()],
    )]));
    assert_eq!(
        target_ids(&mut r, owner, "superclassifier"),
        [r.element_id(base).to_string()]
    );
    assert_eq!(
        target_ids(&mut r, x, "redefinedFeature"),
        [r.element_id(b).to_string()]
    );
}

#[test]
fn library_identity_overrides_update_loaded_and_supplied_name_indexes() {
    for warm in [false, true] {
        for supplied in [false, true] {
            let mut r = model("package U { part def P; }");
            let base = r.resolve_qualified("Parts::Part").unwrap();
            let p = r.resolve_qualified("U::P").unwrap();
            let old = r.element_id(base);
            if supplied {
                r.set_library_names(&HashMap::from([(
                    old.to_string(),
                    vec!["Parts".into(), "Part".into()],
                )]));
            }
            if warm {
                r.inherited_memberships(p, true);
            }
            let new = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"remapped library general");
            r.override_ids(&HashMap::from([(old, new)]));
            assert_eq!(target_ids(&mut r, p, "superclassifier"), [new.to_string()]);
            assert!(r.conforms_with_implied(p, base));
        }
    }
}
