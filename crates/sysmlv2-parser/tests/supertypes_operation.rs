#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{
        ClosurePolicy, DerivedValue, OperationArgumentIssue, OperationError, Reference,
        ResolvedModel,
    },
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
use uuid::Uuid;
const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";
fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    models_named(library, user, "calls.kerml")
}
fn models_named(library: &str, user: &str, user_name: &str) -> Vec<(Model, ResolvedModel)> {
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
            assert!(model.add_source(user_name, user).diagnostics.is_empty());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

#[test]
fn explicit_direct_supertypes_preserve_order_conjugation_and_chain_identity() {
    for (model, mut r) in models(
        "package L {class A; class B;}",
        "class C specializes L::A,L::B; class D conjugates C; class E conjugates D; class T {feature x;} feature p:T; feature q chains p.x; class Missing specializes L::A,Unknown; class Duplicate specializes L::A,L::A;",
    ) {
        let loaded = model.loaded_library_unit_count();
        let a = r.resolve_qualified("L::A").unwrap();
        let b = r.resolve_qualified("L::B").unwrap();
        let c = r.resolve_qualified("C").unwrap();
        let d = r.resolve_qualified("D").unwrap();
        let e = r.resolve_qualified("E").unwrap();
        let p = r.resolve_qualified("p").unwrap();
        let t = r.resolve_qualified("T").unwrap();
        let q = r.resolve_qualified("q").unwrap();
        let x = r.resolve_qualified("T::x").unwrap();
        let before: Vec<_> = r
            .user_elements()
            .map(|e| {
                (
                    r.element_id(e),
                    r.element_properties(e),
                    r.owned_relationships(e),
                )
            })
            .collect();
        for policy in [
            ClosurePolicy::Passthrough,
            ClosurePolicy::Closure {
                include_implied: false,
            },
            ClosurePolicy::Closure {
                include_implied: true,
            },
        ] {
            r.set_closure_policy(policy);
            for _ in 0..2 {
                for (receiver, targets) in [
                    (a, vec![]),
                    (c, vec![a, b]),
                    (d, vec![c]),
                    (e, vec![d]),
                    (p, vec![t]),
                    (q, vec![x]),
                ] {
                    let result = r
                        .invoke_operation(receiver, SUPERTYPES, &[DerivedValue::Bool(true)])
                        .unwrap();
                    assert_eq!(
                        result.value,
                        DerivedValue::References(
                            targets.into_iter().map(Reference::Element).collect()
                        )
                    );
                    if receiver == q {
                        assert_eq!(result.effective, "Core-Features-Feature-supertypes_Boolean");
                    }
                }
            }
            for (receiver, target) in [(d, c), (e, d)] {
                assert_eq!(
                    r.invoke_operation(receiver, SUPERTYPES, &[DerivedValue::Bool(false)])
                        .unwrap()
                        .value,
                    DerivedValue::References(vec![Reference::Element(target)])
                );
            }
            for name in ["Missing", "Duplicate"] {
                let receiver = r.resolve_qualified(name).unwrap();
                assert!(matches!(
                    r.invoke_operation(receiver, SUPERTYPES, &[DerivedValue::Bool(true)]),
                    Err(OperationError::Incomplete { .. })
                ));
            }
            assert!(matches!(
                r.invoke_operation(c, SUPERTYPES, &[DerivedValue::Bool(false)]),
                Err(OperationError::UnsupportedConfiguration { .. })
            ));
            assert!(matches!(
                r.invoke_operation(c, SUPERTYPES, &[DerivedValue::Str("true".into())]),
                Err(OperationError::InvalidArgument {
                    issue: OperationArgumentIssue::WrongShape,
                    ..
                })
            ));
            assert!(matches!(
                r.invoke_operation(c, SUPERTYPES, &[DerivedValue::Null]),
                Err(OperationError::InvalidArgument {
                    issue: OperationArgumentIssue::NullNotAllowed,
                    ..
                })
            ));
        }
        let after: Vec<_> = r
            .user_elements()
            .map(|e| {
                (
                    r.element_id(e),
                    r.element_properties(e),
                    r.owned_relationships(e),
                )
            })
            .collect();
        assert_eq!(before, after);
        let id = Uuid::new_v4();
        r.override_ids(&HashMap::from([(r.element_id(a), id)]));
        assert_eq!(
            r.invoke_operation(c, SUPERTYPES, &[DerivedValue::Bool(true)])
                .unwrap()
                .value,
            DerivedValue::References(vec![Reference::Element(a), Reference::Element(b)])
        );
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
