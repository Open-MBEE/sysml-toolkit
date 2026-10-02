//! Checked Type operation identities remain stable across library replay.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Vec<ElementRef> {
    let result = r.invoke_operation(receiver, operation, arguments).unwrap();
    let DerivedValue::References(values) = result.value else {
        panic!("expected Membership references");
    };
    values
        .into_iter()
        .map(|value| match value {
            Reference::Element(e) => e,
            _ => panic!("expected local Membership identity"),
        })
        .collect()
}

#[test]
fn type_membership_operations_preserve_actual_library_replay_and_exclusions() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut base = Model::with_graph_format(format);
        base.load_library_dir(&library).unwrap();
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(95).unwrap(), 95).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut model = Model::with_graph_format(format);
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.load_library_dir(&library).unwrap();
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            let source = "class A { feature original; feature retained; protected feature guarded; private feature hidden; alias Scalar for ScalarValues::Integer; } class B specializes A { feature replacement redefines original; feature own; }";
            let unit = model.add_source("type-memberships.kerml", source);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let a = r.resolve_qualified("A").unwrap();
            let b = r.resolve_qualified("B").unwrap();
            let original = r.resolve_qualified("A::original").unwrap();
            let retained = r.resolve_qualified("A::retained").unwrap();
            let guarded = r.resolve_qualified("A::guarded").unwrap();
            let hidden = r.resolve_qualified("A::hidden").unwrap();
            let membership = |r: &mut ResolvedModel, e| {
                let value = r.property(e, "owningRelationship").unwrap();
                r.element_by_id(value["@id"].as_str().unwrap()).unwrap()
            };
            let original = membership(&mut r, original);
            let retained = membership(&mut r, retained);
            let guarded = membership(&mut r, guarded);
            let hidden = membership(&mut r, hidden);
            let owned = r.property(a, "ownedMembership").unwrap();
            let scalar = owned
                .as_array()
                .unwrap()
                .iter()
                .find_map(|value| {
                    let member = r.element_by_id(value["@id"].as_str().unwrap()).unwrap();
                    (r.membership_member_name(member).as_deref() == Some("Scalar"))
                        .then_some(member)
                })
                .unwrap();
            assert!(r.membership_is_alias(scalar));
            let visible_args = [
                DerivedValue::Elements(vec![]),
                DerivedValue::Bool(false),
                DerivedValue::Bool(false),
            ];
            let visible = invoke(
                &mut r,
                b,
                "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
                &visible_args,
            );
            assert!(visible.contains(&retained));
            assert!(visible.contains(&scalar));
            assert!(!visible.contains(&guarded));
            assert!(!visible.contains(&hidden));
            let args = [
                DerivedValue::Elements(vec![]),
                DerivedValue::Elements(vec![]),
                DerivedValue::Bool(false),
            ];
            let inherited = invoke(
                &mut r,
                b,
                "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
                &args,
            );
            assert!(inherited.contains(&retained));
            assert!(inherited.contains(&scalar));
            assert!(inherited.contains(&guarded));
            assert!(!inherited.contains(&original));
            assert!(!inherited.contains(&hidden));
            let inheritable = invoke(
                &mut r,
                b,
                "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean",
                &args,
            );
            assert!(inheritable.contains(&original));
            let non_private = invoke(
                &mut r,
                b,
                "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean",
                &args,
            );
            assert!(inherited.iter().all(|e| non_private.contains(e)));
            let mut excluding = args.clone();
            excluding[0] = DerivedValue::Elements(vec![a]);
            assert_eq!(
                invoke(
                    &mut r,
                    b,
                    "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
                    &excluding,
                ),
                inherited,
                "Namespace exclusions affect imports, not ancestry"
            );
            excluding[1] = DerivedValue::Elements(vec![a]);
            let excluded = invoke(
                &mut r,
                b,
                "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
                &excluding,
            );
            assert!(!excluded.contains(&retained));
            assert!(!excluded.contains(&guarded));
            let ids: Vec<Vec<_>> = [inherited, inheritable, non_private, visible, excluded]
                .into_iter()
                .map(|values| values.into_iter().map(|e| r.element_id(e)).collect())
                .collect();
            if let Some(expected) = &expected {
                assert_eq!(&ids, expected, "{format:?} replay {mode}");
            } else {
                expected = Some(ids);
            }
        }
    }
}
