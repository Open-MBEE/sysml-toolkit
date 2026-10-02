//! Checked Usage definitions reuse the complete Feature typing closure.
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel},
    model::{GraphFormat, Model},
};

#[test]
fn structural_usage_types_and_definition_subsets_use_the_real_library() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        // Attribute library aliases do not yet provide retained implied paths;
        // explicit canonical heritage keeps this test about the checked reader.
        let unit = model.add_source(
            "typing.sysml",
            "package P {
            part def Module;
            part def Vehicle { ref part camera : Module; part compositeCamera : Module; }
            part vehicle : Vehicle { part camera : Module { part sensor : Module; } }
            occurrence def Event;
            part def Carrier { item component : ItemType; occurrence happening : Event; }
            ref part standalone : Module;
            item def ItemType;
            ref item component : ItemType;
            ref part mixed : ItemType;
            ref occurrence occurrenceValue : Event;
            attribute def Data :> Base::DataValue;
            ref attribute data : Data :> Base::dataValues;
        }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        for (path, target, properties) in [
            (
                "P::Vehicle::camera",
                "P::Module",
                &[
                    "type",
                    "definition",
                    "occurrenceDefinition",
                    "itemDefinition",
                    "partDefinition",
                ][..],
            ),
            (
                "P::standalone",
                "P::Module",
                &["type", "partDefinition"][..],
            ),
            (
                "P::component",
                "P::ItemType",
                &["type", "definition", "itemDefinition"][..],
            ),
            (
                "P::occurrenceValue",
                "P::Event",
                &["type", "definition", "occurrenceDefinition"][..],
            ),
            (
                "P::data",
                "P::Data",
                &["type", "definition", "attributeDefinition"][..],
            ),
        ] {
            let e = r.resolve_qualified(path).unwrap();
            let target = r.resolve_qualified(target).unwrap();
            let expected = serde_json::json!([{"@id": r.element_id(target).to_string()}]);
            for property in properties {
                assert_eq!(
                    r.property(e, property),
                    Ok(expected.clone()),
                    "{format:?} {path}.{property}"
                );
            }
        }
        let mixed = r.resolve_qualified("P::mixed").unwrap();
        let part = r.resolve_qualified("Parts::Part").unwrap();
        assert_eq!(
            r.property(mixed, "partDefinition"),
            Ok(serde_json::json!([{"@id": r.element_id(part).to_string()}]))
        );
        assert_eq!(
            r.property(mixed, "itemDefinition")
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            2
        );
        for (path, target) in [
            ("P::Vehicle::compositeCamera", "P::Module"),
            ("P::vehicle::camera", "P::Module"),
            ("P::vehicle::camera::sensor", "P::Module"),
            ("P::Carrier::component", "P::ItemType"),
            ("P::Carrier::happening", "P::Event"),
        ] {
            let composite = r.resolve_qualified(path).unwrap();
            let target = r.resolve_qualified(target).unwrap();
            assert_eq!(
                r.feature_type_report(composite).types,
                Ok(vec![target]),
                "{format:?} {path}"
            );
            assert_eq!(
                r.property(composite, "definition"),
                Ok(serde_json::json!([{"@id": r.element_id(target).to_string()}]))
            );
        }
    }
}

fn small_library(parts: &str) -> Model {
    let mut model = Model::new();
    for (name, text) in [
        (
            "kernel.kerml",
            "standard library package Base { classifier Anything; feature things : Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; } standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; }",
        ),
        (
            "items.sysml",
            "standard library package Items { item def Item :> Objects::Object; ref item items : Item :> Objects::objects; }",
        ),
        ("parts.sysml", parts),
    ] {
        let unit = model.add_library_source(name, text);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    }
    model
}

#[test]
fn checked_usage_typing_replays_and_preserves_policy_and_incomplete_refusals() {
    use std::sync::Arc;
    use sysmlv2_parser::prepared::PreparedLibrary;
    const PARTS: &str = "standard library package Parts { part def Part :> Items::Item; ref part parts : Part :> Items::items; }";
    let mut library = small_library(PARTS);
    let prepared = library.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(137).unwrap(), 137).unwrap());
    let mut expected_ids = None;
    for mode in 0..3 {
        let mut model = match mode {
            0 => small_library(PARTS),
            _ => {
                let mut model = Model::new();
                Arc::clone(if mode == 1 { &prepared } else { &decoded })
                    .install(&mut model)
                    .unwrap();
                model
            }
        };
        assert!(model.add_source("user.sysml", "part def Module; part def Container { ref part camera : Module; part compositeCamera : Module; } part outer { ref part nested : Module; } ref part broken : Missing; ").diagnostics.is_empty());
        let mut r = ResolvedModel::build(&model);
        let camera = r.resolve_qualified("Container::camera").unwrap();
        let module = r.resolve_qualified("Module").unwrap();
        let ids = (r.element_id(camera), r.element_id(module));
        assert_eq!(*expected_ids.get_or_insert(ids), ids);
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
            for property in ["type", "definition", "itemDefinition", "partDefinition"] {
                let value = r.property(camera, property);
                if policy
                    == (ClosurePolicy::Closure {
                        include_implied: true,
                    })
                {
                    assert_eq!(
                        value,
                        Ok(serde_json::json!([{"@id": ids.1.to_string()}])),
                        "mode {mode} {property}"
                    );
                } else {
                    assert_eq!(value, Err(sysmlv2_parser::json::PropertyError::Approximate));
                }
            }
        }
        for path in ["Container::compositeCamera", "outer::nested", "broken"] {
            let e = r.resolve_qualified(path).unwrap();
            assert!(r.property(e, "type").is_err(), "{path}");
            assert!(r.property(e, "partDefinition").is_err(), "{path}");
        }
    }
    // A direct authored typing cannot replace the canonical family witness.
    let mut model =
        small_library("standard library package Parts { part def Part :> Items::Item; }");
    model.add_source(
        "missing-role.sysml",
        "part def Module; ref part camera : Module;",
    );
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let camera = r.resolve_qualified("camera").unwrap();
    assert!(r.property(camera, "type").is_err());
    assert!(r.property(camera, "partDefinition").is_err());
}

const COMPOSITE_KERNEL: &str = "standard library package Base { classifier Anything; feature things : Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything { composite feature suboccurrences : Occurrence subsets occurrences; } feature occurrences : Occurrence subsets Base::things; } standard library package Objects { struct Object specializes Occurrences::Occurrence { composite feature subobjects : Object subsets objects, Occurrences::Occurrence::suboccurrences intersects objects, Occurrences::Occurrence::suboccurrences; } feature objects : Object subsets Occurrences::occurrences; }";
const COMPOSITE_ITEMS: &str = "standard library package Items { item def Item :> Objects::Object { item subitems : Item :> items, Objects::Object::subobjects; part subparts : Parts::Part :> subitems, Parts::parts; } ref item items : Item :> Objects::objects; } standard library package Parts { part def Part :> Items::Item; ref part parts : Part :> Items::items; }";
fn composite_library(format: GraphFormat, kernel: &str, items: &str) -> Model {
    let mut model = Model::with_graph_format(format);
    for (name, text) in [("kernel.kerml", kernel), ("items.sysml", items)] {
        let parsed = model.add_library_source(name, text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    }
    model
}
#[test]
fn composite_usage_typing_replays_and_is_independent_of_query_order() {
    use std::sync::Arc;
    use sysmlv2_parser::prepared::PreparedLibrary;
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut library = composite_library(format, COMPOSITE_KERNEL, COMPOSITE_ITEMS);
        let prepared = library.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(138).unwrap(), 138).unwrap());
        let mut expected = None;
        for mode in 0..3 {
            for warm in [false, true] {
                let mut model = if mode == 0 {
                    composite_library(format, COMPOSITE_KERNEL, COMPOSITE_ITEMS)
                } else {
                    let mut model = Model::with_graph_format(format);
                    Arc::clone(if mode == 1 { &prepared } else { &decoded })
                        .install(&mut model)
                        .unwrap();
                    model
                };
                let parsed = model.add_source("composite.sysml", "part def Module; part def Container { part camera : Module; } part outer { part nested : Module; } part def Bad { part broken : Missing; }");
                assert!(parsed.diagnostics.is_empty());
                let mut r = ResolvedModel::build(&model);
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let container = r.resolve_qualified("Container").unwrap();
                let camera = r.resolve_qualified("Container::camera").unwrap();
                let module = r.resolve_qualified("Module").unwrap();
                if warm {
                    let _ = r.property(container, "inheritedFeature");
                    let _ = r.property(camera, "ownedRelationship");
                }
                let nested = r.resolve_qualified("outer::nested").unwrap();
                assert_eq!(r.feature_type_report(nested).types, Ok(vec![module]));
                for property in [
                    "type",
                    "definition",
                    "occurrenceDefinition",
                    "itemDefinition",
                    "partDefinition",
                ] {
                    let value = r.property(camera, property).unwrap();
                    assert_eq!(
                        value,
                        serde_json::json!([{"@id": r.element_id(module).to_string()}])
                    );
                    assert_eq!(
                        expected.get_or_insert_with(|| value.clone()),
                        &value,
                        "{format:?} {mode} {warm}"
                    );
                }
                let broken = r.resolve_qualified("Bad::broken").unwrap();
                assert!(r.property(broken, "type").is_err());
                for policy in [
                    ClosurePolicy::Passthrough,
                    ClosurePolicy::Closure {
                        include_implied: false,
                    },
                ] {
                    r.set_closure_policy(policy);
                    assert!(r.property(camera, "type").is_err());
                }
            }
        }
    }
}
#[test]
fn composite_typing_requires_canonical_composition_paths_and_redundant_intersections() {
    for (kernel, items) in [
        (
            COMPOSITE_KERNEL.to_owned(),
            COMPOSITE_ITEMS.replace("part subparts", "part missingSubparts"),
        ),
        (
            COMPOSITE_KERNEL.to_owned(),
            COMPOSITE_ITEMS.replace("part subparts", "item subparts"),
        ),
        (
            COMPOSITE_KERNEL.replace(
                "subsets objects, Occurrences::Occurrence::suboccurrences intersects",
                "subsets objects intersects",
            ),
            COMPOSITE_ITEMS.to_owned(),
        ),
        (
            COMPOSITE_KERNEL.replace(
                "intersects objects, Occurrences::Occurrence::suboccurrences",
                "intersects objects, Missing",
            ),
            COMPOSITE_ITEMS.to_owned(),
        ),
    ] {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut model = composite_library(format, &kernel, &items);
            model.add_source(
                "refusal.sysml",
                "part def Module; part def Container { part camera : Module; } part outer : Module { part camera : Module; }",
            );
            let mut r = ResolvedModel::build(&model);
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            let camera = r.resolve_qualified("Container::camera").unwrap();
            assert!(
                r.property(camera, "type").is_err(),
                "{format:?} {kernel} {items}"
            );
            assert!(r.property(camera, "partDefinition").is_err());
            let nested = r.resolve_qualified("outer::camera").unwrap();
            assert!(r.property(nested, "type").is_err());
        }
    }
}

#[test]
fn nested_composite_typing_uses_complete_owner_types_across_replay() {
    use std::sync::Arc;
    use sysmlv2_parser::prepared::PreparedLibrary;
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut base = composite_library(format, COMPOSITE_KERNEL, COMPOSITE_ITEMS);
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(139).unwrap(), 139).unwrap());
        for mode in 0..3 {
            for warm in [false, true] {
                let mut model = if mode == 0 {
                    composite_library(format, COMPOSITE_KERNEL, COMPOSITE_ITEMS)
                } else {
                    let mut model = Model::with_graph_format(format);
                    Arc::clone(if mode == 1 { &prepared } else { &decoded })
                        .install(&mut model)
                        .unwrap();
                    model
                };
                let parsed = model.add_source(
                    "nested.sysml",
                    "
                    part def Module; item def ItemType; occurrence def Event;
                    part outer : Module { part inner : Module { part sensor : Module; } }
                    item items : ItemType { item inner : ItemType; }
                    occurrence events : Event { occurrence inner : Event; }
                    part broken : Missing { part inner : Module; }
                    part valued : Module = 1 { part inner : Module; }
                    variation part varying : Module { part inner : Module; }
                ",
                );
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                let mut r = ResolvedModel::build(&model);
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                for (path, target) in [
                    ("outer::inner", "Module"),
                    ("outer::inner::sensor", "Module"),
                    ("items::inner", "ItemType"),
                    ("events::inner", "Event"),
                ] {
                    let e = r.resolve_qualified(path).unwrap();
                    let target = r.resolve_qualified(target).unwrap();
                    if warm {
                        let _ = r.property(e, "owningType");
                        let _ = r.property(e, "ownedRelationship");
                    }
                    assert_eq!(
                        r.feature_type_report(e).types,
                        Ok(vec![target]),
                        "{format:?} {mode} {warm} {path}"
                    );
                    assert_eq!(
                        r.property(e, "definition"),
                        Ok(serde_json::json!([{"@id":r.element_id(target).to_string()}]))
                    );
                }
                for path in ["broken::inner", "valued::inner", "varying::inner"] {
                    let e = r.resolve_qualified(path).unwrap();
                    assert!(r.property(e, "type").is_err(), "{format:?} {mode} {path}");
                }
            }
        }
    }
}
