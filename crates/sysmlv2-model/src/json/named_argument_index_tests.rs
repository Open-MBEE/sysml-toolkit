//! Named argument redefinitions retain callee-context identity across replay.
use super::{ElementRef, ResolvedModel};
use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};
use std::{collections::HashMap, sync::Arc};
use uuid::Uuid;

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    let mut base = Model::new();
    assert!(
        base.add_library_source("arguments-library.kerml", library)
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
                    model.add_library_source("arguments-library.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(
                model
                    .add_source("arguments-user.kerml", user)
                    .diagnostics
                    .is_empty()
            );
            ResolvedModel::build(&model)
        })
        .collect()
}
fn argument(r: &mut ResolvedModel, name: &str) -> usize {
    let owner = r.resolve_qualified(name).unwrap().0;
    let value = r.b.elements[owner]
        .owned_relationships
        .iter()
        .copied()
        .find(|&r0| r.b.elements[r0].ty == "FeatureValue")
        .unwrap();
    let expression = r.b.elements[value].children[0];
    let membership = r.b.elements[expression]
        .owned_relationships
        .iter()
        .copied()
        .find(|&r0| r.b.elements[r0].ty == "ParameterMembership")
        .unwrap();
    r.b.elements[membership].children[0]
}
fn assert_target(r: &mut ResolvedModel, argument: usize, target: Option<usize>) {
    let recorded: Vec<_> =
        r.b.spec_targets
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.0 == argument && entry.1 == "Redefinition")
            .map(|(index, _)| index)
            .collect();
    assert_eq!(recorded.len(), 1);
    assert!(
        r.b.spec_resolved.get(recorded[0]).is_some(),
        "even a cached miss records an explicit outcome"
    );
    let expected: Vec<_> = target.into_iter().collect();
    assert_eq!(r.b.indexed_redefinition_targets(argument), expected);
    assert_eq!(r.b.redefinition_target_elems(argument), expected);
    assert_eq!(
        r.b.explicit_specialization_elems(argument),
        expected
            .iter()
            .map(|&e| ("Redefinition", e))
            .collect::<Vec<_>>()
    );
}

#[test]
fn named_argument_targets_keep_callee_context_through_replay_and_id_changes() {
    let library = "package Functions {function F {in x; return r;} feature sample=F(x=1); feature x; feature missing=Missing(x=2);}";
    let user = "function F {in x; return r;} alias invoke for F; feature byName=F(x=1); feature byAlias=invoke(x=2); class Point {feature x;} feature constructed=new Point(x=3); class Holder {feature fnMember:F;} feature h:Holder; feature chained=h.fnMember(x=4); feature x; feature missing=Missing(x=5); feature z; feature wrong=F(z=6); feature forward=late.fnMember(x=7); class Later {feature fnMember:F;} feature late:Later;";
    for mut r in models(library, user) {
        let f_x = r.resolve_qualified("F::x").unwrap().0;
        let point_x = r.resolve_qualified("Point::x").unwrap().0;
        let lib_x = r.resolve_qualified("Functions::F::x").unwrap().0;
        for (name, expected) in [
            ("byName", Some(f_x)),
            ("byAlias", Some(f_x)),
            ("chained", Some(f_x)),
            ("forward", Some(f_x)),
            ("constructed", Some(point_x)),
            ("Functions::sample", Some(lib_x)),
            ("missing", None),
            ("wrong", None),
            ("Functions::missing", None),
        ] {
            let parameter = argument(&mut r, name);
            assert_target(&mut r, parameter, expected);
        }
        // Fixed identities for arguments-user.kerml: specialization indexing
        // must preserve the argument subtree identities.
        for (name, parameter_id, membership_id, literal_id) in [
            (
                "byName",
                "19f667c2-50d4-5a3d-9fa8-0cb9c0869a00",
                "1c34a7a0-3e12-50cc-af2c-cfced1081b58",
                "f8b4a5e5-5ddb-557a-8d86-aaccb7980448",
            ),
            (
                "byAlias",
                "3f059e88-8e71-5720-b68f-f7c49ec73c9c",
                "c7fb9497-9683-5dd0-885f-16fe34d1e519",
                "5ff653a0-e0ab-5fbe-adc8-ea9d87e8807c",
            ),
            (
                "constructed",
                "b935e88c-28ec-50a6-9b98-0d1ea858abf5",
                "e2c650c1-e361-54d3-96f7-0c4a4a02abc1",
                "bb69e901-31af-5470-a9da-ea74d48f5d10",
            ),
            (
                "chained",
                "743949fb-acc8-5d50-9b20-5534dd82a62a",
                "7f4618ac-2696-5ccd-8aa7-a3fc5dbefd85",
                "b2c8557a-0391-538d-b00c-86592aec62f7",
            ),
            (
                "missing",
                "d95d365e-3029-5b1b-bdf4-915364f0a177",
                "8264348b-cbce-5728-b8e0-6303a5ea5ac9",
                "6a8b52c0-2825-5ce0-ac80-24493c3dea43",
            ),
            (
                "wrong",
                "2ea929c2-e8ac-5c2f-8710-23e31fbe7c4d",
                "11fbe8a7-26ab-5bd8-9380-8440d1b2bbc3",
                "b6eb3a88-402a-5b37-a4fa-b1766fce5f52",
            ),
        ] {
            let parameter = argument(&mut r, name);
            let membership = r.b.elements[parameter].owning_relationship.unwrap();
            let value = r.b.elements[parameter]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| r.b.elements[rel].ty == "FeatureValue")
                .unwrap();
            let literal = r.b.elements[value].children[0];
            assert_eq!(
                r.b.elements[parameter].id.to_string(),
                parameter_id,
                "{name}"
            );
            assert_eq!(
                r.b.elements[membership].id.to_string(),
                membership_id,
                "{name}"
            );
            assert_eq!(r.b.elements[literal].id.to_string(), literal_id, "{name}");
        }
        let parameter = argument(&mut r, "byName");
        r.override_ids(&HashMap::from([(
            r.element_id(ElementRef(f_x)),
            Uuid::new_v4(),
        )]));
        assert_target(&mut r, parameter, Some(f_x));
    }
}

#[test]
fn ambiguous_callee_parameter_does_not_bind_a_lexical_namesake() {
    for mut r in models(
        "package L;",
        "function F {in x; in x; return r;} feature x; feature call=F(x=1);",
    ) {
        let parameter = argument(&mut r, "call");
        assert_target(&mut r, parameter, None);
    }
}

#[test]
fn declaration_header_missing_outcome_cannot_capture_a_foreign_lexical_namesake() {
    for mut r in models(
        "package L;",
        "class A {feature x;} class C {feature y redefines x;} feature x;",
    ) {
        let y = r.resolve_qualified("C::y").unwrap().0;
        let lexical_x = r.resolve_qualified("x").unwrap().0;
        let index =
            r.b.spec_targets
                .iter()
                .position(|entry| entry.0 == y && entry.1 == "Redefinition")
                .unwrap();
        assert_eq!(r.b.spec_resolved.get(index), Some(&None));
        let (_, _, scope, qn) = r.b.spec_targets[index].clone();
        assert_eq!(
            r.b.resolve(scope, &qn, 0),
            Some(lexical_x),
            "ordinary fallback finds a different target than the original header context"
        );
        assert_target(&mut r, y, None);
    }
}

#[test]
fn source_spelled_callee_identity_rebinds_named_argument_context() {
    const ID: &str = "88888888-8888-4888-8888-888888888888";
    let source = format!(
        "function Actual {{in x; return r;}} function '{ID}' {{in x; return r;}} feature call='{ID}'(x=1);"
    );
    for mut r in models("package L;", &source) {
        let actual = r.resolve_qualified("Actual").unwrap();
        let actual_x = r.resolve_qualified("Actual::x").unwrap().0;
        let spelled_x = r.resolve_qualified(&format!("'{ID}'::x")).unwrap().0;
        let parameter = argument(&mut r, "call");
        assert_target(&mut r, parameter, Some(spelled_x));
        let call = r.resolve_qualified("call").unwrap();
        let expression = r.members_via(call, "FeatureValue")[0];
        let callee_membership = r
            .owned_relationships(expression)
            .into_iter()
            .find(|&edge| r.element_type(edge) == "Membership")
            .unwrap();
        r.override_ids(&HashMap::from([(
            r.element_id(actual),
            ID.parse().unwrap(),
        )]));
        let mut hints = HashMap::from([(
            (r.element_id(callee_membership), "memberElement".into()),
            ID.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        assert_target(&mut r, parameter, Some(actual_x));
        // A second source rebind must not resurrect the lexical namesake.
        r.bind_id_spelled_references_with(&mut hints);
        assert_target(&mut r, parameter, Some(actual_x));
    }
}
