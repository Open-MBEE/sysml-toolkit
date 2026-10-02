//! Declaration-identity operation invocation is distinct from scalar evaluation.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{
        ClosurePolicy, Derived, DerivedValue, ElementRef, OperationArgumentIssue, OperationError,
        Reference, ResolvedModel, operation_execution_signature,
    },
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
use uuid::Uuid;
const EVALUATE: &str = "Kernel-Functions-Expression-evaluate_Element";
const ELIGIBLE: &str = "Kernel-Functions-Expression-modelLevelEvaluable_Feature";
const DIRECTION: &str = "Kernel-Behaviors-ParameterMembership-parameterDirection_";
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

fn value(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let feature = r.resolve_qualified(name).unwrap();
    let relation = r
        .owned_relationships(feature)
        .into_iter()
        .find(|&r0| r.element_type(r0) == "FeatureValue")
        .unwrap();
    match r.derived(relation, "value") {
        Derived::Value(v) => v.element().unwrap(),
        value => panic!("{value:?}"),
    }
}

#[test]
fn constant_families_preserve_identity_order_and_empty_results_across_replay_modes() {
    let user = r#"class T; feature target; feature i=1; feature b=true; feature real=1.5; feature text="s"; feature inf=*; feature n=null; feature m=T.metadata; function F {in x; return r;} feature call=F(1);"#;
    for (model, mut r) in models("package L {classifier T;}", user) {
        let loaded = model.loaded_library_unit_count();
        let target = r.resolve_qualified("target").unwrap();
        let function = r.resolve_qualified("F").unwrap();
        let parameters = r.owned_relationships(function);
        let call = value(&mut r, "call");
        let parameter = r
            .owned_relationships(call)
            .into_iter()
            .find(|&e| r.element_type(e) == "ParameterMembership")
            .unwrap();
        let return_ = *parameters
            .iter()
            .find(|&&e| r.element_type(e) == "ReturnParameterMembership")
            .unwrap();
        let expressions: Vec<_> = ["i", "b", "real", "text", "inf", "n", "m"]
            .into_iter()
            .map(|name| (name, value(&mut r, name)))
            .collect();
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
                assert_eq!(
                    r.invoke_operation(parameter, DIRECTION, &[]).unwrap().value,
                    DerivedValue::Str("in".into())
                );
                let output = r.invoke_operation(return_, DIRECTION, &[]).unwrap();
                assert_eq!(
                    output.effective,
                    "Kernel-Functions-ReturnParameterMembership-parameterDirection_"
                );
                assert_eq!(output.value, DerivedValue::Str("out".into()));
                for &(name, expression) in &expressions {
                    let eligible = r
                        .invoke_operation(
                            expression,
                            ELIGIBLE,
                            &[DerivedValue::Elements(vec![target])],
                        )
                        .unwrap();
                    assert_eq!(eligible.value, DerivedValue::Bool(true), "{name}");
                    if name == "m" {
                        assert!(matches!(
                            r.invoke_operation(
                                expression,
                                EVALUATE,
                                &[DerivedValue::Element(target)]
                            ),
                            Err(OperationError::Unsupported {
                                effective: "Kernel-Expressions-MetadataAccessExpression-evaluate_Element"
                            })
                        ));
                    } else {
                        let output = r
                            .invoke_operation(
                                expression,
                                EVALUATE,
                                &[DerivedValue::Element(target)],
                            )
                            .unwrap();
                        assert_eq!(output.requested, EVALUATE);
                        assert_eq!(
                            output.value,
                            DerivedValue::References(if name == "n" {
                                vec![]
                            } else {
                                vec![Reference::Element(expression)]
                            })
                        );
                    }
                }
            }
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
        assert_eq!(after, before);
        let integer = expressions[0].1;
        let id = Uuid::new_v4();
        r.override_ids(&HashMap::from([(r.element_id(integer), id)]));
        let result = r
            .invoke_operation(
                integer,
                EVALUATE,
                &[DerivedValue::Reference(Reference::Element(target))],
            )
            .unwrap();
        assert_eq!(
            result.value,
            DerivedValue::References(vec![Reference::Element(integer)])
        );
        assert_eq!(r.element_id(integer), id);
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
#[test]
fn overridden_sysml_constants_are_negative_and_do_not_fall_back() {
    for (_, mut r) in models_named(
        "package L;",
        "calc def F {return r;} calc c:F; constraint def R; constraint r:R;",
        "ops.sysml",
    ) {
        for name in ["c", "r"] {
            let e = r.resolve_qualified(name).unwrap();
            assert_eq!(
                r.invoke_operation(e, ELIGIBLE, &[DerivedValue::Elements(vec![])])
                    .unwrap()
                    .value,
                DerivedValue::Bool(false)
            );
        }
    }
}
#[test]
fn checked_arguments_are_validated_even_for_constant_bodies() {
    for (_, mut r) in models(
        "package L;",
        "class T; feature f; feature i=1; feature n=null;",
    ) {
        let i = value(&mut r, "i");
        let n = value(&mut r, "n");
        let t = r.resolve_qualified("T").unwrap();
        let f = r.resolve_qualified("f").unwrap();
        assert_eq!(
            r.invoke_operation(i, "evaluate", &[]),
            Err(OperationError::UnknownOperation)
        );
        assert!(matches!(
            r.invoke_operation(t, EVALUATE, &[]),
            Err(OperationError::WrongReceiver { .. })
        ));
        assert!(matches!(
            r.invoke_operation(i, EVALUATE, &[]),
            Err(OperationError::ArgumentCount {
                expected: 1,
                actual: 0
            })
        ));
        assert!(matches!(
            r.invoke_operation(n, EVALUATE, &[DerivedValue::Null]),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::NullNotAllowed,
                ..
            })
        ));
        assert!(matches!(
            r.invoke_operation(i, ELIGIBLE, &[DerivedValue::Element(f)]),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::WrongShape,
                ..
            })
        ));
        assert!(matches!(
            r.invoke_operation(i, ELIGIBLE, &[DerivedValue::Elements(vec![t])]),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::WrongMetaclass {
                    expected: "Feature",
                    ..
                },
                ..
            })
        ));
        assert!(matches!(
            r.invoke_operation(i, ELIGIBLE, &[DerivedValue::Elements(vec![f, f])]),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::DuplicateIdentity,
                ..
            })
        ));
        for reference in [
            Reference::External(Uuid::new_v4()),
            Reference::Unresolved("Missing".into()),
        ] {
            assert!(matches!(
                r.invoke_operation(i, EVALUATE, &[DerivedValue::Reference(reference)]),
                Err(OperationError::InvalidArgument {
                    issue: OperationArgumentIssue::UnverifiedReference,
                    ..
                })
            ));
        }
        assert!(matches!(
            r.invoke_operation(
                i,
                "Kernel-Expressions-NullExpression-evaluate_Element",
                &[DerivedValue::Element(f)]
            ),
            Err(OperationError::WrongReceiver { .. })
        ));
        let signature = operation_execution_signature(
            "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature",
        )
        .unwrap();
        assert_eq!(
            signature.inputs,
            ["Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature-visited"]
        );
        assert_eq!(
            signature.result,
            "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature-"
        );
    }
}

#[test]
fn unique_operation_arguments_reject_distinct_handles_with_the_same_uuid() {
    for (_, mut r) in models("package L;", "feature f; feature g; feature i=1;") {
        let i = value(&mut r, "i");
        let f = r.resolve_qualified("f").unwrap();
        let g = r.resolve_qualified("g").unwrap();
        assert_ne!(f, g);
        assert_ne!(r.element_id(f), r.element_id(g));
        assert_eq!(
            r.invoke_operation(i, ELIGIBLE, &[DerivedValue::Elements(vec![f, g])])
                .unwrap()
                .value,
            DerivedValue::Bool(true),
        );
        r.override_ids(&HashMap::from([(r.element_id(g), r.element_id(f))]));
        assert_eq!(r.element_id(f), r.element_id(g));
        for argument in [
            DerivedValue::Elements(vec![f, g]),
            DerivedValue::References(vec![Reference::Element(f), Reference::Element(g)]),
        ] {
            assert!(matches!(
                r.invoke_operation(i, ELIGIBLE, &[argument]),
                Err(OperationError::InvalidArgument {
                    index: 0,
                    issue: OperationArgumentIssue::DuplicateIdentity,
                    ..
                })
            ));
        }
        // This is per-argument identity validation, not a newly introduced
        // global model-validity prerequisite for constant operations.
        assert_eq!(
            r.invoke_operation(i, ELIGIBLE, &[DerivedValue::Elements(vec![f])])
                .unwrap()
                .value,
            DerivedValue::Bool(true),
        );
    }
}
