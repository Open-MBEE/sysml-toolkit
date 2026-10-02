#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};

#[test]
fn actual_library_assertion_roles_replay_with_identity_and_source_stability() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: standard library unavailable");
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let recorded =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(91).unwrap(), 91).unwrap());
    let mut replay_ids = None;
    for mode in 0..4 {
        let mut m = Model::new();
        match mode {
            2 => Arc::clone(&prepared).install(&mut m).unwrap(),
            3 => Arc::clone(&decoded).install(&mut m).unwrap(),
            _ => {
                m.load_library_dir(&library).unwrap();
                if mode == 1 {
                    m.set_library_cache(recorded.clone());
                }
            }
        }
        let parsed=m.add_source("assertion-roles.sysml","package P { constraint plain {true} requirement ordinary; assert constraint yes {true} assert not constraint no {false} part thing; requirement def R { subject s; } satisfy requirement sat : R by thing; not satisfy requirement unsat : R by thing; assert constraint direct :> Constraints::assertedConstraintChecks; assert constraint indirect :> direct; satisfy requirement directSat :> Requirements::satisfiedRequirementChecks; satisfy requirement indirectSat :> directSat; }");
        assert!(
            parsed.diagnostics.is_empty(),
            "mode {mode}: {:?}",
            parsed.diagnostics
        );
        let compact = model_to_compact_json(&m);
        let mut r = ResolvedModel::build(&m);
        let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let cases: Vec<_> = [
            (
                "P::yes",
                "AssertConstraintUsage",
                "Constraints::assertedConstraintChecks",
                false,
            ),
            (
                "P::no",
                "AssertConstraintUsage",
                "Constraints::negatedConstraintChecks",
                true,
            ),
            (
                "P::sat",
                "SatisfyRequirementUsage",
                "Requirements::satisfiedRequirementChecks",
                false,
            ),
            (
                "P::unsat",
                "SatisfyRequirementUsage",
                "Requirements::notSatisfiedRequirementChecks",
                true,
            ),
        ]
        .into_iter()
        .map(|(name, kind, role, negated)| {
            let owner = r.resolve_qualified(name).unwrap();
            let role = r.resolve_qualified(role).unwrap();
            assert_eq!(r.element_type(owner), kind);
            assert_eq!(
                r.element_type(role),
                if kind == "SatisfyRequirementUsage" {
                    "RequirementUsage"
                } else {
                    "ConstraintUsage"
                }
            );
            (owner, role, negated)
        })
        .collect();
        let mut policy_ids = None;
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
            let mut ids = Vec::new();
            for &(owner, role, negated) in &cases {
                assert_eq!(
                    r.property(owner, "isNegated").unwrap(),
                    serde_json::json!(negated)
                );
                assert!(r.conforms_with_implied(owner, role));
                let assertion = if negated {
                    "Constraints::negatedConstraintChecks"
                } else {
                    "Constraints::assertedConstraintChecks"
                };
                let invariant = if negated {
                    "Performances::falseEvaluations"
                } else {
                    "Performances::trueEvaluations"
                };
                for parent in [
                    assertion,
                    invariant,
                    "Constraints::constraintChecks",
                    "Performances::booleanEvaluations",
                    "Performances::evaluations",
                ] {
                    let parent = r.resolve_qualified(parent).unwrap();
                    assert!(r.conforms_with_implied(owner, parent), "{parent:?}");
                }
                let role_id = r.element_id(role);
                let rows = r.implied_relationships(owner);
                let direct: Vec<_> = rows
                    .iter()
                    .copied()
                    .filter(|&row| {
                        r.element_properties(row)["subsettedFeature"]["@id"] == role_id.to_string()
                    })
                    .collect();
                assert_eq!(direct.len(), 1);
                let key = format!("{}/implied/Subsetting/{}", r.element_id(owner), role_id);
                assert_eq!(
                    r.element_id(direct[0]),
                    uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, key.as_bytes())
                );
                for redundant in [
                    "Constraints::constraintChecks",
                    "Requirements::requirementChecks",
                    assertion,
                    invariant,
                    "Performances::booleanEvaluations",
                    "Performances::evaluations",
                ] {
                    let redundant = r.resolve_qualified(redundant).unwrap();
                    if redundant != role {
                        assert!(
                            !rows
                                .iter()
                                .any(|&row| r.element_properties(row)["subsettedFeature"]["@id"]
                                    == r.element_id(redundant).to_string()),
                            "redundant inherited role"
                        );
                    }
                }
                ids.extend(rows.into_iter().map(|row| r.element_id(row)));
            }
            for (name, role) in [
                ("P::plain", "Constraints::constraintChecks"),
                ("P::ordinary", "Requirements::requirementChecks"),
            ] {
                let owner = r.resolve_qualified(name).unwrap();
                let role = r.resolve_qualified(role).unwrap();
                let role_id = r.element_id(role).to_string();
                let rows = r.implied_relationships(owner);
                let row = *rows
                    .iter()
                    .find(|&&row| r.element_properties(row)["subsettedFeature"]["@id"] == role_id)
                    .unwrap();
                let key = format!("{}/implied0", r.element_id(owner));
                assert_eq!(
                    r.element_id(row),
                    uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, key.as_bytes()),
                    "surviving legacy obligation changed identity"
                );
                ids.push(r.element_id(row));
            }
            for name in ["P::direct", "P::indirect", "P::directSat", "P::indirectSat"] {
                let owner = r.resolve_qualified(name).unwrap();
                assert!(
                    r.implied_relationships(owner).is_empty(),
                    "redundant explicit path {name}"
                );
            }
            if let Some(expected) = &policy_ids {
                assert_eq!(&ids, expected)
            } else {
                policy_ids = Some(ids)
            }
        }
        if let Some(expected) = &replay_ids {
            assert_eq!(&policy_ids, expected)
        } else {
            replay_ids = Some(policy_ids)
        }
        assert_eq!(
            source_ids,
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>()
        );
        assert_eq!(compact, model_to_compact_json(&m));
    }
}
