//! Parser integration controls for nonmetadata Annotation source precision.
#![cfg(feature = "json")]
use sysmlv2_parser::{
    check::{ConstraintVerdict, check_constraints},
    model::Model,
};
#[test]
fn unresolved_comment_target_does_not_hide_unrelated_value_receiver() {
    for extra in [
        "",
        "comment about Missing /*text*/",
        "metaclass M; @M about Missing;",
    ] {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "constraint.sysml",
                    "part def Tire { attribute depth default 6; constraint legal {depth >= 3} }"
                )
                .diagnostics
                .is_empty()
        );
        assert!(
            model
                .add_source("annotation.kerml", extra)
                .diagnostics
                .is_empty()
        );
        let checks = check_constraints(&model);
        let check = checks
            .iter()
            .find(|c| c.name.as_deref() == Some("legal"))
            .unwrap();
        if extra.starts_with("metaclass") {
            assert!(
                matches!(check.verdict, ConstraintVerdict::Undecided(_)),
                "{:?}",
                check.verdict
            );
        } else {
            assert_eq!(check.verdict, ConstraintVerdict::Satisfied);
        }
    }
}
