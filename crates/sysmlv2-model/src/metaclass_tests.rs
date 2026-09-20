//! Pins the generated metaclass conformance tables against the hierarchy
//! they were generated from.
use crate::metaclass::{ANCESTOR_NAMES, canonical_name, conforms};

#[test]
fn conformance_table_matches_the_generated_hierarchy() {
    let names: Vec<&str> = ANCESTOR_NAMES.iter().map(|(name, _)| *name).collect();
    assert!(names.windows(2).all(|w| w[0] < w[1]), "sorted, unique");
    for (specific, ancestors) in ANCESTOR_NAMES {
        assert!(ancestors.windows(2).all(|w| w[0] < w[1]));
        for general in &names {
            let expected = specific == *general || ancestors.contains(general);
            assert_eq!(
                conforms(specific, general),
                expected,
                "{specific} -> {general}"
            );
        }
        // Inheritance is transitive: every ancestor's ancestors are ours.
        for ancestor in ancestors {
            let (_, theirs) = ANCESTOR_NAMES[names.binary_search(ancestor).unwrap()];
            for further in theirs {
                assert!(
                    ancestors.contains(further),
                    "{specific}: {ancestor} -> {further}"
                );
            }
        }
    }
}

#[test]
fn conformance_samples_and_unknown_names() {
    for (specific, general, expected) in [
        ("PortDefinition", "Definition", true),
        ("PortDefinition", "Classifier", true),
        ("PortDefinition", "Element", true),
        ("PortDefinition", "Usage", false),
        ("Definition", "PortDefinition", false),
        ("AcceptActionUsage", "Step", true),
        ("AcceptActionUsage", "Behavior", false),
        ("Membership", "Relationship", true),
        ("Relationship", "Membership", false),
        ("LiteralInteger", "Expression", true),
        ("MetadataUsage", "ItemUsage", true),
        ("Element", "Element", true),
        ("Unknown", "Element", false),
        ("Element", "Unknown", false),
        ("Unknown", "Unknown", true),
    ] {
        assert_eq!(
            conforms(specific, general),
            expected,
            "{specific} -> {general}"
        );
    }
    assert_eq!(canonical_name("PortDefinition"), Some("PortDefinition"));
    assert_eq!(canonical_name("portdefinition"), None);
    assert_eq!(canonical_name(""), None);
    assert!(
        ANCESTOR_NAMES
            .iter()
            .all(|(n, _)| canonical_name(n) == Some(*n))
    );
}
