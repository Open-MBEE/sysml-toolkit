#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{Reference, ResolvedModel},
    model::{GraphFormat, Model},
};

const LIB: &str = "standard library package Connections {
 connection def Connection;
 connection def BinaryConnection :> Connection { end source; end target; }
}";

#[test]
fn two_owned_connection_ends_resolve_their_binary_redefinitions() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model.add_library_source("connections.sysml", LIB);
        model.add_source(
            "pairs.sysml",
            "package P { connection def Pair { end left :>> source; end right :>> target; } }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        assert!(
            r.unresolved_references().is_empty(),
            "{:?}",
            r.unresolved_references()
        );
        let binary = r
            .resolve_qualified("Connections::BinaryConnection")
            .unwrap();
        let pair = r.resolve_qualified("P::Pair").unwrap();
        assert!(r.conforms_with_implied(pair, binary));
        for (end, target) in [("left", "source"), ("right", "target")] {
            let local = r.resolve_qualified(&format!("P::Pair::{end}")).unwrap();
            let inherited = r
                .resolve_qualified(&format!("Connections::BinaryConnection::{target}"))
                .unwrap();
            let redef = r
                .owned_relationships(local)
                .into_iter()
                .find(|&rel| r.element_type(rel) == "Redefinition")
                .unwrap();
            assert_eq!(
                r.relationship_ends(redef).1,
                vec![Reference::Element(inherited)]
            );
        }
    }
}

#[test]
fn owned_end_count_controls_binary_definition_heritage() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model.add_library_source("connections.sysml", LIB);
        model.add_source(
            "counts.sysml",
            "package P {
            connection def Empty;
            connection def Unary { end a; }
            connection def Ternary { end a; end b; end c; }
            connection def Ordinary { ref a; ref b; }
            connection def Pair { end a; end b; }
            connection def Inherited :> Pair;
        }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let binary = r
            .resolve_qualified("Connections::BinaryConnection")
            .unwrap();
        for name in ["Empty", "Unary", "Ternary", "Ordinary"] {
            let element = r.resolve_qualified(&format!("P::{name}")).unwrap();
            assert!(!r.conforms_with_implied(element, binary), "{name}");
            assert!(
                r.resolve_qualified(&format!("P::{name}::source")).is_none(),
                "{name}"
            );
        }
        let inherited = r.resolve_qualified("P::Inherited").unwrap();
        assert!(r.conforms_with_implied(inherited, binary));
        assert!(
            !r.implied_relationships(inherited)
                .into_iter()
                .any(|rel| r.relationship_ends(rel).1 == vec![Reference::Element(binary)])
        );
    }
}

#[test]
fn noncanonical_binary_definition_names_do_not_supply_lookup_heritage() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for (library, user_library) in [
            (
                "standard library package Connections { connection def Connection; class BinaryConnection { feature source; feature target; } }",
                false,
            ),
            (LIB, true),
            (
                "standard library package Connections { connection def Connection; }",
                false,
            ),
        ] {
            let mut model = Model::with_graph_format(format);
            if user_library {
                model.add_source("connections.sysml", library);
            } else {
                model.add_library_source("connections.sysml", library);
            }
            model.add_source(
                "pair.sysml",
                "connection def Pair { end left :>> source; end right :>> target; }",
            );
            assert!(!model.has_errors());
            let r = ResolvedModel::build(&model);
            let names: Vec<_> = r
                .unresolved_references()
                .into_iter()
                .map(|site| site.spelling)
                .collect();
            assert!(names.iter().any(|n| n == "source"), "{names:?}");
            assert!(names.iter().any(|n| n == "target"), "{names:?}");
        }
    }
}

#[test]
fn binary_library_end_redefinitions_agree_across_preparation_and_graph_formats() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        let cold = ResolvedModel::build(&model);
        let expected = cold.unresolved_count();
        let prepared = model.prepare_library().unwrap();
        let decoded = std::sync::Arc::new(
            sysmlv2_parser::prepared::PreparedLibrary::from_bytes(
                &prepared.to_bytes(1).unwrap(),
                1,
            )
            .unwrap(),
        );
        let mut resolved = vec![cold];
        for library in [prepared, decoded] {
            let mut installed = Model::with_graph_format(format);
            library.install(&mut installed).unwrap();
            installed.add_source(
                "user.sysml",
                "package VerificationFixture { connection def Pair { end a; end b; } }",
            );
            resolved.push(ResolvedModel::build(&installed));
        }
        for mut r in resolved {
            assert_eq!(r.unresolved_count(), expected);
            let binary = r
                .resolve_qualified("Connections::BinaryConnection")
                .unwrap();
            let concrete = r
                .resolve_qualified("CausationConnections::Causation")
                .unwrap();
            assert!(r.conforms_with_implied(concrete, binary));
            for (end, target) in [("theCause", "source"), ("theEffect", "target")] {
                let local = r
                    .resolve_qualified(&format!("CausationConnections::Causation::{end}"))
                    .unwrap();
                let inherited = r
                    .resolve_qualified(&format!("Connections::BinaryConnection::{target}"))
                    .unwrap();
                let redef = r
                    .owned_relationships(local)
                    .into_iter()
                    .find(|&rel| r.element_type(rel) == "Redefinition")
                    .unwrap();
                assert_eq!(
                    r.relationship_ends(redef).1,
                    vec![Reference::Element(inherited)]
                );
            }
        }
        eprintln!("{format:?}: unresolved library sites {expected}");
    }
}
