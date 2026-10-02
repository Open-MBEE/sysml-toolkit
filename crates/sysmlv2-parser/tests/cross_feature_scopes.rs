#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{Reference, ResolvedModel},
    model::{GraphFormat, Model},
};

const FORMATS: [GraphFormat; 2] = [GraphFormat::LegacyV2, GraphFormat::CanonicalV3];

const SOURCE: &str = "package P {
    class A { feature leaf; }
    class B { feature leaf; feature count; }
    feature leaf; feature count;
    assoc Pair {
        end feature a : A;
        end cross [count] subsets leaf feature b : B;
    }
    assoc Derived specializes Pair {
        end feature a redefines Pair::a;
        end inheritedCross subsets leaf feature b redefines Pair::b;
    }
}";

fn assert_cross_targets(model: &Model, source_sites: bool) {
    let mut resolved = ResolvedModel::build(model);
    assert!(
        resolved.unresolved_references().is_empty(),
        "{:?}",
        resolved.unresolved_references()
    );
    for (name, count) in [
        ("P::B::leaf", 2),
        ("P::B::count", 1),
        ("P::A::leaf", 0),
        ("P::leaf", 0),
        ("P::count", 0),
    ] {
        let target = resolved.resolve_qualified(name).unwrap();
        let sites = resolved.references_to(target);
        assert_eq!(
            sites.len(),
            if source_sites { count } else { 0 },
            "{name}: {sites:?}"
        );
        for site in sites {
            assert_eq!(
                &SOURCE[site.name_span.start as usize..site.name_span.end as usize],
                name.rsplit("::").next().unwrap()
            );
        }
    }
    let leaf = resolved.resolve_qualified("P::B::leaf").unwrap();
    for name in ["P::Pair::b", "P::Derived::b"] {
        let end = resolved.resolve_qualified(name).unwrap();
        let cross = resolved
            .owned_members(end)
            .into_iter()
            .find(|&member| resolved.element_type(member) == "ReferenceUsage")
            .unwrap();
        let subset = resolved
            .owned_relationships(cross)
            .into_iter()
            .find(|&rel| resolved.element_type(rel) == "Subsetting")
            .unwrap();
        assert_eq!(
            resolved.relationship_ends(subset).1,
            vec![Reference::Element(leaf)]
        );
    }
}

#[test]
fn cross_feature_references_use_the_owning_end_scope() {
    for format in FORMATS {
        let mut model = Model::with_graph_format(format);
        model.add_source("cross.kerml", SOURCE);
        assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
        assert_cross_targets(&model, true);
    }
}

#[test]
fn prepared_cross_feature_scope_survives_serialization() {
    for format in FORMATS {
        let mut model = Model::with_graph_format(format);
        model.add_library_source("cross.kerml", SOURCE);
        let prepared = model.prepare_library().unwrap();
        let decoded = std::sync::Arc::new(
            sysmlv2_parser::prepared::PreparedLibrary::from_bytes(
                &prepared.to_bytes(1).unwrap(),
                1,
            )
            .unwrap(),
        );
        for library in [prepared, decoded] {
            let mut model = Model::with_graph_format(format);
            library.install(&mut model).unwrap();
            assert_cross_targets(&model, false);
        }
    }
}

#[test]
fn cross_feature_missing_and_ambiguous_members_stay_unresolved() {
    for format in FORMATS {
        for source in [
            "package P { class A { feature leaf; } class B; assoc Pair { end feature a : A; end cross subsets leaf feature b : B; } }",
            "package P { feature leaf; class A { feature leaf; } class B { feature leaf; } class C specializes A, B; assoc Pair { end cross subsets leaf feature c : C; } }",
        ] {
            let mut model = Model::with_graph_format(format);
            model.add_source("unresolved.kerml", source);
            assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
            let resolved = ResolvedModel::build(&model);
            let failures = resolved.unresolved_references();
            assert_eq!(failures.len(), 1, "{failures:?}");
            assert_eq!(failures[0].spelling, "leaf");
        }
    }
}

#[test]
fn occurrence_library_cross_feature_members_resolve_after_replay() {
    for format in FORMATS {
        let mut source = Model::with_graph_format(format);
        source
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        let prepared = source.prepare_library().unwrap();
        let decoded = std::sync::Arc::new(
            sysmlv2_parser::prepared::PreparedLibrary::from_bytes(
                &prepared.to_bytes(1).unwrap(),
                1,
            )
            .unwrap(),
        );
        let mut models = vec![source];
        for library in [prepared, decoded] {
            let mut model = Model::with_graph_format(format);
            library.install(&mut model).unwrap();
            models.push(model);
        }
        for model in models {
            let resolved = ResolvedModel::build(&model);
            let failures: Vec<_> = resolved
                .unresolved_references()
                .into_iter()
                .filter(|reference| {
                    model
                        .unit(reference.unit)
                        .name
                        .ends_with("Occurrences.kerml")
                })
                .collect();
            assert!(failures.is_empty(), "{failures:?}");
        }
    }
}
