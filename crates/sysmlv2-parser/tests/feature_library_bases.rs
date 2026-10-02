#![cfg(feature = "json")]

use sysmlv2_parser::{json::ResolvedModel, model::Model};

#[test]
fn ordinary_features_inherit_the_kernel_base_members() {
    let mut model = Model::new();
    model.add_library_source("base.kerml", "standard library package Base { classifier Anything; feature things : Anything { feature that : Anything; } }");
    model.add_source(
        "features.kerml",
        "package P { class C; feature outer : C { feature inner subsets that; } }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    assert!(r.unresolved_references().is_empty());
    let that = r.resolve_qualified("Base::things::that").unwrap();
    assert_eq!(r.resolve_qualified("P::outer::that"), Some(that));
    assert_eq!(r.resolve_qualified("P::outer::inner::that"), Some(that));
}

#[test]
fn occurrence_library_features_resolve_their_featuring_instance() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let r = ResolvedModel::build(&model);
    let unresolved = r.unresolved_references();
    let failures: Vec<_> = unresolved
        .iter()
        .filter(|reference| {
            model
                .unit(reference.unit)
                .name
                .ends_with("Occurrences.kerml")
                && reference.spelling == "that"
        })
        .collect();
    assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn inherited_kernel_base_names_do_not_override_owned_names() {
    let mut model = Model::new();
    model.add_library_source("base.kerml", "standard library package Base { classifier Anything; feature things : Anything { feature that : Anything; } }");
    model.add_source(
        "features.kerml",
        "package P { feature outer { feature that; feature inner subsets that; } }",
    );
    let mut r = ResolvedModel::build(&model);
    assert!(r.unresolved_references().is_empty());
    let own = r.resolve_qualified("P::outer::that").unwrap();
    assert_ne!(Some(own), r.resolve_qualified("Base::things::that"));
    let inner = r.resolve_qualified("P::outer::inner").unwrap();
    let subsetting = r
        .owned_relationships(inner)
        .into_iter()
        .find(|&rel| r.element_type(rel) == "Subsetting")
        .unwrap();
    assert_eq!(
        r.relationship_ends(subsetting).1,
        vec![sysmlv2_parser::json::Reference::Element(own)]
    );
}

#[test]
fn prepared_features_preserve_inherited_kernel_members() {
    let mut base = Model::new();
    base.add_library_source("base.kerml", "standard library package Base { classifier Anything; feature things : Anything { feature that : Anything; } } package L { feature outer { feature inner subsets that; } }");
    let prepared = base.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(1).unwrap(), 1)
            .unwrap(),
    );
    for library in [prepared, decoded] {
        let mut model = Model::new();
        library.install(&mut model).unwrap();
        model.add_source("user.kerml", "feature test subsets L::outer::that;");
        let mut r = ResolvedModel::build(&model);
        assert!(r.unresolved_references().is_empty());
        assert_eq!(
            r.resolve_qualified("L::outer::that"),
            r.resolve_qualified("Base::things::that")
        );
    }
}

const PERFORMANCE_LIBRARY: &str = "standard library package Base { classifier Anything; feature things : Anything; }
standard library package Performances { behavior Performance specializes Base::Anything { feature startShot; } step performances : Performance subsets Base::things; }";

fn assert_step_base(mut r: ResolvedModel) {
    assert!(
        r.unresolved_references().is_empty(),
        "{:?}",
        r.unresolved_references()
    );
    let base = r.resolve_qualified("Performances::performances").unwrap();
    let inherited = r
        .resolve_qualified("Performances::Performance::startShot")
        .unwrap();
    for name in ["P::untyped", "P::indirect"] {
        let step = r.resolve_qualified(name).unwrap();
        assert_eq!(
            r.resolve_qualified(&format!("{name}::startShot")),
            Some(inherited)
        );
        assert!(r.conforms_with_implied(step, base));
    }
    let own = r.resolve_qualified("P::shadow::startShot").unwrap();
    assert_ne!(own, inherited);
    // A plain Feature does not gain Step's performance-specific members.
    assert!(r.resolve_qualified("P::ordinary::startShot").is_none());
    assert!(!r.implied_relationships(base).into_iter().any(|edge| {
        r.element_type(edge) == "Subsetting"
            && r.relationship_ends(edge).1 == vec![sysmlv2_parser::json::Reference::Element(base)]
    }));
}

#[test]
fn untyped_steps_inherit_and_materialize_the_performance_base() {
    let mut model = Model::new();
    model.add_library_source("performances.kerml", PERFORMANCE_LIBRARY);
    model.add_source("steps.kerml", "package P { step untyped; step indirect subsets untyped; step shadow { feature startShot; } feature ordinary; feature use subsets untyped.startShot; }");
    assert!(!model.has_errors());
    assert_step_base(ResolvedModel::build(&model));
}

#[test]
fn prepared_steps_preserve_the_performance_base() {
    let mut base = Model::new();
    base.add_library_source("performances.kerml", PERFORMANCE_LIBRARY);
    base.add_library_source("steps.kerml", "package P { step untyped; step indirect subsets untyped; step shadow { feature startShot; } feature ordinary; }");
    let prepared = base.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(1).unwrap(), 1)
            .unwrap(),
    );
    for library in [prepared, decoded] {
        let mut model = Model::new();
        library.install(&mut model).unwrap();
        model.add_source("use.kerml", "feature use subsets P::untyped.startShot;");
        assert_step_base(ResolvedModel::build(&model));
    }
}

#[test]
fn state_performance_library_steps_resolve_their_occurrence_members() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let r = ResolvedModel::build(&model);
    let failures: Vec<_> = r
        .unresolved_references()
        .into_iter()
        .filter(|reference| {
            model
                .unit(reference.unit)
                .name
                .ends_with("StatePerformances.kerml")
        })
        .collect();
    assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn metaclasses_inherit_and_materialize_the_metaobject_base() {
    let mut model = Model::new();
    model.add_library_source("metaobjects.kerml", "standard library package Metaobjects { metaclass Metaobject { feature annotatedElement; } }");
    model.add_source("metadata.kerml", "package P { metaclass M { feature annotatedElement redefines annotatedElement; } metaclass N specializes M; class Ordinary; }");
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    assert!(r.unresolved_references().is_empty());
    let base = r.resolve_qualified("Metaobjects::Metaobject").unwrap();
    let annotation = r
        .resolve_qualified("Metaobjects::Metaobject::annotatedElement")
        .unwrap();
    let own = r.resolve_qualified("P::M::annotatedElement").unwrap();
    assert_ne!(own, annotation);
    assert_eq!(r.resolve_qualified("P::N::annotatedElement"), Some(own));
    assert!(
        r.resolve_qualified("P::Ordinary::annotatedElement")
            .is_none()
    );
    for name in ["P::M", "P::N"] {
        let metaclass = r.resolve_qualified(name).unwrap();
        assert!(r.conforms_with_implied(metaclass, base));
    }
    let redefinition = r
        .owned_relationships(own)
        .into_iter()
        .find(|&r0| r.element_type(r0) == "Redefinition")
        .unwrap();
    assert_eq!(
        r.relationship_ends(redefinition).1,
        vec![sysmlv2_parser::json::Reference::Element(annotation)]
    );
}

#[test]
fn metamodel_library_resolves_its_inherited_annotation_member() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let prepared = model.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(1).unwrap(), 1)
            .unwrap(),
    );
    let mut resolved = vec![ResolvedModel::build(&model)];
    for library in [prepared, decoded] {
        let mut installed = Model::new();
        library.install(&mut installed).unwrap();
        installed.add_source(
            "use.kerml",
            "metaclass Example specializes KerML::Root::Annotation;",
        );
        resolved.push(ResolvedModel::build(&installed));
    }
    for r in resolved {
        let failures: Vec<_> = r
            .unresolved_references()
            .into_iter()
            .filter(|reference| reference.spelling == "annotatedElement")
            .collect();
        assert!(failures.is_empty(), "{failures:?}");
    }
}
