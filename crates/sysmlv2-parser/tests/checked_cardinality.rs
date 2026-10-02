//! Exact checked cardinality and collection questions across library replay modes.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    eval::Value,
    json::{CardinalityBounds, CardinalityIssue, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

#[test]
fn checked_collection_bounds_preserve_actual_library_and_prepared_results() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(91).unwrap(), 91).unwrap());
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
            let unit = model.add_source("checked-bounds.kerml", "feature a[2..5]; feature b[3..7]; feature c subsets a,b; feature zero[0]; feature fixed[3]; feature n=3; feature referenceBound[n]; feature formulaBound[(1+2)]; multiplicity huge[9223372036854775809]; feature named { multiplicity subsets huge; }");
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let unit = model.add_source("checked-default.sysml", "part def P { part singleton; port portSingleton; attribute attrSingleton; ref explicit[4]; }");
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let unit = model.add_source("contextual-bounds.kerml", "class BoundsParent { feature count=4; feature entries[count]; multiplicity limits[count]; feature namedEntries { multiplicity subsets limits; } } class BoundsChild specializes BoundsParent { feature count redefines BoundsParent::count=6; feature entries redefines BoundsParent::entries; feature namedEntries redefines BoundsParent::namedEntries; }");
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let c = r.resolve_qualified("c").unwrap();
            if format == GraphFormat::CanonicalV3 {
                r.implied_relationships(c);
            }
            for (name, expected) in [
                ("BoundsParent::entries", 4),
                ("BoundsParent::namedEntries", 4),
                ("BoundsChild::entries", 6),
                ("BoundsChild::namedEntries", 6),
            ] {
                let e = r.resolve_qualified(name).unwrap();
                let report = r.cardinality_report(e);
                assert_eq!(
                    report
                        .bounds
                        .unwrap_or_else(|issue| panic!(
                            "{name} {format:?} replay {mode}, {} steps: {issue:?}",
                            report.steps
                        ))
                        .size(),
                    Some(expected),
                    "{name} {format:?} replay {mode}"
                );
            }
            let fixed = r.resolve_qualified("fixed").unwrap();
            let zero = r.resolve_qualified("zero").unwrap();
            assert_eq!(
                r.cardinality_report(c).bounds,
                Ok(CardinalityBounds {
                    lower: 3,
                    upper: Some(5)
                }),
                "{format:?} mode {mode}"
            );
            for name in ["P::singleton", "P::portSingleton", "P::attrSingleton"] {
                let e = r.resolve_qualified(name).unwrap();
                let report = r.cardinality_report(e);
                assert_eq!(
                    report.bounds.unwrap().size(),
                    Some(1),
                    "{name} {format:?} {mode}"
                );
                assert_eq!(report.implicit_singletons, vec![e]);
            }
            let sequence = Value::Sequence(vec![
                Value::Unbound(fixed),
                Value::Sequence(vec![Value::Unbound(zero), Value::Integer(7)]),
                Value::Element(fixed),
            ]);
            let bounds = r.collection_cardinality_report(&sequence).bounds.unwrap();
            assert_eq!(bounds.size(), Some(5));
            assert_eq!(bounds.is_empty(), Some(false));
            assert_eq!(bounds.contains_index(5), Some(true));
            assert_eq!(bounds.contains_index(6), Some(false));
            assert_eq!(
                r.collection_cardinality_report(&Value::UnboundMember(fixed))
                    .bounds,
                Err(CardinalityIssue::IncompleteProvider)
            );
            let dependent = r.resolve_qualified("referenceBound").unwrap();
            assert_eq!(
                r.collection_cardinality_report(&Value::UnboundMember(dependent))
                    .bounds,
                Err(CardinalityIssue::IncompleteProvider)
            );
            for name in ["referenceBound", "formulaBound"] {
                let e = r.resolve_qualified(name).unwrap();
                let report = r.cardinality_report(e);
                if name == "formulaBound" && format == GraphFormat::LegacyV2 {
                    assert_eq!(report.bounds, Err(CardinalityIssue::UnsupportedBound));
                } else {
                    assert_eq!(
                        report
                            .bounds
                            .unwrap_or_else(|issue| panic!(
                                "{name} {format:?} mode {mode}: {issue:?}"
                            ))
                            .size(),
                        Some(3),
                        "{name} {format:?} {mode}"
                    );
                }
            }
            let named = r.resolve_qualified("named").unwrap();
            assert_eq!(
                r.cardinality_report(named).bounds.unwrap().size(),
                Some(9223372036854775809)
            );
            r.implied_relationships(named);
            assert_eq!(
                r.cardinality_report(named).bounds.unwrap().size(),
                Some(9223372036854775809)
            );
            assert_eq!(
                r.cardinality_report(c).bounds,
                Ok(CardinalityBounds {
                    lower: 3,
                    upper: Some(5)
                })
            );
        }
    }
}

#[test]
fn unknown_receiver_members_do_not_fabricate_outer_collection_cardinality() {
    let mut model = Model::new();
    let unit = model.add_source("receiver-cardinality.kerml", "class C { feature items[3]; } feature empty[0]:C; feature many[0..*]:C; feature a=empty.items; feature b=many.items;");
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let items = r.resolve_qualified("C::items").unwrap();
    assert_eq!(
        r.collection_cardinality_report(&Value::UnboundMember(items))
            .bounds,
        Err(CardinalityIssue::IncompleteProvider)
    );
    let empty = r.resolve_qualified("a").unwrap();
    let value = r.evaluate(empty).unwrap();
    assert_eq!(
        r.collection_cardinality_report(&value)
            .bounds
            .unwrap()
            .size(),
        Some(0)
    );
    let many = r.resolve_qualified("b").unwrap();
    let value = r.evaluate(many).unwrap();
    assert_eq!(
        r.collection_cardinality_report(&value).bounds,
        Err(CardinalityIssue::IncompleteProvider)
    );
}
