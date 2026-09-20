use sysmlv2_transform::{Library, Session};

#[test]
fn prepared_library_keeps_source_order_and_navigation_text() {
    let units = vec![
        ("lib.KerML".to_owned(), "package L { class A; }".to_owned()),
        (
            "extra.sysml".to_owned(),
            "package Extra { part def B; }".to_owned(),
        ),
    ];
    let library = Library::prepared_sources(units.clone(), None).unwrap();
    if let Library::Prepared(graph) = &library {
        assert_eq!(
            graph.sources().collect::<Vec<_>>(),
            units
                .iter()
                .map(|(n, t)| (n.as_str(), t.as_str()))
                .collect::<Vec<_>>()
        );
        assert!(graph.source(2).is_none());
    } else {
        panic!("prepared library expected");
    }
    let s = Session::from_sources_with_library(
        vec![("user.sysml".into(), "package U;".into())],
        Some(library),
    )
    .unwrap();
    for (i, (name, text)) in units.iter().enumerate() {
        assert_eq!(s.library_unit(i), Some((name.as_str(), text.as_str())));
        assert!(s.library_unit_path(i).is_none());
    }
    assert!(s.library_unit(2).is_none());
}
