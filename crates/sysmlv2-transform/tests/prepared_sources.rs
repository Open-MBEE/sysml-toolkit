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

/// A library decoded from a prepared snapshot holds what hosts shipped in
/// it only when asked to keep it: `prepared_snapshot` and
/// `prepared_snapshot_chunks` drop it, and their `_with` variants keep it
/// with `true`.
#[test]
fn a_decoded_library_keeps_the_hosts_parts_only_when_asked() {
    let units = vec![(
        "lib.sysml".to_owned(),
        "package L { part def A; }".to_owned(),
    )];
    let Library::Prepared(prepared) = Library::prepared_sources(units.clone(), None).unwrap()
    else {
        panic!("prepared library expected");
    };
    prepared.carry_host_part("table", &"shipped").unwrap();
    let key =
        sysmlv2_model::libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
    let bytes = prepared.to_bytes(key).unwrap();
    let feed = || {
        let mut at = 0;
        let bytes = bytes.clone();
        move |buf: &mut [u8]| {
            let n = buf.len().min(bytes.len() - at);
            buf[..n].copy_from_slice(&bytes[at..at + n]);
            at += n;
            n
        }
    };
    let held = |library: Library| match library {
        Library::Prepared(library) => library.take_host_part::<String>("table"),
        _ => panic!("prepared library expected"),
    };
    let snapshot = |keep: Option<bool>| match keep {
        None => Library::prepared_snapshot(units.clone(), &bytes, None),
        Some(keep) => Library::prepared_snapshot_with(units.clone(), &bytes, None, keep),
    };
    let chunks = |keep: Option<bool>| match keep {
        None => Library::prepared_snapshot_chunks(units.clone(), bytes.len(), feed(), None),
        Some(keep) => {
            Library::prepared_snapshot_chunks_with(units.clone(), bytes.len(), feed(), None, keep)
        }
    };
    for decode in [&snapshot as &dyn Fn(Option<bool>) -> _, &chunks] {
        assert_eq!(held(decode(None).unwrap()), None, "dropped by default");
        assert_eq!(held(decode(Some(false)).unwrap()), None);
        assert_eq!(
            held(decode(Some(true)).unwrap()).as_deref(),
            Some("shipped")
        );
    }
}
