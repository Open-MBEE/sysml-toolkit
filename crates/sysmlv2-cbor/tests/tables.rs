//! Corpus gate: the generated CBOR field tables cover — by key,
//! value shape, and enum vocabulary — every element the compact emitter
//! produces across the per-metaclass golden snapshots. This pins the
//! tables to real emitter behavior, not just the normative metamodel.

use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::tables::{
    CborField, ENUM_NAMES, ENUM_TABLES, FULL_METACLASS_FIELDS, K_BOOL, K_ELEMENT_ID, K_ENUM,
    K_LITERAL, K_REF, K_REF_LIST, K_STR, K_STR_LIST, METACLASS_FIELDS,
};

fn goldens_expected() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../sysmlv2-parser/tests/goldens/expected")
}

fn is_uuid(s: &str) -> bool {
    s.len() == 36
        && s.char_indices().all(|(i, c)| match i {
            8 | 13 | 18 | 23 => c == '-',
            _ => c.is_ascii_hexdigit(),
        })
}

/// A reference value: `{"@id": uuid}` or the hermetic `{"@ref": name}`.
fn is_ref(v: &Value) -> bool {
    let Value::Object(o) = v else { return false };
    if o.len() != 1 {
        return false;
    }
    match (o.get("@id"), o.get("@ref")) {
        (Some(Value::String(s)), None) => is_uuid(s),
        (None, Some(Value::String(_))) => true,
        _ => false,
    }
}

fn kind_accepts(field: &CborField, v: &Value, elem_id: &str) -> bool {
    let (_, kind, etbl, _) = *field;
    match kind {
        K_BOOL => v.is_boolean(),
        K_STR => v.is_string() || v.is_null(),
        K_STR_LIST => v.as_array().is_some_and(|a| a.iter().all(Value::is_string)),
        K_REF => v.is_null() || is_ref(v),
        K_REF_LIST => v.as_array().is_some_and(|a| a.iter().all(is_ref)),
        K_ENUM => match v {
            Value::Null => true,
            Value::String(s) => ENUM_TABLES[etbl as usize].contains(&s.as_str()),
            _ => false,
        },
        K_LITERAL => v.is_boolean() || v.is_number() || v.is_string(),
        K_ELEMENT_ID => v.as_str() == Some(elem_id),
        _ => false,
    }
}

#[test]
fn tables_are_canonically_ordered() {
    assert!(
        METACLASS_FIELDS.windows(2).all(|w| w[0].0 < w[1].0),
        "metaclasses sorted and unique"
    );
    assert_eq!(ENUM_NAMES.len(), ENUM_TABLES.len());
    for (name, fields) in METACLASS_FIELDS {
        assert!(
            fields.windows(2).all(|w| w[0].0 < w[1].0),
            "{name}: fields sorted and unique"
        );
        assert!(fields.len() <= 64, "{name}: presence mask fits u64");
        for (prop, kind, etbl, dflt) in *fields {
            match *kind {
                K_ENUM => {
                    let table = ENUM_TABLES[*etbl as usize];
                    assert!(
                        *dflt == 255 || (*dflt as usize) < table.len(),
                        "{name}.{prop}: enum default in range"
                    );
                }
                K_BOOL => assert!(*dflt <= 1, "{name}.{prop}: boolean default"),
                _ => assert_eq!(*etbl, 255, "{name}.{prop}: no enum table"),
            }
        }
    }
}

/// The wire spells a metaclass as a 16-bit code and a property as an
/// 8-bit ordinal, and the lookups convert into those widths rather than
/// truncating — so a table that outgrew either space would start
/// answering "unknown metaclass" / "not a compact-form property" for
/// real names. Hold both spaces here, on both table sets.
#[test]
fn tables_fit_the_wire_code_spaces() {
    for (which, tables) in [
        ("compact", METACLASS_FIELDS),
        ("full", FULL_METACLASS_FIELDS),
    ] {
        assert!(
            u16::try_from(tables.len()).is_ok(),
            "{which} metaclass table fits the 16-bit type-code space ({})",
            tables.len()
        );
        for (name, fields) in tables {
            assert!(
                u8::try_from(fields.len()).is_ok(),
                "{which} {name}: {} fields fit the 8-bit ordinal space",
                fields.len()
            );
        }
    }
    let (last, _) = METACLASS_FIELDS[METACLASS_FIELDS.len() - 1];
    assert_eq!(
        sysmlv2_cbor::type_code(last),
        u16::try_from(METACLASS_FIELDS.len() - 1).ok(),
        "the highest metaclass still answers its own code"
    );
}

#[test]
fn tables_cover_the_golden_corpus() {
    let dir = goldens_expected();
    let mut files = 0usize;
    let mut elements = 0usize;
    for entry in fs::read_dir(&dir).expect("goldens/expected exists") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        files += 1;
        let text = fs::read_to_string(&path).unwrap();
        let Value::Array(elems) = serde_json::from_str(&text).unwrap() else {
            panic!("{}: golden is an element array", path.display());
        };
        for e in elems {
            elements += 1;
            let ty = e["@type"].as_str().expect("@type present");
            let code = METACLASS_FIELDS
                .binary_search_by(|(n, _)| n.cmp(&ty))
                .unwrap_or_else(|_| panic!("{ty}: emitted @type is a concrete metaclass"));
            let fields = METACLASS_FIELDS[code].1;
            let id = e["@id"].as_str().expect("@id present");
            assert!(is_uuid(id), "{ty}: @id is a UUID");
            for (key, value) in e.as_object().unwrap() {
                if key == "@id" || key == "@type" {
                    continue;
                }
                let f = fields
                    .binary_search_by(|(n, _, _, _)| n.cmp(&key.as_str()))
                    .unwrap_or_else(|_| panic!("{ty}.{key}: emitted key is in the field table"));
                assert!(
                    kind_accepts(&fields[f], value, id),
                    "{ty}.{key}: value {value} matches kind {}",
                    fields[f].1
                );
            }
        }
    }
    assert!(files >= 150, "corpus present ({files} golden files)");
    assert!(elements >= 1000, "corpus non-trivial ({elements} elements)");
}
