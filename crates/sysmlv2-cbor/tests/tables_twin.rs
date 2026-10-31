//! The data twin of the generated CBOR tables (`spec-refs/cbor-tables.json`,
//! written by `tools/gen_cbor_tables.py` beside `cbor_tables.rs`) is the
//! compiled tables: the same version and source digest, the same enum
//! vocabularies, the same metaclass order (the wire type codes) and the
//! same compact and full field tables (the wire ordinals, kinds, enum
//! tables and defaults). A reader generated from the file in another
//! language then decodes what this crate encodes.

use serde_json::Value;
use sysmlv2_cbor::tables::{
    CBOR_TABLES_SOURCE_DIGEST, CBOR_TABLES_VERSION, CborField, ENUM_NAMES, ENUM_TABLES,
    FULL_METACLASS_FIELDS, METACLASS_FIELDS,
};

/// The kind names the twin spells, index-aligned with the `K_*` codes.
const KIND_NAMES: [&str; 8] = [
    "bool",
    "string",
    "stringList",
    "ref",
    "refList",
    "enum",
    "literal",
    "elementId",
];

fn fields_match(listed: &[Value], compiled: &[CborField], what: &str) {
    assert_eq!(listed.len(), compiled.len(), "{what}: field count");
    for (row, &(name, kind, enum_table, default)) in listed.iter().zip(compiled) {
        let row = row.as_array().unwrap_or_else(|| panic!("{what}: {row}"));
        assert_eq!(row[0].as_str(), Some(name), "{what}: field name");
        assert_eq!(
            row[1].as_str(),
            Some(KIND_NAMES[kind as usize]),
            "{what}.{name}: kind"
        );
        let expected_enum = if enum_table == 255 {
            Value::Null
        } else {
            Value::from(enum_table)
        };
        assert_eq!(row[2], expected_enum, "{what}.{name}: enum table");
        assert_eq!(row[3], Value::from(default), "{what}.{name}: default");
    }
}

#[test]
fn committed_table_twin_is_the_compiled_tables() {
    let path = sysmlv2_testkit::workspace_root().join("spec-refs/cbor-tables.json");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "{}: {e} (regenerate with tools/gen_cbor_tables.py)",
            path.display()
        )
    });
    let doc: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(doc["tablesVersion"], Value::from(CBOR_TABLES_VERSION));
    assert_eq!(
        doc["sourceDigest"].as_str(),
        Some(CBOR_TABLES_SOURCE_DIGEST)
    );
    let kinds: Vec<&str> = doc["kinds"]
        .as_array()
        .unwrap()
        .iter()
        .map(|k| k.as_str().unwrap())
        .collect();
    assert_eq!(kinds, KIND_NAMES);

    let enums = doc["enums"].as_array().unwrap();
    assert_eq!(enums.len(), ENUM_NAMES.len());
    for ((listed, name), values) in enums.iter().zip(ENUM_NAMES).zip(ENUM_TABLES) {
        assert_eq!(listed["name"].as_str(), Some(*name));
        let spelled: Vec<&str> = listed["values"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap())
            .collect();
        assert_eq!(spelled, *values, "{name}");
    }

    let metaclasses = doc["metaclasses"].as_array().unwrap();
    assert_eq!(metaclasses.len(), METACLASS_FIELDS.len());
    assert_eq!(METACLASS_FIELDS.len(), FULL_METACLASS_FIELDS.len());
    for (code, ((listed, (name, compact)), (full_name, full))) in metaclasses
        .iter()
        .zip(METACLASS_FIELDS)
        .zip(FULL_METACLASS_FIELDS)
        .enumerate()
    {
        assert_eq!(name, full_name);
        assert_eq!(listed["name"].as_str(), Some(*name));
        assert_eq!(listed["typeCode"], Value::from(code));
        fields_match(listed["compactFields"].as_array().unwrap(), compact, name);
        fields_match(
            listed["fullFields"].as_array().unwrap(),
            full,
            &format!("{name} (full)"),
        );
    }
}
