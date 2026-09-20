//! Write `spec-refs/derived-correspondence.json`: for every (concrete
//! metaclass, property) the interchange schema declares, whether the
//! abstract syntax owns or derives it, the derivation layer's fidelity at
//! the passthrough level and under the closure policy, the interchange
//! shape, and — for derived rows — the XMI's type and multiplicity. The
//! table a per-language SDK generator consumes (plan §33i); a consumer
//! keys on `fidelity`, never on corpus fill rate.
//!
//! Usage: `cargo run --example derived_correspondence` from the workspace
//! root (reads `spec-refs/derived-properties.json` for the XMI facts).

use serde_json::{Map, Value, json};
use std::collections::HashMap;
use sysmlv2_parser::json::{
    ClosurePolicy, Derives, PropertyShape, derives, derives_under, property_catalog,
};

fn fidelity(f: Derives) -> &'static str {
    match f {
        Derives::NotDeclared => "not-declared",
        Derives::NotComputed => "not-computed",
        Derives::Passthrough => "passthrough",
        Derives::Exact => "exact",
    }
}

fn shape(s: PropertyShape) -> &'static str {
    match s {
        PropertyShape::Array => "array",
        PropertyShape::Boolean => "boolean",
        PropertyShape::Nullable => "nullable",
        PropertyShape::Scalar => "scalar",
        PropertyShape::Enumeration => "enumeration",
        PropertyShape::RequiredReference => "required-reference",
        _ => "other",
    }
}

fn main() {
    let root = sysmlv2_testkit::workspace_root();
    let census: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("spec-refs/derived-properties.json"))
            .expect("spec-refs/derived-properties.json"),
    )
    .unwrap();
    // (property name) -> declaring records, for the XMI type and
    // multiplicity of a derived row (matched by the nearest declaring
    // metaclass the concrete carrier conforms to — the first declaring
    // record when several).
    let mut declaring: HashMap<String, Vec<Value>> = HashMap::new();
    for record in census["properties"].as_array().unwrap() {
        let name = record["name"].as_str().unwrap().to_string();
        declaring.insert(name, record["declaring"].as_array().unwrap().clone());
    }
    let closure = ClosurePolicy::Closure {
        include_implied: true,
    };
    let mut rows: Vec<Value> = Vec::new();
    for entry in property_catalog() {
        let mut row = Map::new();
        row.insert("metaclass".into(), json!(entry.metaclass));
        row.insert("property".into(), json!(entry.property));
        row.insert("shape".into(), json!(shape(entry.shape)));
        row.insert("owned".into(), json!(entry.owned));
        if !entry.owned {
            row.insert(
                "fidelity".into(),
                json!(fidelity(derives(entry.metaclass, entry.property))),
            );
            row.insert(
                "fidelityUnderClosure".into(),
                json!(fidelity(derives_under(
                    entry.metaclass,
                    entry.property,
                    closure
                ))),
            );
            if let Some(decls) = declaring.get(entry.property) {
                // The nearest declaring metaclass: of those the row's
                // metaclass conforms to, the one that conforms to all the
                // others. A row with no conforming declarer gets no XMI
                // facts rather than a wrong declarer's.
                let conforming: Vec<&Value> = decls
                    .iter()
                    .filter(|d| {
                        d["metaclass"].as_str().is_some_and(|m| {
                            sysmlv2_parser::json::metaclass_conforms(entry.metaclass, m)
                        })
                    })
                    .collect();
                let decl = conforming.iter().copied().find(|d| {
                    let m = d["metaclass"].as_str().unwrap();
                    conforming.iter().all(|o| {
                        sysmlv2_parser::json::metaclass_conforms(
                            m,
                            o["metaclass"].as_str().unwrap(),
                        )
                    })
                });
                if let Some(d) = decl {
                    row.insert("type".into(), d["type"].clone());
                    row.insert("multiplicity".into(), d["multiplicity"].clone());
                    row.insert("ordered".into(), d["ordered"].clone());
                    row.insert("declaredOn".into(), d["metaclass"].clone());
                }
            }
        }
        rows.push(Value::Object(row));
    }
    let out = json!({
        "source": "the interchange schema catalog (SysML.schema.json 20250201) joined with spec-refs/derived-properties.json",
        "generator": "cargo run --example derived_correspondence",
        "note": "key on `fidelity` (not-computed / passthrough / exact), never on corpus fill rate; `fidelityUnderClosure` is the fidelity with ClosurePolicy::Closure in force",
        "rows": rows,
    });
    let path = root.join("spec-refs/derived-correspondence.json");
    std::fs::write(&path, serde_json::to_string_pretty(&out).unwrap() + "\n").unwrap();
    let derived = out["rows"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["owned"] == false)
        .count();
    println!(
        "wrote {} ({} rows, {derived} derived)",
        path.display(),
        out["rows"].as_array().unwrap().len()
    );
}
