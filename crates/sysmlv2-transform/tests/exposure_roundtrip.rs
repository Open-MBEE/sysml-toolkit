//! Exposure filters retain their meaning through identity-preserving interchange.
use serde_json::Value;
use sysmlv2_transform::Session;

fn exposed_names(full: &Value) -> Vec<String> {
    let rows = full.as_array().unwrap();
    let view = rows.iter().find(|e| e["declaredName"] == "v").unwrap();
    view["exposedElement"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            rows.iter().find(|e| e["@id"] == r["@id"]).unwrap()["qualifiedName"]
                .as_str()
                .unwrap()
                .to_owned()
        })
        .collect()
}
fn foreign_ids(value: &Value) -> Value {
    let map: std::collections::HashMap<String, String> = value
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            let id = e["@id"].as_str().unwrap();
            (
                id.to_owned(),
                uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, id.as_bytes()).to_string(),
            )
        })
        .collect();
    fn rewrite(value: &Value, map: &std::collections::HashMap<String, String>) -> Value {
        match value {
            Value::String(s) => Value::String(map.get(s).unwrap_or(s).clone()),
            Value::Array(a) => Value::Array(a.iter().map(|v| rewrite(v, map)).collect()),
            Value::Object(o) => Value::Object(
                o.iter()
                    .map(|(k, v)| (k.clone(), rewrite(v, map)))
                    .collect(),
            ),
            other => other.clone(),
        }
    }
    rewrite(value, &map)
}

#[test]
fn metadata_attribute_exposure_filters_survive_json_and_foreign_id_reload() {
    for declaration in [
        "view v {expose Parts::**[@Flag and (as Flag).enabled];}",
        "view def Filtered {filter @Flag and (as Flag).enabled;} view v:Filtered {expose Parts::**;}",
    ] {
        let source = format!(
            "package P {{ metadata def Flag {{ attribute enabled; }} package Parts {{part yes {{@Flag {{enabled=true;}}}} part no {{@Flag {{enabled=false;}}}}}} {declaration}}}"
        );
        let session = Session::from_sources(vec![("exposure.sysml".into(), source)]).unwrap();
        assert_eq!(
            exposed_names(&session.to_full_json_with(false)),
            ["P::Parts::yes"]
        );
        let compact = session.to_compact_json();
        for payload in [&compact, &foreign_ids(&compact)] {
            let loaded =
                Session::from_interchange_json_named(payload, None, &["exposure.sysml".into()])
                    .unwrap();
            assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
            for _ in 0..2 {
                assert_eq!(
                    exposed_names(&loaded.to_full_json_with(false)),
                    ["P::Parts::yes"]
                );
            }
        }
    }
}
