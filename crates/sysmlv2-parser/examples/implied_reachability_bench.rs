use std::{collections::HashMap, time::Instant};
use sysmlv2_parser::{json::ResolvedModel, model::Model};
fn main() {
    for count in [1000, 5000] {
        for reverse in [false, true] {
            let mut declarations = vec!["part def T0;".to_string()];
            for i in 1..count {
                declarations.push(format!("part def T{i} :> T{};", i - 1));
            }
            if reverse {
                declarations.reverse();
            }
            let source = format!("package P {{ {} }}", declarations.join("\n"));
            let mut model = Model::new();
            model.add_source("bench.sysml", &source);
            let mut r = ResolvedModel::build(&model);
            let mut names = HashMap::new();
            names.insert(
                uuid::Uuid::new_v4().to_string(),
                vec!["Parts".into(), "Part".into()],
            );
            r.set_library_names(&names);
            let owner = r.resolve_qualified("P::T0").unwrap();
            let start = Instant::now();
            let edges = r.implied_relationships(owner);
            assert_eq!(edges.len(), 1);
            println!(
                "chain count={count} reverse={reverse} inference={:?}",
                start.elapsed()
            );
        }
    }
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "export.sysml",
        &format!(
            "package P {{ part def Base; {} }}",
            (0..200)
                .map(|i| format!("part def T{i} :> Base; part x{i}: T{i};"))
                .collect::<Vec<_>>()
                .join("\n")
        ),
    );
    for _ in 0..3 {
        let mut resolved = ResolvedModel::build(&model);
        let owner = resolved.resolve_qualified("P::Base").unwrap();
        let start = Instant::now();
        resolved.implied_relationships(owner);
        println!(
            "loaded library 200 definitions/usages inference={:?}",
            start.elapsed()
        );
        let start = Instant::now();
        let json = sysmlv2_parser::full::model_to_full_json(&model);
        println!(
            "loaded library 200 definitions/usages export={:?} elements={}",
            start.elapsed(),
            json.as_array().map_or(0, Vec::len)
        );
    }
}
