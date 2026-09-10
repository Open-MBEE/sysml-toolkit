//! Dev tool: corpus feature-value evaluation statistics.
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

fn main() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let mut r = ResolvedModel::build(&model);
    let features = r.features_with_values();
    let mut ok = 0usize;
    let mut indeterminate = 0usize;
    let mut by_err: std::collections::HashMap<String, usize> = Default::default();
    for e in &features {
        match r.evaluate(*e) {
            Ok(sysmlv2_parser::eval::Value::Indeterminate) => indeterminate += 1,
            Ok(_) => ok += 1,
            Err(err) => {
                let key = match err {
                    sysmlv2_parser::eval::EvalError::Unresolved(_) => "unresolved".into(),
                    sysmlv2_parser::eval::EvalError::Unsupported(w) => {
                        format!("unsupported: {}", w.split('`').next().unwrap_or("?").trim())
                    }
                    sysmlv2_parser::eval::EvalError::Type(_) => "type error".into(),
                    sysmlv2_parser::eval::EvalError::Cycle(_) => "cycle".into(),
                    sysmlv2_parser::eval::EvalError::DivisionByZero => "div0".into(),
                };
                *by_err.entry(key).or_default() += 1;
            }
        }
    }
    println!(
        "{ok}/{} feature values compute ({:.1}%); {indeterminate} indeterminate \
         (parametric over unbound inputs); {} errors",
        features.len(),
        100.0 * ok as f64 / features.len() as f64,
        features.len() - ok - indeterminate,
    );
    let mut v: Vec<_> = by_err.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in v.into_iter().take(8) {
        println!("{n:>6}  {k}");
    }
}
