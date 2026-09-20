//! The command line driven in process: the shared model prologue and
//! the verbs that sit on it, called directly rather than through a
//! spawned binary, so each one's outcome is inspected as a value.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use sysmlv2_cli::{CliError, LoadedModel};

/// A scratch directory holding `files`, removed when the test ends.
struct Workspace(PathBuf);

impl Workspace {
    fn new(name: &str, files: &[(&str, &str)]) -> Workspace {
        let dir = std::env::temp_dir().join(format!(
            "sysmlv2-cli-inprocess-{}-{name}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        for (file, source) in files {
            std::fs::write(dir.join(file), source).unwrap();
        }
        Workspace(dir)
    }

    fn path(&self, file: &str) -> PathBuf {
        self.0.join(file)
    }

    fn inputs(&self, files: &[&str]) -> Vec<PathBuf> {
        files.iter().map(|f| self.path(f)).collect()
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).ok();
    }
}

/// An exit status carries no equality, so statuses are compared by the
/// only thing one shows of itself.
fn same_status(left: ExitCode, right: ExitCode) -> bool {
    format!("{left:?}") == format!("{right:?}")
}

/// The message an error carries, or `None` when it has already said
/// everything it will.
fn message(e: &CliError) -> Option<String> {
    match e {
        CliError::Reported(_) => None,
        CliError::Message(_) => Some(e.to_string()),
    }
}

fn load(files: Vec<PathBuf>) -> Result<LoadedModel, CliError> {
    sysmlv2_cli::load_model(files, None, true)
}

/// The error a refused call carries. A loaded model says nothing of
/// itself, so the accepted side is dropped rather than unwrapped.
fn refusal<T>(outcome: Result<T, CliError>) -> CliError {
    match outcome {
        Ok(_) => panic!("the call was accepted"),
        Err(e) => e,
    }
}

#[test]
fn the_prologue_parses_every_input_into_one_model() {
    let ws = Workspace::new(
        "prologue",
        &[
            ("a.sysml", "package A {\n    part def V;\n}\n"),
            ("b.sysml", "package B {\n    part def W;\n}\n"),
        ],
    );
    let loaded = load(ws.inputs(&["a.sysml", "b.sysml"])).expect("both files parse");
    // Without a standard library nothing precedes the inputs, and each
    // one is kept with the text it was read from.
    assert_eq!(loaded.boundary, 0);
    assert_eq!(loaded.sources.len(), 2);
    assert_eq!(loaded.sources[0].0, ws.path("a.sysml"));
    assert!(loaded.sources[1].1.contains("part def W"));

    // One model: a name from either file resolves in the same view.
    let mut resolved = loaded.into_resolved();
    assert!(resolved.resolve_qualified("A::V").is_some());
    assert!(resolved.resolve_qualified("B::W").is_some());
    assert!(resolved.resolve_qualified("A::W").is_none());
}

#[test]
fn the_prologue_reports_a_parse_failure_and_stops() {
    let ws = Workspace::new("illformed", &[("bad.sysml", "package P { part def ;")]);
    let e = refusal(load(ws.inputs(&["bad.sysml"])));
    // The diagnostic has already gone out against its own file, so the
    // error carries only the status the run ends with.
    assert_eq!(message(&e), None);
}

#[test]
fn the_prologue_expands_a_project_archive_into_its_units() {
    let ws = Workspace::new(
        "archive",
        &[("m.sysml", "package M {\n    part def V;\n}\n")],
    );
    let archive = ws.path("m.kpar");
    let status = sysmlv2_cli::run([
        "sysmlv2",
        "convert",
        ws.path("m.sysml").to_str().unwrap(),
        "--to",
        "kpar",
        "-o",
        archive.to_str().unwrap(),
    ]);
    assert!(same_status(status, ExitCode::SUCCESS));

    let loaded = load(vec![archive.clone()]).expect("the archive's units parse");
    assert_eq!(loaded.sources.len(), 1);
    assert_eq!(loaded.sources[0].0, archive.join("m.sysml"));
    assert!(loaded.into_resolved().resolve_qualified("M::V").is_some());
}

#[test]
fn a_verb_that_cannot_resolve_its_name_says_so() {
    let ws = Workspace::new(
        "resolve",
        &[("m.sysml", "package M {\n    part def V;\n}\n")],
    );
    let model = ws.path("m.sysml").display().to_string();

    sysmlv2_cli::run_describe(Some(ws.path("m.sysml")), vec!["M::V".into()], None, true)
        .expect("the element is there");
    let e = sysmlv2_cli::run_members(Some(ws.path("m.sysml")), vec!["M::Gone".into()], None, true)
        .expect_err("refused");
    assert_eq!(message(&e).as_deref(), Some("cannot resolve `M::Gone`"));

    // Too many names is a refusal too, before anything is loaded.
    let e = sysmlv2_cli::run_describe(None, vec![model, "A".into(), "B".into()], None, true)
        .expect_err("refused");
    assert_eq!(
        message(&e).as_deref(),
        Some("expected exactly one qualified name, got 2")
    );
}

#[test]
fn the_expression_verbs_refuse_an_argument_list_they_cannot_read() {
    let ws = Workspace::new("args", &[("m.sysml", "package M {\n    part def V;\n}\n")]);
    let model = ws.path("m.sysml").display().to_string();

    let e = sysmlv2_cli::run_query(
        None,
        vec![model.clone(), "1".into(), "2".into()],
        None,
        true,
    )
    .expect_err("refused");
    assert_eq!(
        message(&e).as_deref(),
        Some("expected exactly one query expression, got 2")
    );

    let e = sysmlv2_cli::run_render(vec![model], None, false, true).expect_err("refused");
    assert_eq!(
        message(&e).as_deref(),
        Some("expected exactly one view usage name, got 0")
    );
}

#[test]
fn eval_fails_the_run_after_reporting_every_name_it_could_not_evaluate() {
    let ws = Workspace::new(
        "eval",
        &[(
            "m.sysml",
            "package M {\n    attribute x : ScalarValues::Integer = 2 + 3;\n}\n",
        )],
    );
    sysmlv2_cli::run_eval(
        Some(ws.path("m.sysml")),
        vec!["M::x".into()],
        false,
        None,
        true,
    )
    .expect("the attribute evaluates");

    let e = sysmlv2_cli::run_eval(
        Some(ws.path("m.sysml")),
        vec!["M::x".into(), "M::gone".into()],
        false,
        None,
        true,
    )
    .expect_err("refused");
    // Each unresolved name was reported as it was reached, so only the
    // status is left to carry.
    assert_eq!(message(&e), None);
}

#[test]
fn parse_answers_for_every_file_it_was_given() {
    let ws = Workspace::new(
        "parse",
        &[
            ("ok.sysml", "package P;\n"),
            ("bad.sysml", "package P { part def ;"),
        ],
    );
    sysmlv2_cli::run_parse(Some(ws.path("ok.sysml")), false, true).expect("it parses");
    let e = sysmlv2_cli::run_parse(Some(ws.path("bad.sysml")), false, true).expect_err("refused");
    assert_eq!(message(&e), None);
}

#[test]
fn the_whole_command_line_runs_in_process() {
    let ws = Workspace::new(
        "run",
        &[(
            "m.sysml",
            "package M {\n    part def V;\n    part v : V;\n}\n",
        )],
    );
    let model = ws.path("m.sysml");
    let model = model.to_str().unwrap();
    assert!(same_status(
        sysmlv2_cli::run(["sysmlv2", "check", model]),
        ExitCode::SUCCESS
    ));
    assert!(same_status(
        sysmlv2_cli::run(["sysmlv2", "members", model, "M"]),
        ExitCode::SUCCESS
    ));
    // An argument list the parser refuses never reaches a verb.
    assert!(same_status(
        sysmlv2_cli::run(["sysmlv2", "members", model, "M", "--bogus"]),
        ExitCode::from(2)
    ));
    // …and a file that does not exist fails the run.
    assert!(same_status(
        sysmlv2_cli::run([
            "sysmlv2",
            "check",
            &ws.path("gone.sysml").display().to_string()
        ]),
        ExitCode::FAILURE
    ));
}

#[test]
fn the_prologue_takes_a_standard_library_before_the_inputs() {
    // The library directory is only consulted when one is named; a
    // directory that is not one fails the prologue with a message.
    let ws = Workspace::new("lib", &[("m.sysml", "package M;\n")]);
    let e = refusal(sysmlv2_cli::load_model(
        ws.inputs(&["m.sysml"]),
        Some(Path::new("/nonexistent-library-directory")),
        true,
    ));
    assert!(
        message(&e)
            .unwrap_or_default()
            .starts_with("cannot load library /nonexistent-library-directory"),
        "{:?}",
        message(&e)
    );
}
