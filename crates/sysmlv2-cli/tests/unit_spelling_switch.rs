//! The spelled-unit expansion switch against repeated runs in one
//! process.
//!
//! Lives in its own test binary because the switch is process-wide: a run
//! in a neighbouring test would set it while this one reads it back.

use std::process::ExitCode;
use sysmlv2_parser::eval::unit_spelling_expansion;

/// The command line is a library entry point a host may call many times
/// in one process, so each run sets the switch from its own arguments: a
/// run that opts out must not decide the setting for the run after it,
/// which says nothing about spellings and therefore wants the default.
#[test]
fn each_run_sets_the_switch_from_its_own_arguments() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-units-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("m.sysml");
    std::fs::write(&path, "package M {\n    part def V;\n}\n").unwrap();
    let file = path.to_str().unwrap();

    let status = sysmlv2_cli::run(["sysmlv2", "-q", "--no-unit-spellings", "parse", file]);
    assert_eq!(format!("{status:?}"), format!("{:?}", ExitCode::SUCCESS));
    assert!(!unit_spelling_expansion(), "the run opted out");

    let status = sysmlv2_cli::run(["sysmlv2", "-q", "parse", file]);
    assert_eq!(format!("{status:?}"), format!("{:?}", ExitCode::SUCCESS));
    assert!(
        unit_spelling_expansion(),
        "a run saying nothing about spellings expands them"
    );

    std::fs::remove_dir_all(&dir).ok();
}
