//! The `sysmlv2` command line. Everything it does lives in the library
//! beside it, so the verbs run (and are tested) in process too.

fn main() -> std::process::ExitCode {
    sysmlv2_cli::run(std::env::args_os())
}
