//! The `sysmlv2` command line. Everything it does lives in the library
//! beside it, so the verbs run (and are tested) in process too.

fn main() -> std::process::ExitCode {
    // One verb, then the end of the process: what the verb made need not
    // be freed.
    sysmlv2_cli::forget_at_exit();
    sysmlv2_cli::run(std::env::args_os())
}
