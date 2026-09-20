//! Z3 subprocess driver: one `z3 -in` invocation per query, SMT-LIB 2 on
//! stdin, verdict + `(get-value …)` s-expression on stdout. Running the
//! solver as a child process (rather than linking libz3) keeps this crate
//! dependency-free and buildable everywhere; the binary is only needed at
//! run time.

use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

/// Result of one `(check-sat)` query. `Sat` carries the parsed
/// `(get-value …)` pairs' value expressions, in query order (empty when no
/// values were requested).
pub(crate) enum QueryResult {
    Sat(Vec<SExpr>),
    Unsat,
    Unknown(String),
}

/// Run one SMT-LIB 2 script. `nvalues` is how many `(get-value …)` results
/// to expect after a `sat` verdict.
pub(crate) fn run_query(
    z3: &Path,
    timeout_ms: u64,
    script: &str,
    nvalues: usize,
) -> Result<QueryResult, String> {
    // -T is a hard wall-clock kill switch one notch above the soft
    // (set-option :timeout) already in the script.
    let hard_secs = (timeout_ms / 1000).max(1) + 1;
    let mut child = Command::new(z3)
        .arg("-in")
        .arg(format!("-T:{hard_secs}"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run `{}`: {e}", z3.display()))?;
    let mut stdin = child.stdin.take().expect("stdin piped");
    let write_err = stdin.write_all(script.as_bytes()).err();
    // Closing the pipe is what tells the solver the script is complete.
    // (On a target without processes the handle is a stub with nothing
    // to drop, which the lint would otherwise report.)
    #[cfg_attr(target_family = "wasm", allow(clippy::drop_non_drop))]
    drop(stdin);
    if write_err.is_some() {
        // The script did not get through — most often because the solver
        // rejected its command line and exited before reading it. Stop it
        // and collect it below: an abandoned child would linger as a
        // zombie in a long-lived host, and its own message explains the
        // failure far better than a broken pipe does.
        let _ = child.kill();
    }
    let out = match child.wait_with_output() {
        Ok(out) => out,
        Err(e) => {
            return Err(match write_err {
                Some(w) => {
                    format!("cannot write to z3: {w}; and it did not run to completion: {e}")
                }
                None => format!("z3 did not run to completion: {e}"),
            });
        }
    };
    if let Some(w) = write_err {
        return Err(format!(
            "cannot write to z3: {w}{}",
            early_exit_report(&out)
        ));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let mut rest: &str = &text;
    // Skip anything before the verdict line (warnings etc.).
    let verdict = loop {
        let (line, tail) = match rest.split_once('\n') {
            Some(p) => p,
            None => (rest, ""),
        };
        let line = line.trim();
        rest = tail;
        match line {
            "sat" | "unsat" | "unknown" | "timeout" => break line,
            l if l.starts_with("(error") => {
                return Err(format!("z3 error: {l}"));
            }
            "" if rest.is_empty() => {
                let err = String::from_utf8_lossy(&out.stderr);
                return Err(format!(
                    "z3 produced no verdict{}",
                    if err.trim().is_empty() {
                        String::new()
                    } else {
                        format!(": {}", err.trim())
                    }
                ));
            }
            _ => {}
        }
    };
    match verdict {
        "unsat" => Ok(QueryResult::Unsat),
        "unknown" => Ok(QueryResult::Unknown("solver returned unknown".into())),
        "timeout" => Ok(QueryResult::Unknown("solver timed out".into())),
        _ => {
            if nvalues == 0 {
                return Ok(QueryResult::Sat(Vec::new()));
            }
            let (sexpr, _) =
                parse_sexpr(rest).ok_or_else(|| "cannot parse z3 model values".to_string())?;
            let SExpr::List(pairs) = sexpr else {
                return Err("unexpected z3 model shape".into());
            };
            let mut values = Vec::with_capacity(nvalues);
            for p in pairs {
                let SExpr::List(pair) = p else {
                    return Err("unexpected z3 model entry".into());
                };
                if pair.len() != 2 {
                    return Err("unexpected z3 model entry".into());
                }
                values.push(pair.into_iter().nth(1).unwrap());
            }
            if values.len() != nvalues {
                return Err("z3 returned a partial model".into());
            }
            Ok(QueryResult::Sat(values))
        }
    }
}

/// What a solver that quit before the script reached it has to say for
/// itself: its own output (stderr, else stdout) and how it ended. Appended
/// to the write failure so the caller sees the cause and not just the
/// symptom.
fn early_exit_report(out: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&out.stderr);
    let said = if stderr.trim().is_empty() {
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    } else {
        stderr.trim().to_string()
    };
    let how = match out.status.code() {
        Some(c) => format!("; z3 exited first with status {c}"),
        None => "; z3 exited first".to_string(),
    };
    if said.is_empty() {
        how
    } else {
        format!("{how}: {said}")
    }
}

/// The z3 binary's version banner — the availability probe. The error
/// carries the operating system's own account of why the binary could not
/// be run (a missing binary and an unreadable one are different failures),
/// or `None` when it ran but printed no banner.
pub(crate) fn version(z3: &Path) -> Result<String, Option<std::io::Error>> {
    let out = Command::new(z3).arg("-version").output().map_err(Some)?;
    let banner = String::from_utf8_lossy(&out.stdout);
    let banner = banner.trim();
    if banner.is_empty() {
        Err(None)
    } else {
        Ok(banner.to_string())
    }
}

// ---------------------------------------------------------------------------
// Minimal s-expression reader (for `(get-value …)` responses)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Parse one s-expression off the front of `input`; returns it and the
/// remaining text.
pub(crate) fn parse_sexpr(input: &str) -> Option<(SExpr, &str)> {
    let input = input.trim_start();
    let mut chars = input.char_indices();
    let (_, first) = chars.next()?;
    if first == '(' {
        let mut items = Vec::new();
        let mut rest = &input[1..];
        loop {
            rest = rest.trim_start();
            if let Some(stripped) = rest.strip_prefix(')') {
                return Some((SExpr::List(items), stripped));
            }
            let (item, tail) = parse_sexpr(rest)?;
            items.push(item);
            rest = tail;
        }
    }
    if first == '|' {
        let end = input[1..].find('|')? + 1;
        return Some((SExpr::Atom(input[1..end].to_string()), &input[end + 1..]));
    }
    if first == '"' {
        let end = input[1..].find('"')? + 1;
        return Some((SExpr::Atom(input[1..end].to_string()), &input[end + 1..]));
    }
    let end = input
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(input.len());
    if end == 0 {
        return None;
    }
    Some((SExpr::Atom(input[..end].to_string()), &input[end..]))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    /// A stand-in solver that never reads its input: it writes one line of
    /// its own and exits straight away, the way a real one does when it
    /// rejects its command line.
    fn stub_that_exits_first() -> (std::path::PathBuf, std::path::PathBuf) {
        let dir = std::env::temp_dir().join(format!("sysmlv2-solve-stub-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("exits-first");
        std::fs::write(&path, "#!/bin/sh\necho 'unrecognized option' >&2\nexit 3\n").unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        (dir, path)
    }

    #[test]
    fn a_solver_that_quits_first_is_collected_and_quoted() {
        let (dir, stub) = stub_that_exits_first();
        // Wider than any pipe buffer, so the write cannot slip into the
        // buffer before the child is gone.
        let script = format!("; {}\n(check-sat)\n", "x".repeat(1 << 20));
        let outcome = run_query(&stub, 1000, &script, 0);
        std::fs::remove_dir_all(&dir).unwrap();
        let Err(err) = outcome else {
            panic!("a solver that never read the script cannot have a verdict");
        };
        assert!(err.contains("cannot write to z3"), "{err}");
        // Its own account reaches the caller, which is only possible if
        // the driver waited for it instead of abandoning it.
        assert!(err.contains("status 3"), "{err}");
        assert!(err.contains("unrecognized option"), "{err}");
    }
}
