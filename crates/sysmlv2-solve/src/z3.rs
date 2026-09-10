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
    child
        .stdin
        .take()
        .expect("stdin piped")
        .write_all(script.as_bytes())
        .map_err(|e| format!("cannot write to z3: {e}"))?;
    let out = child
        .wait_with_output()
        .map_err(|e| format!("z3 did not run to completion: {e}"))?;
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

/// The z3 binary's version banner, or an error naming what failed — the
/// availability probe.
pub(crate) fn version(z3: &Path) -> Result<String, String> {
    let out = Command::new(z3)
        .arg("-version")
        .output()
        .map_err(|e| format!("cannot run `{}`: {e}", z3.display()))?;
    let banner = String::from_utf8_lossy(&out.stdout);
    let banner = banner.trim();
    if banner.is_empty() {
        Err(format!("`{} -version` printed nothing", z3.display()))
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
