//! Workspace model tier: a background worker computing the full
//! `check --lib` diagnostic set — parse + body-context always,
//! referential + semantic when a library is configured — plus the
//! unused-private-import findings, over the *workspace*: every
//! `.sysml`/`.kerml` under the root, with open-document texts overlaid.
//!
//! Debounce discipline: jobs collapse — after a job arrives, newer jobs
//! replace it until the channel stays quiet for the debounce window, and
//! a job that arrives during computation discards the computed result
//! (latest-only). There is no mid-computation cancellation: a build is
//! ~0.15 s warm with a library, so the wasted work is bounded and the
//! version guard on every publish keeps stale results out of the editor.
//! The syntax tier still publishes per keystroke for fast feedback; this
//! worker's fuller set replaces it a debounce later.

use crate::Report;
use crate::position::{Encoding, UnitMappers};
use lsp_server::Message;
use lsp_types::notification::Notification as _;
use lsp_types::{DiagnosticSeverity, DiagnosticTag, PublishDiagnosticsParams, Uri};
use std::collections::{HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::mpsc;
use std::time::Duration;
use sysmlv2_transform::{Library, Session, Severity, check_sources};

pub(crate) const UNUSED_IMPORT_MESSAGE: &str = "unused private import";

/// Stack reserved for the worker thread.
///
/// The worker parses, and the parser bounds its own descent at a depth
/// it can only reach on a stack sized for it — the size named here. A
/// thread that does not ask for one gets two megabytes, a fraction of
/// that bound: ordinary nested input the parser accepts and reports
/// nothing about would end the whole language server, editor session and
/// all, with no diagnostic and no unwind to catch.
///
/// Reserved address space, not resident pages: the cost of asking for it
/// is nothing until the recursion touches it.
///
/// It is the parser's own constant, not a number sized to match one, so
/// there is nothing here that can drift from what the bound asks for.
const WORKER_STACK_BYTES: usize = sysmlv2_parser::parser::MAX_NESTING_STACK_BYTES;

pub(crate) struct Job {
    /// (uri, version, text) of every open document; the texts are
    /// shared with the document store, not copied per job.
    pub docs: Vec<(String, i32, std::sync::Arc<str>)>,
    pub root: Option<PathBuf>,
}

pub(crate) struct Worker {
    tx: mpsc::Sender<Job>,
}

impl Worker {
    pub fn spawn(
        sender: crossbeam_channel::Sender<Message>,
        library: Option<PathBuf>,
        encoding: Encoding,
        debounce: Duration,
    ) -> Worker {
        let (tx, rx) = mpsc::channel::<Job>();
        let client = sender.clone();
        let spawned = std::thread::Builder::new()
            .name("sysmlv2-lsp-worker".into())
            .stack_size(WORKER_STACK_BYTES)
            .spawn(move || {
                run(&rx, &sender, library.as_deref(), encoding, debounce, cycle);
            });
        match spawned {
            Ok(_) => Worker { tx },
            Err(err) => Worker::unstarted(&client, &err),
        }
    }

    /// The worker whose thread never started. No thread, no model tier:
    /// the syntax tier keeps publishing per keystroke and every job is
    /// dropped, exactly as for a host without threads — but a host that
    /// *has* threads and could not give this one a stack the size the
    /// parser's bound asks for has lost half its findings, so it is told
    /// rather than left to notice.
    ///
    /// Once, both ways: the thread is started once, so the failure is
    /// reported once — the log carries what the system said, and the
    /// message says what the editor session loses by it.
    fn unstarted(sender: &crossbeam_channel::Sender<Message>, err: &std::io::Error) -> Worker {
        let lost = "the workspace model tier is off: its thread could not be started. \
             Findings are the open file's own syntax only — the library-aware and \
             cross-file ones are not computed.";
        for notification in [
            lsp_server::Notification::new(
                lsp_types::notification::LogMessage::METHOD.to_string(),
                lsp_types::LogMessageParams {
                    typ: lsp_types::MessageType::ERROR,
                    message: format!("{lost} The thread was refused: {err}"),
                },
            ),
            lsp_server::Notification::new(
                lsp_types::notification::ShowMessage::METHOD.to_string(),
                lsp_types::ShowMessageParams {
                    typ: lsp_types::MessageType::ERROR,
                    message: lost.to_string(),
                },
            ),
        ] {
            let _ = sender.send(Message::Notification(notification));
        }
        Worker::disabled()
    }

    pub fn schedule(&self, job: Job) {
        let _ = self.tx.send(job);
    }

    /// A worker that drops every job: for hosts without threads (the
    /// push-driven WASM frontend), where the model tier is the host's
    /// responsibility. `schedule` sends into a closed channel — a no-op.
    pub fn disabled() -> Worker {
        let (tx, _) = mpsc::channel::<Job>();
        Worker { tx }
    }
}

/// One cycle's work — [`cycle`], swapped out in tests.
type CycleFn = fn(&Job, Option<&std::path::Path>, Encoding) -> (Diagnostics, Vec<Report>);

fn run(
    rx: &mpsc::Receiver<Job>,
    sender: &crossbeam_channel::Sender<Message>,
    library: Option<&std::path::Path>,
    encoding: Encoding,
    debounce: Duration,
    cycle: CycleFn,
) {
    // Uris published last cycle — files whose findings vanish (or which
    // drop out of the workspace) publish an empty set once to clear.
    let mut published: HashSet<String> = HashSet::new();
    let mut pending: Option<Job> = None;
    // Panics already announced: a model that panics on the text in the
    // editor would otherwise announce it again per keystroke.
    let mut announced: HashSet<String> = HashSet::new();
    loop {
        let mut job = match pending.take() {
            Some(j) => j,
            None => match rx.recv() {
                Ok(j) => j,
                Err(_) => return,
            },
        };
        // Debounce: newer jobs replace this one until the channel is
        // quiet for the window.
        loop {
            match rx.recv_timeout(debounce) {
                Ok(newer) => job = newer,
                Err(mpsc::RecvTimeoutError::Timeout) => break,
                Err(mpsc::RecvTimeoutError::Disconnected) => return,
            }
        }

        // A panic in the model, the lint or the line mapping used to
        // end this thread, after which every later job vanished into a
        // dead channel and the editor kept the findings it had, for
        // good, with nothing said. The cycle is skipped instead and the
        // worker stays up for the next edit.
        let (by_uri, reports) =
            match catch_unwind(AssertUnwindSafe(|| cycle(&job, library, encoding))) {
                Ok(done) => done,
                Err(payload) => {
                    let reason = crate::panic_reason(payload.as_ref());
                    let message = format!(
                        "model diagnostics failed: {reason}. \
                         Findings already shown may be out of date."
                    );
                    announce(
                        sender,
                        &mut announced,
                        &Report {
                            show: true,
                            message,
                        },
                    );
                    continue;
                }
            };
        // A model the worker could not build at all publishes nothing,
        // which on its own reads as "no problems here".
        for report in &reports {
            announce(sender, &mut announced, report);
        }

        // Latest-only: a job that arrived during computation wins.
        if let Ok(newer) = rx.try_recv() {
            pending = Some(newer);
            continue;
        }

        let versions: HashMap<&str, i32> =
            job.docs.iter().map(|(u, v, _)| (u.as_str(), *v)).collect();
        let mut next_published = HashSet::new();
        for (uri_str, diagnostics) in by_uri {
            if diagnostics.is_empty() && !published.contains(&uri_str) {
                continue; // nothing to say, nothing to clear
            }
            let Ok(uri) = Uri::from_str(&uri_str) else {
                continue;
            };
            if !diagnostics.is_empty() {
                next_published.insert(uri_str.clone());
            }
            let params = PublishDiagnosticsParams {
                uri,
                diagnostics,
                version: versions.get(uri_str.as_str()).copied(),
            };
            let _ = sender.send(Message::Notification(lsp_server::Notification::new(
                "textDocument/publishDiagnostics".to_string(),
                params,
            )));
        }
        published = next_published;
    }
}

/// Findings keyed by the uri they belong to.
type Diagnostics = HashMap<String, Vec<lsp_types::Diagnostic>>;

/// Tell the client about a failure the first time it comes up. The
/// same failure recurs on every keystroke until it is fixed, and one
/// popup per keystroke is worse than the silence it replaces.
fn announce(
    sender: &crossbeam_channel::Sender<Message>,
    announced: &mut HashSet<String>,
    report: &Report,
) {
    if !announced.insert(report.message.clone()) {
        return;
    }
    // What the user has to act on is an error; the rest is background
    // for whoever reads the log.
    let message = report.message.clone();
    let notification = if report.show {
        let typ = lsp_types::MessageType::ERROR;
        lsp_server::Notification::new(
            lsp_types::notification::ShowMessage::METHOD.to_string(),
            lsp_types::ShowMessageParams { typ, message },
        )
    } else {
        let typ = lsp_types::MessageType::WARNING;
        lsp_server::Notification::new(
            lsp_types::notification::LogMessage::METHOD.to_string(),
            lsp_types::LogMessageParams { typ, message },
        )
    };
    let _ = sender.send(Message::Notification(notification));
}

/// One workspace cycle: the findings of every workspace unit, keyed by
/// uri (every unit gets an entry, so stale sets clear).
fn cycle(
    job: &Job,
    library: Option<&std::path::Path>,
    encoding: Encoding,
) -> (Diagnostics, Vec<Report>) {
    // A failure here can only come from the library: the units
    // themselves are already in memory.
    let mut reports: Vec<Report> = Vec::new();
    let from_library = library.is_some();
    let sources = collect_sources(job);
    let mut by_uri: Diagnostics = sources
        .iter()
        .map(|(u, _)| (u.clone(), Vec::new()))
        .collect();

    // The check set, keyed by unit name; one line index per unit with
    // findings, built over the texts that are about to move into the
    // session.
    match check_sources(&sources, library) {
        Err(e) => reports.extend(Report::for_session_failure(&e, from_library)),
        Ok(findings) => {
            let texts: HashMap<&str, &str> = sources
                .iter()
                .map(|(u, t)| (u.as_str(), t.as_str()))
                .collect();
            let mut mappers = UnitMappers::new(encoding);
            for f in findings {
                let Some((&name, &text)) = texts.get_key_value(f.unit.as_str()) else {
                    continue;
                };
                let Some((_, mapper)) = mappers.get(name, || Some((name, text))) else {
                    continue;
                };
                by_uri
                    .entry(f.unit)
                    .or_default()
                    .push(lsp_types::Diagnostic {
                        range: mapper.range(f.span),
                        severity: Some(match f.severity {
                            Severity::Error => DiagnosticSeverity::ERROR,
                            Severity::Warning => DiagnosticSeverity::WARNING,
                        }),
                        source: Some("sysmlv2".to_string()),
                        message: f.message,
                        ..Default::default()
                    });
            }
        }
    }

    // Unused private imports and the lint: a second model build over
    // the same sources (one build, library included); bounded and
    // debounced, so the duplication is acceptable until a shared check
    // pipeline exists.
    let library = library.map(Library::dir);
    let mut session = match Session::from_sources_with_library(sources, library) {
        Ok(session) => session,
        Err(e) => {
            reports.extend(Report::for_session_failure(&e, from_library));
            return (by_uri, reports);
        }
    };
    let unused = session.unused_private_imports();

    // Configurable lint: project policy from the workspace root's
    // sysmlint.json, over the same resolved model. Absent file = every
    // rule at its default severity; unreadable JSON degrades to
    // defaults with the error published on the config file itself —
    // where `lint-config` findings (unknown ids/options) anchor too, so
    // a typo is never silent.
    let config_path = job.root.as_ref().map(|r| r.join("sysmlint.json"));
    let config_uri = config_path.as_ref().map(|p| uri_for_path(p));
    let mut config_errors: Vec<String> = Vec::new();
    let config = match config_path.as_ref().map(std::fs::read_to_string) {
        Some(Ok(text)) => match sysmlv2_lint::Config::from_json(&text) {
            Ok(c) => c,
            Err(e) => {
                config_errors.push(e.to_string());
                sysmlv2_lint::Config::default()
            }
        },
        _ => sysmlv2_lint::Config::default(),
    };
    let push_config = |message: String, by: &mut Diagnostics| {
        let Some(uri) = &config_uri else { return };
        by.entry(uri.clone())
            .or_default()
            .push(lsp_types::Diagnostic {
                range: lsp_types::Range::default(),
                severity: Some(DiagnosticSeverity::WARNING),
                source: Some("sysmlv2 lint".to_string()),
                code: Some(lsp_types::NumberOrString::String("lint-config".to_string())),
                message,
                ..Default::default()
            });
    };
    for e in config_errors.drain(..) {
        push_config(e, &mut by_uri);
    }
    // The units' names and texts, copied out once: the textual lint
    // tier (`indentation`) reads the texts while the resolved model is
    // borrowed mutably, and both tiers' findings map through the same
    // line indexes afterwards. User unit indexes run consecutively from
    // the first one, so a finding's unit indexes straight into this.
    let units: Vec<(String, String)> = session
        .units()
        .map(|(_, n, t)| (n.to_string(), t.to_string()))
        .collect();
    let first_unit = session.units().next().map_or(0, |(i, _, _)| i);
    let unit_at = |unit: usize| {
        unit.checked_sub(first_unit)
            .and_then(|i| units.get(i))
            .map(|(n, t)| (n.as_str(), t.as_str()))
    };
    let lint_sources: Vec<(usize, &str)> = units
        .iter()
        .enumerate()
        .map(|(i, (_, t))| (i + first_unit, t.as_str()))
        .collect();
    let findings = sysmlv2_lint::lint_with_sources(session.resolved(), &config, &lint_sources);

    // One line index per unit, shared by every finding of both tiers.
    let mut mappers = UnitMappers::new(encoding);
    for (unit, span) in unused {
        let Some((name, mapper)) = mappers.get(unit, || unit_at(unit)) else {
            continue;
        };
        by_uri
            .entry(name.to_string())
            .or_default()
            .push(lsp_types::Diagnostic {
                range: mapper.range(span),
                severity: Some(DiagnosticSeverity::WARNING),
                source: Some("sysmlv2".to_string()),
                message: UNUSED_IMPORT_MESSAGE.to_string(),
                tags: Some(vec![DiagnosticTag::UNNECESSARY]),
                ..Default::default()
            });
    }
    for f in findings {
        let severity = match f.severity {
            sysmlv2_lint::Severity::Error => DiagnosticSeverity::ERROR,
            sysmlv2_lint::Severity::Info => DiagnosticSeverity::INFORMATION,
            sysmlv2_lint::Severity::Hint => DiagnosticSeverity::HINT,
            _ => DiagnosticSeverity::WARNING,
        };
        match f.unit.zip(f.span) {
            Some((unit, span)) => {
                let Some((name, mapper)) = mappers.get(unit, || unit_at(unit)) else {
                    continue;
                };
                by_uri
                    .entry(name.to_string())
                    .or_default()
                    .push(lsp_types::Diagnostic {
                        range: mapper.range(span),
                        severity: Some(severity),
                        source: Some("sysmlv2 lint".to_string()),
                        code: Some(lsp_types::NumberOrString::String(f.rule.to_string())),
                        // Dead-model rules render faded, like unused
                        // imports.
                        tags: f
                            .rule
                            .is_dead_model()
                            .then(|| vec![DiagnosticTag::UNNECESSARY]),
                        message: f.message,
                        ..Default::default()
                    });
            }
            None => push_config(f.message, &mut by_uri),
        }
    }
    (by_uri, reports)
}

/// The workspace's sources: every model file under the root (skipping
/// hidden and build directories), re-read from disk each cycle — no file
/// watcher to configure, and off-editor changes are picked up on the
/// next edit — with open-document texts overlaid on top.
fn collect_sources(job: &Job) -> Vec<(String, String)> {
    let mut out = match &job.root {
        Some(root) => root_sources(root),
        None => Vec::new(),
    };
    for (uri, _, text) in &job.docs {
        overlay_source(&mut out, uri, text);
    }
    out
}

/// Every model file under `root` as `(file:// uri, text)`, sorted by
/// uri — the workspace's on-disk units (shared with navigation, which
/// must resolve imports into units that are not open).
pub(crate) fn root_sources(root: &std::path::Path) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() {
                if !name.starts_with('.') && name != "target" && name != "node_modules" {
                    stack.push(path);
                }
            } else if crate::is_model_file(&name) {
                if let Ok(text) = std::fs::read_to_string(&path) {
                    out.push((uri_for_path(&path), text));
                }
            }
        }
    }
    out.sort();
    out
}

/// Overlay one open document's text on the collected sources: replace
/// the on-disk unit the client is editing — under the client's own
/// spelling of its uri, which is what diagnostics must be published
/// under — or append a unit the walk did not find.
pub(crate) fn overlay_source(out: &mut Vec<(String, String)>, uri: &str, text: &str) {
    match out.iter_mut().find(|(u, _)| same_unit(u, uri)) {
        Some(slot) => {
            slot.0 = uri.to_string();
            slot.1 = text.to_string();
        }
        None => out.push((uri.to_string(), text.to_string())),
    }
}

/// Whether two uris name the same unit. Clients disagree with the walk
/// — and with each other — on which characters of a path they escape,
/// and a unit that only *looks* new joins the model a second time, so
/// everything it declares is reported as declared twice.
fn same_unit(a: &str, b: &str) -> bool {
    a == b || matches!((decode(a), decode(b)), (Some(a), Some(b)) if a == b)
}

/// A `file://` uri for an absolute path.
pub(crate) fn uri_for_path(path: &std::path::Path) -> String {
    let mut path = path.display().to_string();
    if std::path::MAIN_SEPARATOR == '\\' {
        path = path.replace('\\', "/");
    }
    // A drive-letter path has no leading separator of its own; the uri
    // needs one, after the empty authority.
    if !path.starts_with('/') {
        path.insert(0, '/');
    }
    format!("file://{}", encode_uri_path(&path))
}

/// Percent-encode a uri path. Everything RFC 3986 allows in a path
/// segment stays literal (the unreserved set, the sub-delimiters, `:`
/// and `@`) along with the separator; every other byte of the UTF-8
/// spelling becomes `%XX`. Leaving the rest raw is not cosmetic: a `#`
/// would start a fragment and a `?` a query, and a non-ASCII byte is
/// not a uri character at all, so the result parses as no uri and that
/// file's diagnostics never reach the client.
pub(crate) fn encode_uri_path(path: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(path.len());
    for b in path.bytes() {
        match b {
            b'A'..=b'Z'
            | b'a'..=b'z'
            | b'0'..=b'9'
            | b'-'
            | b'.'
            | b'_'
            | b'~'
            | b'!'
            | b'$'
            | b'&'
            | b'\''
            | b'('
            | b')'
            | b'*'
            | b'+'
            | b','
            | b';'
            | b'='
            | b':'
            | b'@'
            | b'/' => out.push(b as char),
            b => {
                let _ = write!(out, "%{b:02X}");
            }
        }
    }
    out
}

/// A percent-encoded uri with every `%XX` resolved, as UTF-8. `None`
/// when an escape is truncated or not hexadecimal, or when the bytes it
/// spells are not UTF-8 — nothing names a file there.
fn decode(uri: &str) -> Option<String> {
    if !uri.contains('%') {
        return Some(uri.to_string());
    }
    let bytes = uri.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            out.push(u8::from_str_radix(uri.get(i + 1..i + 3)?, 16).ok()?);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).ok()
}

/// The path for a `file://` uri, from [`uri_for_path`] or from any
/// client: the parsed path component — never a query or a fragment,
/// whatever an unescaped `?` or `#` in a file name would otherwise make
/// of them — with every escape resolved, whatever the client escaped.
pub(crate) fn path_for_uri(uri: &Uri) -> Option<PathBuf> {
    if !uri
        .scheme()
        .is_some_and(|s| s.as_str().eq_ignore_ascii_case("file"))
    {
        return None;
    }
    let path = decode(uri.path().as_str())?;
    // `/C:/dir/file`: the leading separator belongs to the empty
    // authority, not to a drive-letter path. Only where drive letters
    // are what paths start with, though — elsewhere `/a:/b` is an
    // ordinary absolute path whose first segment happens to hold a
    // colon, and dropping its root would make it relative.
    let drive_letter = |rest: &str| {
        let b = rest.as_bytes();
        cfg!(windows) && b.first().is_some_and(u8::is_ascii_alphabetic) && b.get(1) == Some(&b':')
    };
    let path = match path.strip_prefix('/') {
        Some(rest) if drive_letter(rest) => rest,
        _ => &path,
    };
    Some(PathBuf::from(path))
}

#[cfg(test)]
mod tests {
    use super::*;
    use sysmlv2_parser::parser::MAX_NESTING;

    const PANIC_TEXT: &str = "the model gave up";
    const FAILURE_TEXT: &str = "the library could not be read";

    /// A worker whose thread never started used to disable the model
    /// tier in silence: half the findings an editor shows stopped
    /// arriving with nothing said, and asking for a stack the size the
    /// parser's bound needs is exactly what makes a host refuse. What
    /// the system said goes to the log, and what the session loses goes
    /// to the client.
    #[test]
    fn a_worker_whose_thread_is_refused_says_so() {
        let (out, messages) = crossbeam_channel::unbounded();
        let refused = std::io::Error::new(std::io::ErrorKind::OutOfMemory, "no room for a thread");
        let worker = Worker::unstarted(&out, &refused);
        // Still a worker, and still one that swallows jobs.
        worker.schedule(Job {
            docs: Vec::new(),
            root: None,
        });

        let sent: Vec<(String, String)> = messages
            .try_iter()
            .map(|m| {
                let Message::Notification(n) = m else {
                    panic!("{m:?}")
                };
                (n.method, n.params["message"].as_str().unwrap().to_string())
            })
            .collect();
        let methods: Vec<&str> = sent.iter().map(|(m, _)| m.as_str()).collect();
        assert_eq!(
            methods,
            ["window/logMessage", "window/showMessage"],
            "{sent:?}"
        );
        assert!(sent[0].1.contains("no room for a thread"), "{sent:?}");
        for (_, message) in &sent {
            assert!(message.contains("model tier is off"), "{sent:?}");
        }
    }

    /// Input nested to the parser's bound is ordinary input — a
    /// kilobyte and a half of it here, with nothing to report — and the
    /// bound only reports what it bounds on a stack sized for it. On the
    /// two megabytes a thread gets when it asks for nothing, the descent
    /// ends the process: no diagnostic, no unwind, no server.
    ///
    /// The worker is started here exactly as the server starts it, so
    /// what this runs on is the stack it really runs on. A worker whose
    /// reservation went missing does not fail this test — it ends the
    /// test process.
    #[test]
    fn the_worker_parses_at_the_nesting_bound() {
        // One level is the package, so the braces within it stop one
        // short of the bound.
        let levels = MAX_NESTING as usize - 1;
        let deep = format!(
            "package P {{ {}part x;{} }}",
            "part x { ".repeat(levels),
            "}".repeat(levels)
        );
        // Nesting that also carries a full operator chain at every
        // level: the same descent with the widest expression the parser
        // admits hanging off it.
        let chain = (0..960)
            .map(|i| format!("a{i} > 0"))
            .collect::<Vec<_>>()
            .join(" and ");
        let wide = format!(
            "package P {{ {}part y;{} }}",
            format!("part x {{ attribute v = {chain}; ").repeat(60),
            "}".repeat(60)
        );

        // A clean document publishes nothing at all — an empty set is
        // only sent to clear findings already shown — so each job
        // carries a second document that does have something to say.
        // Its publish is the signal that the cycle ran to the end, and
        // the deep document's silence is the finding count being zero.
        const MARKER: &str = "file:///w/marker.sysml";
        let (out, messages) = crossbeam_channel::unbounded();
        let worker = Worker::spawn(out, None, Encoding::Utf8, Duration::from_millis(1));
        for (name, text) in [("deep", deep), ("wide", wide)] {
            let uri = format!("file:///w/{name}.sysml");
            worker.schedule(Job {
                docs: vec![
                    (uri.clone(), 1, text.into()),
                    (MARKER.to_string(), 1, "package".into()),
                ],
                root: None,
            });
            let deadline = std::time::Instant::now() + Duration::from_secs(60);
            loop {
                let m = messages
                    .recv_deadline(deadline)
                    .expect("the worker answers every job");
                let Message::Notification(n) = m else {
                    continue;
                };
                assert_eq!(n.method, "textDocument/publishDiagnostics", "{n:?}");
                assert_eq!(
                    n.params["uri"], MARKER,
                    "{name}: nesting the parser accepts has nothing to report"
                );
                assert!(
                    n.params["diagnostics"]
                        .as_array()
                        .is_some_and(|d| !d.is_empty()),
                    "{}: the marker's own finding: {}",
                    name,
                    n.params
                );
                break;
            }
        }
    }

    /// A cycle that gives up on a document whose text is its own panic
    /// message, reports a failure for one whose text asks for it, and
    /// otherwise yields one finding per document.
    fn flaky_cycle(
        job: &Job,
        _library: Option<&std::path::Path>,
        _encoding: Encoding,
    ) -> (Diagnostics, Vec<Report>) {
        let mut reports = Vec::new();
        let by_uri = job
            .docs
            .iter()
            .map(|(uri, _, text)| {
                assert_ne!(&**text, PANIC_TEXT, "{PANIC_TEXT}");
                if &**text == FAILURE_TEXT {
                    reports.push(Report {
                        show: true,
                        message: FAILURE_TEXT.to_string(),
                    });
                }
                (
                    uri.clone(),
                    vec![lsp_types::Diagnostic {
                        message: text.to_string(),
                        ..Default::default()
                    }],
                )
            })
            .collect();
        (by_uri, reports)
    }

    /// A cycle that panics used to end the worker thread, after which
    /// every later job vanished into a dead channel and the editor kept
    /// its findings for good with nothing said. It is announced once
    /// instead, and the next job publishes as usual — as is a cycle
    /// that ran but could not build the model.
    #[test]
    fn a_failed_cycle_is_announced_once_and_the_worker_keeps_serving() {
        let (tx, rx) = mpsc::channel::<Job>();
        let (out, messages) = crossbeam_channel::unbounded();
        let worker = std::thread::spawn(move || {
            run(
                &rx,
                &out,
                None,
                Encoding::Utf8,
                Duration::from_millis(1),
                flaky_cycle,
            );
        });
        let job = |text: &str| Job {
            docs: vec![("file:///w/m.sysml".to_string(), 1, text.into())],
            root: None,
        };
        let next = |kind: &str| -> serde_json::Value {
            let deadline = std::time::Instant::now() + Duration::from_secs(10);
            loop {
                let m = messages
                    .recv_deadline(deadline)
                    .expect("the worker answers every job");
                let Message::Notification(n) = m else {
                    continue;
                };
                assert_eq!(n.method, kind, "{n:?}");
                return n.params;
            }
        };

        tx.send(job(PANIC_TEXT)).expect("worker alive");
        let params = next("window/showMessage");
        assert!(
            params["message"].as_str().unwrap().contains(PANIC_TEXT),
            "{params}"
        );

        tx.send(job("first")).expect("worker alive");
        let params = next("textDocument/publishDiagnostics");
        assert_eq!(params["diagnostics"][0]["message"], "first", "{params}");

        // The same failure again says nothing more; the job after it
        // still publishes, and its publish is the next message out.
        tx.send(job(PANIC_TEXT)).expect("worker alive");
        tx.send(job("second")).expect("worker alive");
        let params = next("textDocument/publishDiagnostics");
        assert_eq!(params["diagnostics"][0]["message"], "second", "{params}");

        // A cycle that ran but could not build the model says so once
        // too: an empty finding set on its own reads as "no problems".
        tx.send(job(FAILURE_TEXT)).expect("worker alive");
        let params = next("window/showMessage");
        assert_eq!(params["message"], FAILURE_TEXT, "{params}");
        let params = next("textDocument/publishDiagnostics");
        assert_eq!(
            params["diagnostics"][0]["message"], FAILURE_TEXT,
            "{params}"
        );
        tx.send(job(FAILURE_TEXT)).expect("worker alive");
        let params = next("textDocument/publishDiagnostics");
        assert_eq!(
            params["diagnostics"][0]["message"], FAILURE_TEXT,
            "the same failure is not announced twice: {params}"
        );

        drop(tx);
        worker.join().expect("the worker ends with its channel");
    }

    /// Paths a corpus really contains — a space, an accent, a `#`, a
    /// `%` — survive the round trip, and the uri they produce is one a
    /// client can parse. A raw `#` or `?` would otherwise start a
    /// fragment or a query and a raw non-ASCII byte is no uri character
    /// at all, leaving a uri nothing can be published against.
    #[test]
    fn uris_round_trip_the_paths_a_corpus_contains() {
        for path in [
            "/w/models/plain.sysml",
            "/w/my models/Heizöl.sysml",
            "/w/a#b/c?d.sysml",
            "/w/100%/x.kerml",
            "/w/日本語/モデル.sysml",
            "/w/punct/a+b,c;d=e:f@g!h$i&j'k(l)m*n.sysml",
        ] {
            let uri = uri_for_path(std::path::Path::new(path));
            let parsed = Uri::from_str(&uri).unwrap_or_else(|e| panic!("{uri}: {e}"));
            assert_eq!(
                path_for_uri(&parsed),
                Some(PathBuf::from(path)),
                "{uri} from {path}"
            );
        }
        // The sub-delimiters a path may carry literally are not
        // escaped, so the spelling stays the one clients use.
        assert_eq!(
            uri_for_path(std::path::Path::new("/w/a+b/c.sysml")),
            "file:///w/a+b/c.sysml"
        );
        assert_eq!(
            uri_for_path(std::path::Path::new("/w/a#b.sysml")),
            "file:///w/a%23b.sysml"
        );
        // Why those two have to be escaped: a raw non-ASCII byte is no
        // uri character, and a raw `#` ends the path and starts a
        // fragment.
        assert!(Uri::from_str("file:///w/Heizöl.sysml").is_err());
        assert_eq!(
            path_for_uri(&Uri::from_str("file:///w/a#b.sysml").unwrap()),
            Some(PathBuf::from("/w/a"))
        );
    }

    /// A client that escapes more than the walk does — the drive-letter
    /// form a Windows client sends, or an escaped separator — still
    /// names a path, and a malformed escape names none.
    #[test]
    fn a_clients_own_escaping_still_names_a_path() {
        let path = |s: &str| path_for_uri(&Uri::from_str(s).unwrap());
        // Where paths begin with a drive letter the root separator is
        // the empty authority's and comes off; everywhere else the same
        // spelling is an ordinary absolute path and keeps its root.
        let drive = |p: &str| {
            Some(PathBuf::from(if cfg!(windows) {
                p.to_string()
            } else {
                format!("/{p}")
            }))
        };
        assert_eq!(path("file:///c%3A/w/m.sysml"), drive("c:/w/m.sysml"));
        assert_eq!(path("file:///c:/w/m.sysml"), drive("c:/w/m.sysml"));
        // A first segment that merely contains a colon is not a drive.
        assert_eq!(
            path("file:///a:b/m.sysml"),
            Some(PathBuf::from("/a:b/m.sysml"))
        );
        assert_eq!(
            path("file:///w/%E6%97%A5/m.sysml"),
            Some(PathBuf::from("/w/日/m.sysml"))
        );
        assert_eq!(path("sysmlv2-lib:/Lib.sysml"), None, "another scheme");
        // A well-formed escape that spells no text names no file; a
        // malformed one is not a uri to begin with.
        assert_eq!(path("file:///w/%FF.sysml"), None, "not UTF-8");
        assert!(Uri::from_str("file:///w/a%2").is_err());
        assert!(Uri::from_str("file:///w/a%zz").is_err());
    }

    /// An open document overlays the on-disk unit it edits even when
    /// the client spells the uri with different escapes, and the unit
    /// takes the client's spelling — the one its diagnostics must be
    /// published under. Appending it instead would put the same
    /// declarations into the model twice.
    #[test]
    fn an_open_document_overlays_its_on_disk_unit() {
        let mut sources = vec![
            ("file:///w/a.sysml".to_string(), "package A;".to_string()),
            (
                "file:///w/my+dir/b.sysml".to_string(),
                "package B;".to_string(),
            ),
        ];
        overlay_source(&mut sources, "file:///w/my%2Bdir/b.sysml", "package B2;");
        assert_eq!(sources.len(), 2, "{sources:?}");
        assert_eq!(
            sources[1],
            (
                "file:///w/my%2Bdir/b.sysml".to_string(),
                "package B2;".to_string()
            )
        );
        overlay_source(&mut sources, "file:///w/c.sysml", "package C;");
        assert_eq!(sources.len(), 3, "a unit the walk did not find is added");
    }
}
