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

use crate::position::{Encoding, Mapper};
use lsp_server::Message;
use lsp_types::{DiagnosticSeverity, DiagnosticTag, PublishDiagnosticsParams, Uri};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::mpsc;
use std::time::Duration;
use sysmlv2_transform::{Session, Severity, check_sources};

pub(crate) const UNUSED_IMPORT_MESSAGE: &str = "unused private import";

pub(crate) struct Job {
    /// (uri, version, text) of every open document.
    pub docs: Vec<(String, i32, String)>,
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
        std::thread::spawn(move || run(rx, sender, library, encoding, debounce));
        Worker { tx }
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

fn run(
    rx: mpsc::Receiver<Job>,
    sender: crossbeam_channel::Sender<Message>,
    library: Option<PathBuf>,
    encoding: Encoding,
    debounce: Duration,
) {
    // Uris published last cycle — files whose findings vanish (or which
    // drop out of the workspace) publish an empty set once to clear.
    let mut published: HashSet<String> = HashSet::new();
    let mut pending: Option<Job> = None;
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

        let sources = collect_sources(&job);
        let versions: HashMap<&str, i32> =
            job.docs.iter().map(|(u, v, _)| (u.as_str(), *v)).collect();

        // Findings per uri (every workspace file gets an entry so stale
        // sets clear).
        let mut by_uri: HashMap<String, Vec<lsp_types::Diagnostic>> = sources
            .iter()
            .map(|(u, _)| (u.clone(), Vec::new()))
            .collect();

        let named: Vec<(String, String)> = sources.clone();
        if let Ok(findings) = check_sources(&named, library.as_deref()) {
            for f in findings {
                let Some((_, text)) = sources.iter().find(|(u, _)| *u == f.unit) else {
                    continue;
                };
                let mapper = Mapper::new(text, encoding);
                by_uri
                    .entry(f.unit.clone())
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

        // Unused private imports: a second model build; bounded
        // and debounced, so the duplication is acceptable until a shared
        // check pipeline exists.
        let session = Session::from_sources(named);
        let session = match (&library, session) {
            (Some(dir), Ok(s)) => s.with_library(dir).ok(),
            (None, Ok(s)) => Some(s),
            (_, Err(_)) => None,
        };
        if let Some(mut session) = session {
            for (unit, span) in session.unused_private_imports() {
                let Some((_, name, text)) = session.units().find(|(i, _, _)| *i == unit) else {
                    continue;
                };
                let mapper = Mapper::new(text, encoding);
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

            // Configurable lint: project policy from the
            // workspace root's sysmlint.json, over the same resolved
            // model. Absent file = every rule at its default severity;
            // unreadable JSON degrades to defaults with the error
            // published on the config file itself — where `lint-config`
            // findings (unknown ids/options) anchor too, so a typo is
            // never silent.
            let config_path = job.root.as_ref().map(|r| r.join("sysmlint.json"));
            let config_uri = config_path.as_ref().map(|p| uri_for_path(p));
            let mut config_errors: Vec<String> = Vec::new();
            let config = match config_path.as_ref().map(std::fs::read_to_string) {
                Some(Ok(text)) => match sysmlv2_lint::Config::from_json(&text) {
                    Ok(c) => c,
                    Err(e) => {
                        config_errors.push(e);
                        sysmlv2_lint::Config::default()
                    }
                },
                _ => sysmlv2_lint::Config::default(),
            };
            let unit_texts: Vec<(usize, String, String)> = session
                .units()
                .map(|(i, n, t)| (i, n.to_string(), t.to_string()))
                .collect();
            let push_config =
                |message: String, by: &mut HashMap<String, Vec<lsp_types::Diagnostic>>| {
                    let Some(uri) = &config_uri else { return };
                    by.entry(uri.clone())
                        .or_default()
                        .push(lsp_types::Diagnostic {
                            range: lsp_types::Range::default(),
                            severity: Some(DiagnosticSeverity::WARNING),
                            source: Some("sysmlv2 lint".to_string()),
                            code: Some(lsp_types::NumberOrString::String(
                                "lint-config".to_string(),
                            )),
                            message,
                            ..Default::default()
                        });
                };
            for e in config_errors.drain(..) {
                push_config(e, &mut by_uri);
            }
            // The textual tier (`indentation`) reads the units' source text.
            let sources: Vec<(usize, &str)> = unit_texts
                .iter()
                .map(|(i, _, t)| (*i, t.as_str()))
                .collect();
            for f in sysmlv2_lint::lint_with_sources(session.resolved(), &config, &sources) {
                let severity = match f.severity {
                    sysmlv2_lint::Severity::Error => DiagnosticSeverity::ERROR,
                    sysmlv2_lint::Severity::Info => DiagnosticSeverity::INFORMATION,
                    sysmlv2_lint::Severity::Hint => DiagnosticSeverity::HINT,
                    _ => DiagnosticSeverity::WARNING,
                };
                match f.unit.zip(f.span) {
                    Some((unit, span)) => {
                        let Some((_, name, text)) = unit_texts.iter().find(|(i, _, _)| *i == unit)
                        else {
                            continue;
                        };
                        let mapper = Mapper::new(text, encoding);
                        by_uri
                            .entry(name.clone())
                            .or_default()
                            .push(lsp_types::Diagnostic {
                                range: mapper.range(span),
                                severity: Some(severity),
                                source: Some("sysmlv2 lint".to_string()),
                                code: Some(lsp_types::NumberOrString::String(f.rule.to_string())),
                                // Dead-model rules render faded, like
                                // unused imports.
                                tags: f
                                    .rule
                                    .starts_with("unused-")
                                    .then(|| vec![DiagnosticTag::UNNECESSARY]),
                                message: f.message,
                                ..Default::default()
                            });
                    }
                    None => push_config(f.message, &mut by_uri),
                }
            }
        }

        // Latest-only: a job that arrived during computation wins.
        if let Ok(newer) = rx.try_recv() {
            pending = Some(newer);
            continue;
        }

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
            } else if name.ends_with(".sysml") || name.ends_with(".kerml") {
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
/// the on-disk unit under the same uri, or append a unit the walk did
/// not find.
pub(crate) fn overlay_source(out: &mut Vec<(String, String)>, uri: &str, text: &str) {
    match out.iter_mut().find(|(u, _)| u == uri) {
        Some(slot) => slot.1 = text.to_string(),
        None => out.push((uri.to_string(), text.to_string())),
    }
}

/// A `file://` uri for an absolute path (space and percent encoded — the
/// characters that actually occur in model corpora).
pub(crate) fn uri_for_path(path: &std::path::Path) -> String {
    let mut out = String::from("file://");
    for c in path.display().to_string().chars() {
        match c {
            ' ' => out.push_str("%20"),
            '%' => out.push_str("%25"),
            c => out.push(c),
        }
    }
    out
}

/// The path for a `file://` uri produced by [`uri_for_path`] or a client.
pub(crate) fn path_for_uri(uri: &Uri) -> Option<PathBuf> {
    let s = uri.as_str().strip_prefix("file://")?;
    Some(PathBuf::from(s.replace("%20", " ").replace("%25", "%")))
}
