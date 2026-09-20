#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Workspace-tier harness: the debounced worker's
//! publishes and the code actions riding them, through the wire with a
//! short debounce.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{CodeActionRequest, Initialize, Shutdown};
use lsp_types::{
    CodeActionContext, CodeActionKind, CodeActionOrCommand, CodeActionParams, DiagnosticSeverity,
    DiagnosticTag, DidChangeTextDocumentParams, DidOpenTextDocumentParams, InitializeParams,
    PublishDiagnosticsParams, Range, TextDocumentContentChangeEvent, TextDocumentIdentifier,
    TextDocumentItem, Uri, VersionedTextDocumentIdentifier,
};
use std::str::FromStr;
use std::thread::JoinHandle;
use std::time::Duration;

struct Client {
    conn: Connection,
    server: Option<JoinHandle<Result<(), Box<dyn std::error::Error + Send + Sync>>>>,
    next_id: i32,
}

fn uri(name: &str) -> Uri {
    Uri::from_str(&format!("file:///w/{name}")).unwrap()
}

/// A `file://` uri for a real path, percent-encoding every byte a uri
/// path may not carry — the spelling the client and the server's
/// workspace walk have to agree on.
fn file_uri(path: &std::path::Path) -> Uri {
    use std::fmt::Write as _;
    let mut out = String::from("file://");
    for b in path.display().to_string().bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' => out.push(b as char),
            b'-' | b'.' | b'_' | b'~' | b'/' | b':' | b'@' => out.push(b as char),
            b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b',' | b';' | b'=' => {
                out.push(b as char);
            }
            b => {
                let _ = write!(out, "%{b:02X}");
            }
        }
    }
    Uri::from_str(&out).unwrap()
}

impl Client {
    fn start(root: Option<&std::path::Path>) -> Client {
        Self::start_with_library(root, None)
    }

    /// [`Self::start`] with a standard-library directory for the
    /// workspace tier's referential and semantic checks.
    fn start_with_library(
        root: Option<&std::path::Path>,
        library: Option<std::path::PathBuf>,
    ) -> Client {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || {
            sysmlv2_lsp::run_with_options(server_side, library, Duration::from_millis(50))
        });
        let mut c = Client {
            conn: client_side,
            server: Some(server),
            next_id: 0,
        };
        #[allow(deprecated)]
        let params = InitializeParams {
            root_uri: root.map(|p| {
                Uri::from_str(&format!(
                    "file://{}",
                    p.display().to_string().replace(' ', "%20")
                ))
                .unwrap()
            }),
            ..Default::default()
        };
        let _: lsp_types::InitializeResult = c.request_ok::<Initialize>(params);
        c.notify::<Initialized>(lsp_types::InitializedParams {});
        c
    }

    fn request_ok<R: lsp_types::request::Request>(&mut self, params: R::Params) -> R::Result {
        self.next_id += 1;
        let id = RequestId::from(self.next_id);
        self.conn
            .sender
            .send(Message::Request(Request::new(
                id.clone(),
                R::METHOD.to_string(),
                params,
            )))
            .unwrap();
        loop {
            match self.conn.receiver.recv().unwrap() {
                Message::Response(Response {
                    id: rid,
                    response_result,
                }) if rid == id => {
                    let (result, error) = match response_result {
                        Ok(v) => (Some(v), None),
                        Err(e) => (None, Some(e)),
                    };
                    assert!(error.is_none(), "{error:?}");
                    return serde_json::from_value(result.unwrap_or_default()).unwrap();
                }
                _ => continue,
            }
        }
    }

    /// A request by method name (the server's custom methods), answered
    /// as the raw result or the error the server sent.
    fn request_raw(
        &mut self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<serde_json::Value, lsp_server::ResponseError> {
        self.next_id += 1;
        let id = RequestId::from(self.next_id);
        self.conn
            .sender
            .send(Message::Request(Request::new(
                id.clone(),
                method.to_string(),
                params,
            )))
            .unwrap();
        loop {
            match self.conn.receiver.recv().unwrap() {
                Message::Response(Response {
                    id: rid,
                    response_result,
                }) if rid == id => {
                    return response_result;
                }
                _ => continue,
            }
        }
    }

    fn notify<N: lsp_types::notification::Notification>(&self, params: N::Params) {
        self.conn
            .sender
            .send(Message::Notification(Notification::new(
                N::METHOD.to_string(),
                params,
            )))
            .unwrap();
    }

    fn open(&self, uri: &Uri, text: &str) {
        self.notify::<DidOpenTextDocument>(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: uri.clone(),
                language_id: "sysml".to_string(),
                version: 1,
                text: text.to_string(),
            },
        });
    }

    fn change(&self, uri: &Uri, version: i32, text: &str) {
        self.notify::<DidChangeTextDocument>(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: uri.clone(),
                version,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: text.to_string(),
            }],
        });
    }

    /// The next publish for `target` that satisfies `pred` (the worker's
    /// publishes interleave with the syntax tier's).
    fn await_publish(
        &self,
        target: &Uri,
        pred: impl Fn(&PublishDiagnosticsParams) -> bool,
    ) -> PublishDiagnosticsParams {
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        loop {
            let msg = self
                .conn
                .receiver
                .recv_timeout(deadline - std::time::Instant::now())
                .expect("timed out waiting for a publish");
            if let Message::Notification(n) = msg {
                if n.method == "textDocument/publishDiagnostics" {
                    let p: PublishDiagnosticsParams = serde_json::from_value(n.params).unwrap();
                    if p.uri == *target && pred(&p) {
                        return p;
                    }
                }
            }
        }
    }

    fn shutdown(mut self) {
        self.request_ok::<Shutdown>(());
        self.notify::<Exit>(());
        self.server
            .take()
            .unwrap()
            .join()
            .expect("server thread panicked")
            .expect("server main loop errored");
    }
}

const DEFS: &str = "package Defs { part def Wheel; }\n";
const UNUSED: &str = "package U {\n    private import Defs::*;\n    part def P;\n}\n";

#[test]
fn worker_reports_unused_import_and_quickfix_removes_it() {
    let client = Client::start(None);
    let defs = uri("defs.sysml");
    let unused = uri("u.sysml");
    client.open(&defs, DEFS);
    client.open(&unused, UNUSED);

    // The workspace tier publishes the unused-import warning, tagged
    // UNNECESSARY (renders faded), version-guarded.
    let p = client.await_publish(&unused, |p| {
        p.diagnostics
            .iter()
            .any(|d| d.message == "unused private import")
    });
    assert_eq!(p.version, Some(1));
    let diag = p
        .diagnostics
        .iter()
        .find(|d| d.message == "unused private import")
        .unwrap()
        .clone();
    assert_eq!(
        diag.tags.as_deref(),
        Some(&[DiagnosticTag::UNNECESSARY][..])
    );
    assert_eq!(diag.range.start.line, 1, "the import member's line");

    // The quickfix rides the diagnostic.
    let mut c = client;
    let actions: Option<Vec<CodeActionOrCommand>> =
        c.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier {
                uri: unused.clone(),
            },
            range: diag.range,
            context: CodeActionContext {
                diagnostics: vec![diag.clone()],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let CodeActionOrCommand::CodeAction(fix) = &actions[0] else {
        panic!("expected a code action: {actions:?}");
    };
    assert_eq!(fix.title, "Remove unused import");
    assert_eq!(fix.kind, Some(CodeActionKind::QUICKFIX));
    let edit = &fix.edit.as_ref().unwrap().changes.as_ref().unwrap()[&unused][0];
    assert_eq!(edit.new_text, "");
    assert_eq!(edit.range, diag.range);

    // Apply the fix: the warning clears on the next worker cycle.
    let fixed = "package U {\n    \n    part def P;\n}\n";
    c.change(&unused, 2, fixed);
    let p = client_await_clear(&c, &unused);
    assert_eq!(p.version, Some(2));
    c.shutdown();
}

/// Several findings in one unit, and findings in several units, each
/// land on their own line: the line index a cycle builds once per unit
/// serves every finding of that unit.
#[test]
fn worker_maps_every_finding_of_a_unit_and_of_every_unit() {
    let client = Client::start(None);
    let defs = uri("defs.sysml");
    let a = uri("a.sysml");
    let b = uri("b.sysml");
    client.open(
        &defs,
        "package D1 { part def Wheel; }\npackage D2 { part def Axle; }\npackage D3 { part def Cog; }\n",
    );
    client.open(
        &a,
        "package A {\n    private import D1::Wheel;\n    private import D2::Axle;\n    part def P;\n}\n",
    );
    client.open(
        &b,
        "package B {\n    part def Q;\n    private import D3::Cog;\n}\n",
    );
    let unused = |p: &PublishDiagnosticsParams| -> Vec<(u32, u32, u32)> {
        p.diagnostics
            .iter()
            .filter(|d| d.message == "unused private import")
            .map(|d| {
                (
                    d.range.start.line,
                    d.range.start.character,
                    d.range.end.line,
                )
            })
            .collect()
    };
    // One cycle publishes both units in no particular order: take the
    // first publish of each that carries its warnings.
    let mut got: std::collections::HashMap<Uri, PublishDiagnosticsParams> =
        std::collections::HashMap::new();
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    while got.len() < 2 {
        let msg = client
            .conn
            .receiver
            .recv_timeout(deadline - std::time::Instant::now())
            .expect("timed out waiting for the publishes");
        if let Message::Notification(n) = msg {
            if n.method == "textDocument/publishDiagnostics" {
                let p: PublishDiagnosticsParams = serde_json::from_value(n.params).unwrap();
                if (p.uri == a || p.uri == b) && !unused(&p).is_empty() {
                    got.entry(p.uri.clone()).or_insert(p);
                }
            }
        }
    }
    assert_eq!(unused(&got[&a]), [(1, 4, 1), (2, 4, 2)]);
    assert_eq!(unused(&got[&b]), [(2, 4, 2)]);
    client.shutdown();
}

/// A model file whose name is not plain ASCII, and carries a character
/// a uri gives its own meaning, is published like any other: its uri
/// has to be one the client can parse, or that file's findings never
/// leave the server. Opening it then replaces the unit the walk found
/// rather than joining the model a second time.
#[test]
fn a_non_ascii_workspace_path_publishes_and_overlays_when_opened() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-lsp-ws-uri-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    // Han characters: no canonical decomposition, so the name on disk
    // reads back byte for byte on every filesystem.
    let path = dir.join("日本語 #1.sysml");
    std::fs::write(&path, "package P { part def Wheel;\n").unwrap();

    let client = Client::start(Some(&dir));
    // Any open document triggers a workspace cycle.
    client.open(&uri("probe.sysml"), "package OK;\n");

    let target = file_uri(&path);
    let p = client.await_publish(&target, |p| !p.diagnostics.is_empty());
    assert!(
        p.diagnostics.iter().any(|d| d.message.contains("expected")),
        "{:?}",
        p.diagnostics
    );
    assert_eq!(p.version, None, "closed files publish without a version");

    // Opening it with the error fixed clears the file's findings: the
    // open text replaced the unit on disk. A second unit under the same
    // path would keep publishing the broken text's findings, and would
    // declare `P` twice besides.
    client.open(&target, "package P { part def Wheel; }\n");
    let p = client.await_publish(&target, |p| p.version == Some(1));
    assert_eq!(p.diagnostics, Vec::new(), "{:?}", p.diagnostics);
    client.shutdown();
}

fn client_await_clear(c: &Client, target: &Uri) -> PublishDiagnosticsParams {
    c.await_publish(target, |p| {
        p.version == Some(2)
            && p.diagnostics
                .iter()
                .all(|d| d.message != "unused private import")
    })
}

#[test]
fn worker_publishes_scoped_lint_findings_from_sysmlint_json() {
    // A workspace-root sysmlint.json drives the lint tier:
    // rule findings carry the rule id as the diagnostic code (dead-
    // model rules tagged UNNECESSARY), and configuration complaints
    // anchor on the config file itself.
    let dir = std::env::temp_dir().join(format!("sysmlv2-lsp-lint-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("sysmlint.json"),
        r#"{ "rules": { "unused-definition": { "scopes": { "PartDefinition": "warn" } }, "no-such-rule": "warn" } }"#,
    )
    .unwrap();

    let client = Client::start(Some(&dir));
    let m = uri("m.sysml");
    client.open(
        &m,
        "package P { part def Wheel; part def Orphan; part w : Wheel; }\n",
    );

    let p = client.await_publish(&m, |p| {
        p.diagnostics
            .iter()
            .any(|d| d.source.as_deref() == Some("sysmlv2 lint"))
    });
    let lint: Vec<_> = p
        .diagnostics
        .iter()
        .filter(|d| d.source.as_deref() == Some("sysmlv2 lint"))
        .collect();
    // The scope enables exactly the part-def stereotype of an
    // off-by-default rule; Wheel is referenced, Orphan is not.
    assert_eq!(lint.len(), 1, "{lint:?}");
    assert!(lint[0].message.contains("`Orphan`"), "{}", lint[0].message);
    assert_eq!(
        lint[0].code,
        Some(lsp_types::NumberOrString::String(
            "unused-definition".to_string()
        ))
    );
    assert_eq!(
        lint[0].tags.as_deref(),
        Some(&[DiagnosticTag::UNNECESSARY][..])
    );

    // The unknown-rule complaint lands on the config file. Trigger a
    // fresh cycle so its publish is observable after the model's.
    client.change(
        &m,
        2,
        "package P { part def Wheel; part def Orphan; part w : Wheel; }\n\n",
    );
    let cfg_uri = Uri::from_str(&format!(
        "file://{}",
        dir.join("sysmlint.json")
            .display()
            .to_string()
            .replace(' ', "%20")
    ))
    .unwrap();
    let pc = client.await_publish(&cfg_uri, |p| {
        p.diagnostics
            .iter()
            .any(|d| d.message.contains("no-such-rule"))
    });
    let complaint = pc
        .diagnostics
        .iter()
        .find(|d| d.message.contains("no-such-rule"))
        .unwrap();
    assert_eq!(
        complaint.code,
        Some(lsp_types::NumberOrString::String("lint-config".to_string()))
    );
    client.shutdown();
}

#[test]
fn workspace_root_files_get_diagnostics_without_being_open() {
    // A broken file on disk under the workspace root: the worker reads
    // it and publishes its parse error even though it was never opened.
    let dir = std::env::temp_dir().join(format!("sysmlv2-lsp-ws-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("broken.sysml"), "part def P {\n").unwrap();

    let client = Client::start(Some(&dir));
    // Any open document triggers a workspace cycle.
    let probe = uri("probe.sysml");
    client.open(&probe, "package OK;\n");

    let broken_uri = Uri::from_str(&format!(
        "file://{}",
        dir.join("broken.sysml")
            .display()
            .to_string()
            .replace(' ', "%20")
    ))
    .unwrap();
    let p = client.await_publish(&broken_uri, |p| !p.diagnostics.is_empty());
    assert!(
        p.diagnostics[0].message.contains("expected"),
        "{:?}",
        p.diagnostics
    );
    assert_eq!(p.version, None, "closed files publish without a version");
    client.shutdown();
}

#[test]
fn worker_reports_user_roots_shadowing_library_roots() {
    // A library directory with one standard root package; a user
    // document declaring a root package of the same name gets the
    // referential warning at the declaration's name, severity warning.
    let lib = std::env::temp_dir().join(format!(
        "sysmlv2-lsp-shadow-lib-test-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&lib);
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(
        lib.join("Requirements.sysml"),
        "standard library package Requirements { requirement def Base; }\n",
    )
    .unwrap();

    let client = Client::start_with_library(None, Some(lib));
    let u = uri("shadow.sysml");
    client.open(
        &u,
        "package Requirements {\n    requirement def Speed;\n}\n",
    );
    let p = client.await_publish(&u, |p| {
        p.diagnostics
            .iter()
            .any(|d| d.message.starts_with("root package"))
    });
    let diag = p
        .diagnostics
        .iter()
        .find(|d| d.message.starts_with("root package"))
        .unwrap();
    assert_eq!(
        diag.message,
        "root package `Requirements` shadows the standard library package `Requirements`; \
         references resolve to the library"
    );
    assert_eq!(diag.severity, Some(DiagnosticSeverity::WARNING));
    assert_eq!(diag.source.as_deref(), Some("sysmlv2"));
    assert_eq!(diag.range.start, lsp_types::Position::new(0, 8));
    assert_eq!(diag.range.end, lsp_types::Position::new(0, 20));
    assert_eq!(p.version, Some(1));
    client.shutdown();
}

#[test]
fn visibility_quickfix_rides_the_m11a_finding() {
    let mut client = Client::start(None);
    let u = uri("vis.sysml");
    client.open(
        &u,
        "package P {\n    import Defs::*;\n    package Defs { part def W; }\n}\n",
    );
    // The syntax tier publishes the mandatory-visibility finding.
    let p = client.await_publish(&u, |p| {
        p.diagnostics
            .iter()
            .any(|d| d.message.contains("explicit visibility"))
    });
    let diag = p
        .diagnostics
        .iter()
        .find(|d| d.message.contains("explicit visibility"))
        .unwrap()
        .clone();
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: diag.range,
            context: CodeActionContext {
                diagnostics: vec![diag.clone()],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let titles: Vec<&str> = actions
        .iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) => Some(c.title.as_str()),
            _ => None,
        })
        .collect();
    // Nothing resolves through the import, so `private` is computed
    // and leads; the other keywords follow as plain alternatives.
    assert_eq!(
        titles,
        [
            "Make the import `private` (nothing outside uses it)",
            "Make the import `public`",
            "Make the import `protected`"
        ],
        "{titles:?}"
    );
    let CodeActionOrCommand::CodeAction(private) = &actions[0] else {
        unreachable!()
    };
    assert_eq!(private.is_preferred, Some(true));
    let edit = &private.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u][0];
    assert_eq!(edit.new_text, "private ");
    assert_eq!(edit.range.start, edit.range.end, "pure insertion");
    assert_eq!(edit.range.start, diag.range.start, "at the member start");
    client.shutdown();
}

#[test]
fn minimize_qualified_names_source_action() {
    let mut client = Client::start(None);
    let defs = uri("defs.sysml");
    let u = uri("m.sysml");
    client.open(&defs, DEFS);
    client.open(
        &u,
        "package M {\n    private import Defs::*;\n    part w : Defs::Wheel;\n}\n",
    );

    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: Range::default(),
            context: CodeActionContext {
                diagnostics: vec![],
                only: Some(vec![CodeActionKind::SOURCE]),
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let minimize = actions
        .iter()
        .find_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) if c.title == "Minimize qualified names" => Some(c),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no minimize action: {actions:?}"));
    let edit = &minimize.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u][0];
    assert!(
        edit.new_text.contains("part w : Wheel;"),
        "qualified spelling should shrink: {}",
        edit.new_text
    );
    client.shutdown();
}

fn source_actions(
    client: &mut Client,
    u: &Uri,
    kind: CodeActionKind,
) -> Vec<lsp_types::CodeAction> {
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: Range::default(),
            context: CodeActionContext {
                diagnostics: vec![],
                only: Some(vec![kind]),
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    actions
        .unwrap_or_default()
        .into_iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) => Some(c),
            _ => None,
        })
        .collect()
}

/// Apply whole-line text edits to a source string (edits are
/// non-overlapping; applied back-to-front).
fn apply_edits(text: &str, edits: &[lsp_types::TextEdit]) -> String {
    let index = |p: lsp_types::Position| -> usize {
        let mut off = 0;
        for (i, l) in text.split_inclusive('\n').enumerate() {
            if i as u32 == p.line {
                return off + p.character as usize;
            }
            off += l.len();
        }
        text.len()
    };
    let mut sorted: Vec<&lsp_types::TextEdit> = edits.iter().collect();
    sorted.sort_by_key(|e| std::cmp::Reverse((e.range.start.line, e.range.start.character)));
    let mut out = text.to_string();
    for e in sorted {
        out.replace_range(index(e.range.start)..index(e.range.end), &e.new_text);
    }
    out
}

/// Beside a finding's own quick fix: the rule's every finding at once,
/// in this document and — where other documents hold more — across the
/// workspace, each labeled for the rewrite it is and offered once per
/// rule however many of its findings the request carries.
#[test]
fn rule_wide_fix_all_rides_the_quick_fix() {
    let mut client = Client::start(None);
    let a = uri("kinds-a.sysml");
    let b = uri("kinds-b.sysml");
    client.open(
        &a,
        "package A {\n    port def Pd;\n    part def X { attribute p : Pd; attribute q : Pd; }\n}\n",
    );
    client.open(
        &b,
        "package B {\n    part def Y { attribute r : A::Pd; }\n}\n",
    );
    let kind = |d: &lsp_types::Diagnostic| {
        d.code
            == Some(lsp_types::NumberOrString::String(
                "usage-kind-mismatch".into(),
            ))
    };
    let p = client.await_publish(&a, |p| {
        p.diagnostics.iter().filter(|d| kind(d)).count() >= 2
    });
    let lint: Vec<_> = p.diagnostics.iter().filter(|d| kind(d)).cloned().collect();
    let request = |client: &mut Client,
                   diags: Vec<lsp_types::Diagnostic>|
     -> Vec<lsp_types::CodeAction> {
        client
            .request_ok::<CodeActionRequest>(CodeActionParams {
                text_document: TextDocumentIdentifier { uri: a.clone() },
                range: diags[0].range,
                context: CodeActionContext {
                    diagnostics: diags,
                    only: None,
                    trigger_kind: None,
                },
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            })
            .unwrap_or_default()
            .into_iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(c) if c.kind == Some(CodeActionKind::QUICKFIX) => {
                    Some(c)
                }
                _ => None,
            })
            .collect()
    };
    let actions = request(&mut client, vec![lint[0].clone()]);
    let titles: Vec<&str> = actions.iter().map(|c| c.title.as_str()).collect();
    assert_eq!(
        titles,
        [
            "change `attribute` to `port` (rewrites the declaration)",
            "Fix all 2 `usage-kind-mismatch` findings in this file (rewrites the declarations)",
            "Fix all 3 `usage-kind-mismatch` findings across 2 files (rewrites the declarations)",
        ]
    );
    let changes = |c: &lsp_types::CodeAction| c.edit.clone().unwrap().changes.unwrap();
    let in_file = changes(&actions[1]);
    assert_eq!(in_file.len(), 1);
    assert_eq!(
        apply_edits(
            "package A {\n    port def Pd;\n    part def X { attribute p : Pd; attribute q : Pd; }\n}\n",
            &in_file[&a]
        ),
        "package A {\n    port def Pd;\n    part def X { port p : Pd; port q : Pd; }\n}\n"
    );
    let everywhere = changes(&actions[2]);
    assert_eq!(everywhere.len(), 2);
    assert_eq!(everywhere[&a], in_file[&a]);
    assert_eq!(
        apply_edits(
            "package B {\n    part def Y { attribute r : A::Pd; }\n}\n",
            &everywhere[&b]
        ),
        "package B {\n    part def Y { port r : A::Pd; }\n}\n"
    );
    // Both of this document's findings in the request: two single fixes,
    // the rule-wide pair once.
    let actions = request(&mut client, lint);
    let wide = actions
        .iter()
        .filter(|c| c.title.starts_with("Fix all"))
        .count();
    assert_eq!((actions.len(), wide), (4, 2), "{actions:#?}");
    client.shutdown();
}

/// "Optimize imports" removes exactly the unused imports, keeps the
/// used ones in their original order, and leaves no blank lines.
#[test]
fn optimize_imports_removes_unused_only_preserving_order() {
    let mut client = Client::start(None);
    let defs = uri("defs.sysml");
    let u = uri("o.sysml");
    client.open(
        &defs,
        "package Defs { part def Wheel; part def Axle; part def Cog; }\n",
    );
    let text = "package O {\n    private import Defs::Wheel;\n    private import Defs::Cog;\n    private import Defs::Axle;\n    part w : Wheel;\n    part a : Axle;\n}\n";
    client.open(&u, text);

    let actions = source_actions(
        &mut client,
        &u,
        CodeActionKind::new("source.organizeImports"),
    );
    let optimize = actions
        .iter()
        .find(|c| c.title == "Optimize imports")
        .unwrap_or_else(|| panic!("no optimize action: {actions:?}"));
    assert_eq!(
        optimize.kind,
        Some(CodeActionKind::new("source.organizeImports"))
    );
    let edits = &optimize.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u];
    let after = apply_edits(text, edits);
    assert_eq!(
        after,
        "package O {\n    private import Defs::Wheel;\n    private import Defs::Axle;\n    part w : Wheel;\n    part a : Axle;\n}\n",
        "only the unused Cog import goes, order preserved"
    );
    client.shutdown();
}

/// Unresolved-reference quick fixes: a missing enum literal offers an
/// insertion into the enum's body; a near-miss spelling offers a
/// "Did you mean" replacement.
#[test]
fn unresolved_reference_offers_enum_member_and_respelling() {
    let mut client = Client::start(None);
    let u = uri("e.sysml");
    let text = "package P {\n    enum def Phase {\n        init;\n        ready;\n    }\n    attribute c : Phase = Phase::halt;\n}\n";
    client.open(&u, text);

    let diag_at = |message: &str, line: u32, character: u32| lsp_types::Diagnostic {
        range: Range {
            start: lsp_types::Position { line, character },
            end: lsp_types::Position {
                line,
                character: character + 1,
            },
        },
        message: message.to_string(),
        ..Default::default()
    };

    // `Phase::halt` starts at line 5, character 26.
    let d = diag_at("unresolved reference `Phase::halt`", 5, 26);
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: d.range,
            context: CodeActionContext {
                diagnostics: vec![d],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let add = actions
        .iter()
        .find_map(|a| match a {
            CodeActionOrCommand::CodeAction(c)
                if c.title == "Add enum member `halt` to `Phase`" =>
            {
                Some(c)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("no add-member action: {actions:?}"));
    let edit = &add.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u][0];
    assert_eq!(edit.new_text, "        halt;\n");
    assert_eq!(edit.range.start.line, 4, "inserted above the closing brace");

    // A typo of an existing literal suggests the respelling first.
    let d = diag_at("unresolved reference `Phase::inut`", 5, 26);
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: d.range,
            context: CodeActionContext {
                diagnostics: vec![d],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    // The document still spells `halt`, so re-derive against a doc that
    // spells `inut`.
    let _ = actions;
    let text2 = text.replace("Phase::halt", "Phase::inut");
    client.change(&u, 2, &text2);
    let d = diag_at("unresolved reference `Phase::inut`", 5, 26);
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: d.range,
            context: CodeActionContext {
                diagnostics: vec![d],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let mean = actions
        .iter()
        .find_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) if c.title == "Did you mean `init`?" => Some(c),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no did-you-mean action: {actions:?}"));
    assert_eq!(mean.is_preferred, Some(true));
    let edit = &mean.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u][0];
    assert_eq!(edit.new_text, "init");
    assert_eq!(
        edit.range.start.character, 33,
        "replaces only the last segment"
    );
    client.shutdown();
}

/// The usage spelling (`enum Phase { … }`, an EnumerationUsage whose
/// members are bare ReferenceUsages) gets the same add-member fix as
/// `enum def`.
#[test]
fn unresolved_reference_offers_member_for_enum_usage() {
    let mut client = Client::start(None);
    let u = uri("eu.sysml");
    let text = "package P {\n    enum Phase {\n        init;\n        ready;\n    }\n    attribute c : Phase = Phase::halt;\n}\n";
    client.open(&u, text);

    let d = lsp_types::Diagnostic {
        range: Range {
            start: lsp_types::Position {
                line: 5,
                character: 26,
            },
            end: lsp_types::Position {
                line: 5,
                character: 27,
            },
        },
        message: "unresolved reference `Phase::halt`".to_string(),
        ..Default::default()
    };
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range: d.range,
            context: CodeActionContext {
                diagnostics: vec![d],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions = actions.unwrap();
    let add = actions
        .iter()
        .find_map(|a| match a {
            CodeActionOrCommand::CodeAction(c)
                if c.title == "Add enum member `halt` to `Phase`" =>
            {
                Some(c)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("no add-member action for enum usage: {actions:?}"));
    let edit = &add.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u][0];
    assert_eq!(edit.new_text, "        halt;\n");
    assert_eq!(edit.range.start.line, 4, "inserted above the closing brace");
    client.shutdown();
}

/// "Sort imports" alphabetizes a contiguous import run; statements
/// carry their own visibility and wildcard suffixes with them.
#[test]
fn sort_imports_alphabetizes_contiguous_runs() {
    let mut client = Client::start(None);
    let u = uri("s.sysml");
    let text = "package S {\n    private import Zoo::*;\n    private import Alpha::Beta;\n    private import Mid::Thing;\n    part def P;\n}\n";
    client.open(&u, text);

    let actions = source_actions(&mut client, &u, CodeActionKind::new("source.sortImports"));
    let sort = actions
        .iter()
        .find(|c| c.title == "Sort imports")
        .unwrap_or_else(|| panic!("no sort action: {actions:?}"));
    let edits = &sort.edit.as_ref().unwrap().changes.as_ref().unwrap()[&u];
    let after = apply_edits(text, edits);
    assert_eq!(
        after,
        "package S {\n    private import Alpha::Beta;\n    private import Mid::Thing;\n    private import Zoo::*;\n    part def P;\n}\n"
    );

    // Already sorted → the action is not offered at all.
    let sorted_u = uri("s2.sysml");
    client.open(
        &sorted_u,
        "package T {\n    private import Alpha::A;\n    private import Beta::B;\n}\n",
    );
    let actions = source_actions(
        &mut client,
        &sorted_u,
        CodeActionKind::new("source.sortImports"),
    );
    assert!(
        actions.iter().all(|c| c.title != "Sort imports"),
        "{actions:?}"
    );
    client.shutdown();
}

#[test]
fn lint_fixes_ride_quick_fixes_and_fix_all() {
    // Two lint findings with fixes: a bare import (safe fix: declare
    // `private`) and an attribute typed by a port definition (semantic
    // fix: rewrite the keyword). Quick fixes offer both, labeled; fix-all
    // applies only the safe one.
    let mut client = Client::start(None);
    let m = uri("fixes.sysml");
    client.open(
        &m,
        "package P {\n    import Lib::*;\n    port def Pd;\n    part def A { attribute p : Pd; }\n}\npackage Lib { part def Thing; }\n",
    );
    let p = client.await_publish(&m, |p| {
        p.diagnostics
            .iter()
            .filter(|d| d.source.as_deref() == Some("sysmlv2 lint"))
            .count()
            >= 2
    });
    let lint: Vec<_> = p
        .diagnostics
        .iter()
        .filter(|d| d.source.as_deref() == Some("sysmlv2 lint"))
        .cloned()
        .collect();
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: m.clone() },
            range: lint[0].range,
            context: CodeActionContext {
                diagnostics: lint.clone(),
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let titles: Vec<String> = actions
        .unwrap_or_default()
        .into_iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) if c.kind == Some(CodeActionKind::QUICKFIX) => {
                Some(c.title)
            }
            _ => None,
        })
        .collect();
    assert!(
        titles.iter().any(|t| t == "Make the import `private`"),
        "{titles:?}"
    );
    assert!(
        titles
            .iter()
            .any(|t| t == "change `attribute` to `port` (rewrites the declaration)"),
        "{titles:?}"
    );
    // With the syntax tier's own visibility diagnostic in the request,
    // its quick fix stands and the lint twin steps aside.
    let import_diag = lint
        .iter()
        .find(|d| {
            d.code
                == Some(lsp_types::NumberOrString::String(
                    "import-visibility".into(),
                ))
        })
        .expect("the bare import's lint finding");
    let syntax = lsp_types::Diagnostic {
        range: import_diag.range,
        severity: Some(DiagnosticSeverity::ERROR),
        source: Some("sysmlv2".to_string()),
        message:
            "an import must declare an explicit visibility (`public`, `private`, or `protected`)"
                .to_string(),
        ..Default::default()
    };
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: m.clone() },
            range: import_diag.range,
            context: CodeActionContext {
                diagnostics: vec![syntax, import_diag.clone()],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let titles: Vec<String> = actions
        .unwrap_or_default()
        .into_iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) => Some(c.title),
            _ => None,
        })
        .collect();
    assert!(
        titles
            .iter()
            .any(|t| t.starts_with("Make the import `private`")),
        "{titles:?}"
    );
    assert!(
        !titles.iter().any(|t| t == "Make the import `private`"),
        "{titles:?}"
    );
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: m.clone() },
            range: Range::default(),
            context: CodeActionContext {
                diagnostics: Vec::new(),
                only: Some(vec![CodeActionKind::SOURCE_FIX_ALL]),
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let fix_all = actions
        .unwrap_or_default()
        .into_iter()
        .find_map(|a| match a {
            CodeActionOrCommand::CodeAction(c)
                if c.kind == Some(CodeActionKind::SOURCE_FIX_ALL) =>
            {
                Some(c)
            }
            _ => None,
        })
        .expect("a fix-all action");
    assert_eq!(fix_all.title, "Fix all auto-fixable lint findings (1)");
    let edits = &fix_all.edit.unwrap().changes.unwrap()[&m];
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].new_text, "private ");
    client.shutdown();
}

#[test]
fn split_action_creates_annotated_files_from_a_package_declaration() {
    let mut client = Client::start(None);
    let r = uri("r.sysml");
    client.open(
        &r,
        "package Lib { part def Thing; }\npackage R {\n    private import Lib::*;\n    package A { part def X; part t : Thing; }\n    package B { part def Y :> A::X; }\n    part r : A::X;\n}\n",
    );
    // The cursor on `R` in `package R {` (line 1, character 8).
    let at = lsp_types::Position {
        line: 1,
        character: 8,
    };
    let actions: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: r.clone() },
            range: Range { start: at, end: at },
            context: CodeActionContext {
                diagnostics: Vec::new(),
                only: Some(vec![CodeActionKind::new("refactor.move")]),
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let actions: Vec<lsp_types::CodeAction> = actions
        .unwrap_or_default()
        .into_iter()
        .filter_map(|a| match a {
            CodeActionOrCommand::CodeAction(c) => Some(c),
            _ => None,
        })
        .collect();
    assert_eq!(actions.len(), 1, "{actions:?}");
    assert_eq!(actions[0].title, "Split 'R' into 2 files under r/");
    let edit = actions[0].edit.clone().expect("workspace edit");
    let Some(lsp_types::DocumentChanges::Operations(ops)) = edit.document_changes else {
        panic!("expected document operations: {edit:?}");
    };
    let creates: Vec<String> = ops
        .iter()
        .filter_map(|op| match op {
            lsp_types::DocumentChangeOperation::Op(lsp_types::ResourceOp::Create(c)) => {
                Some(c.uri.to_string())
            }
            _ => None,
        })
        .collect();
    assert_eq!(creates, ["file:///w/r/A.sysml", "file:///w/r/B.sysml"]);
    let edits: Vec<(String, String)> = ops
        .iter()
        .filter_map(|op| match op {
            lsp_types::DocumentChangeOperation::Edit(e) => Some((
                e.text_document.uri.to_string(),
                e.edits
                    .iter()
                    .map(|x| match x {
                        lsp_types::OneOf::Left(t) => t.new_text.clone(),
                        lsp_types::OneOf::Right(a) => a.text_edit.new_text.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join("|"),
            )),
            _ => None,
        })
        .collect();
    assert_eq!(edits.len(), 3, "{edits:?}");
    assert!(edits[0].1.starts_with("package A {"), "{:?}", edits[0]);
    assert!(
        edits[0].1.contains("part t : Lib::Thing;"),
        "{:?}",
        edits[0]
    );
    assert!(edits[1].1.starts_with("package B {"), "{:?}", edits[1]);
    assert_eq!(edits[2].0, "file:///w/r.sysml");
    assert!(edits[2].1.contains("public import A;"), "{:?}", edits[2]);
    // Annotated for a client's preview, not flagged for confirmation:
    // editors read that flag as opt-in per change and would open the
    // preview with every change unticked.
    let annotations = edit.change_annotations.expect("annotated");
    assert_eq!(annotations["split"].needs_confirmation, None);
    assert_eq!(annotations["split"].label, "Split into 2 new file(s)");
    // A package with nothing nested offers no action.
    let at = lsp_types::Position {
        line: 0,
        character: 8,
    };
    let none: Option<Vec<CodeActionOrCommand>> =
        client.request_ok::<CodeActionRequest>(CodeActionParams {
            text_document: TextDocumentIdentifier { uri: r },
            range: Range { start: at, end: at },
            context: CodeActionContext {
                diagnostics: Vec::new(),
                only: Some(vec![CodeActionKind::new("refactor.move")]),
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    assert!(none.unwrap_or_default().is_empty());
    client.shutdown();
}

#[test]
fn split_requests_plan_and_edit_a_package_by_position_or_name() {
    let mut client = Client::start(None);
    let r = uri("r.sysml");
    let text = "package Lib { part def Thing; }\npackage B { part def Elsewhere; }\npackage R {\n    private import Lib::*;\n    package A { part def X; part t : Thing; package Deep { part def D; } }\n    package B { part def Y :> A::X; }\n    package '02 JPL' { part def Z; }\n    part r : A::X;\n}\n";
    client.open(&r, text);
    // The plan alone, from the cursor on `R`: one unit per nested
    // package, file segments spelled as the editor spells a created
    // file's uri, a root-level collision renamed, no edit computed.
    let plan = client
        .request_raw(
            sysmlv2_lsp::SPLIT_PLAN_METHOD,
            serde_json::json!({
                "textDocument": { "uri": r.as_str() },
                "position": { "line": 2, "character": 8 },
            }),
        )
        .expect("a plan");
    assert_eq!(plan["root"]["qualifiedName"], "R");
    assert_eq!(plan["root"]["uri"], r.as_str());
    assert_eq!(plan["directory"], "file:///w/r");
    assert!(plan.get("edit").is_none(), "{plan}");
    let entries = plan["entries"].as_array().expect("entries");
    let uris: Vec<&str> = entries.iter().map(|e| e["uri"].as_str().unwrap()).collect();
    assert_eq!(
        uris,
        [
            "file:///w/r/A.sysml",
            "file:///w/r/R%20B.sysml",
            "file:///w/r/02%20JPL.sysml"
        ]
    );
    let nested: Vec<u64> = entries
        .iter()
        .map(|e| e["nested"].as_u64().unwrap())
        .collect();
    assert_eq!(nested, [1, 0, 0]);
    assert_eq!(entries[1]["name"], "B");
    assert_eq!(entries[1]["newName"], "R B");
    assert_eq!(entries[1]["rootName"], "'R B'");
    assert_eq!(entries[2]["qualifiedName"], "R::'02 JPL'");
    assert_eq!(entries[2]["rootName"], "'02 JPL'");
    assert!(entries[2]["newName"].is_null());
    assert!(entries[0]["bytes"].as_u64().unwrap() > entries[2]["bytes"].as_u64().unwrap());
    // The edit, by package name without a document, under a chosen
    // directory and slugged names.
    let split = client
        .request_raw(
            sysmlv2_lsp::SPLIT_METHOD,
            serde_json::json!({ "package": "R", "naming": "slug", "directory": "file:///w/out" }),
        )
        .expect("a split");
    assert_eq!(split["directory"], "file:///w/out");
    let (creates, _) = split_ops(&split["edit"]);
    assert_eq!(
        creates,
        [
            "file:///w/out/A.sysml",
            "file:///w/out/R-B.sysml",
            "file:///w/out/02-JPL.sysml"
        ]
    );
    // The edit with the names kept: percent-encoded uris spell, the
    // root re-exports each moved package (an alias for the renamed
    // one), and the created texts stand alone.
    let split = client
        .request_raw(
            sysmlv2_lsp::SPLIT_METHOD,
            serde_json::json!({ "textDocument": { "uri": r.as_str() }, "position": { "line": 2, "character": 8 } }),
        )
        .expect("a split");
    let edit: lsp_types::WorkspaceEdit = serde_json::from_value(split["edit"].clone()).unwrap();
    assert_eq!(
        edit.change_annotations.as_ref().expect("annotated")["split"].needs_confirmation,
        None
    );
    let (creates, texts) = split_ops(&split["edit"]);
    assert_eq!(creates, uris);
    let root_text = apply_edits(text, &texts[r.as_str()]);
    assert!(root_text.contains("public import A;"), "{root_text}");
    assert!(
        root_text.contains("public alias B for 'R B';"),
        "{root_text}"
    );
    assert!(root_text.contains("public import '02 JPL';"), "{root_text}");
    assert!(!root_text.contains("package A"), "{root_text}");
    let a_text = apply_edits("", &texts["file:///w/r/A.sysml"]);
    assert!(a_text.starts_with("package A {"), "{a_text}");
    assert!(a_text.contains("part t : Lib::Thing;"), "{a_text}");
    let b_text = apply_edits("", &texts["file:///w/r/R%20B.sysml"]);
    assert!(b_text.starts_with("package 'R B' {"), "{b_text}");
    assert!(b_text.contains("part def Y :> R::A::X;"), "{b_text}");
    // A deeper level: with the level applied (the root changed, the
    // new units open), the hoisted packages are reachable by the names
    // they took — the renamed one by its quoted name (a leaf, refused
    // as such), `A` with its nested package under its own directory.
    client.notify::<DidChangeTextDocument>(DidChangeTextDocumentParams {
        text_document: lsp_types::VersionedTextDocumentIdentifier {
            uri: r.clone(),
            version: 2,
        },
        content_changes: vec![lsp_types::TextDocumentContentChangeEvent {
            range: None,
            range_length: None,
            text: root_text,
        }],
    });
    client.open(&Uri::from_str("file:///w/r/A.sysml").unwrap(), &a_text);
    client.open(&Uri::from_str("file:///w/r/R%20B.sysml").unwrap(), &b_text);
    let err = client
        .request_raw(
            sysmlv2_lsp::SPLIT_PLAN_METHOD,
            serde_json::json!({ "package": "'R B'" }),
        )
        .expect_err("a leaf");
    assert_eq!(err.code, lsp_server::ErrorCode::RequestFailed as i32);
    assert!(
        err.message.contains("owns no nested package"),
        "{}",
        err.message
    );
    // A name takes precedence over a document and position beside it
    // (the wizard's deeper-level shape).
    let deeper = client
        .request_raw(
            sysmlv2_lsp::SPLIT_PLAN_METHOD,
            serde_json::json!({ "textDocument": { "uri": r.as_str() }, "position": { "line": 0, "character": 8 }, "package": "A" }),
        )
        .expect("a deeper plan");
    assert_eq!(deeper["root"]["uri"], "file:///w/r/A.sysml");
    assert_eq!(deeper["directory"], "file:///w/r/A");
    assert_eq!(deeper["entries"][0]["uri"], "file:///w/r/A/Deep.sysml");
    // Refusals carry their reason: not a package; a position in a
    // document that is not open; neither a package nor a position.
    let err = client
        .request_raw(
            sysmlv2_lsp::SPLIT_METHOD,
            serde_json::json!({ "package": "Lib::Thing" }),
        )
        .expect_err("not a package");
    assert_eq!(err.code, lsp_server::ErrorCode::RequestFailed as i32);
    assert!(err.message.contains("is not a package"), "{}", err.message);
    let err = client
        .request_raw(
            sysmlv2_lsp::SPLIT_PLAN_METHOD,
            serde_json::json!({ "textDocument": { "uri": "file:///w/closed.sysml" }, "position": { "line": 0, "character": 0 } }),
        )
        .expect_err("not open");
    assert_eq!(err.code, lsp_server::ErrorCode::InvalidParams as i32);
    let err = client
        .request_raw(sysmlv2_lsp::SPLIT_METHOD, serde_json::json!({}))
        .expect_err("no target");
    assert_eq!(err.code, lsp_server::ErrorCode::InvalidParams as i32);
    client.shutdown();
}

/// A split edit's created uris and, per document, its text edits.
fn split_ops(
    edit: &serde_json::Value,
) -> (
    Vec<String>,
    std::collections::HashMap<String, Vec<lsp_types::TextEdit>>,
) {
    let edit: lsp_types::WorkspaceEdit = serde_json::from_value(edit.clone()).unwrap();
    let Some(lsp_types::DocumentChanges::Operations(ops)) = edit.document_changes else {
        panic!("expected document operations");
    };
    let mut creates = Vec::new();
    let mut texts = std::collections::HashMap::new();
    for op in ops {
        match op {
            lsp_types::DocumentChangeOperation::Op(lsp_types::ResourceOp::Create(c)) => {
                creates.push(c.uri.to_string());
            }
            lsp_types::DocumentChangeOperation::Edit(e) => {
                let edits = e
                    .edits
                    .into_iter()
                    .map(|x| match x {
                        lsp_types::OneOf::Left(t) => t,
                        lsp_types::OneOf::Right(a) => a.text_edit,
                    })
                    .collect();
                texts.insert(e.text_document.uri.to_string(), edits);
            }
            _ => {}
        }
    }
    (creates, texts)
}

/// The workspace's lint configuration drives formatting style as well
/// as the lint, and both are asked for it on every keystroke-driven
/// request. It is read from disk once and re-read when the file
/// changes — a stale answer here would leave the editor formatting to
/// a policy the project no longer has.
#[test]
fn formatting_follows_the_lint_configuration_as_it_changes() {
    use lsp_types::request::Formatting;
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-lsp-config-cache-test-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let config = dir.join("sysmlint.json");
    // `min: 0` keeps a logical chain on one line.
    std::fs::write(
        &config,
        r#"{ "rules": { "multiline-conditions": { "min": 0 } } }"#,
    )
    .unwrap();

    let mut client = Client::start(Some(&dir));
    let m = uri("m.sysml");
    client.open(
        &m,
        "package P {\n    constraint def C {\n        a and b and c and d\n    }\n}\n",
    );
    let format = |client: &mut Client| -> Vec<lsp_types::TextEdit> {
        client
            .request_ok::<Formatting>(lsp_types::DocumentFormattingParams {
                text_document: TextDocumentIdentifier {
                    uri: uri("m.sysml"),
                },
                options: Default::default(),
                work_done_progress_params: Default::default(),
            })
            .unwrap_or_default()
    };
    assert_eq!(format(&mut client), Vec::new(), "the chain stays inline");

    // A project that wants chains of two or more broken out. The new
    // text is a different length, so the change is visible however
    // coarse the clock is.
    std::fs::write(
        &config,
        r#"{ "rules": { "multiline-conditions": { "min": 2, "severity": "warn" } } }"#,
    )
    .unwrap();
    let edits = format(&mut client);
    assert_eq!(edits.len(), 1, "{edits:?}");
    assert!(
        edits[0].new_text.contains("and b\n"),
        "one operand per line: {:?}",
        edits[0].new_text
    );
    client.shutdown();
}
