#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Workspace-tier harness: the debounced worker's
//! publishes and the code actions riding them, through the wire with a
//! short debounce.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{CodeActionRequest, Initialize, Shutdown};
use lsp_types::{
    CodeActionContext, CodeActionKind, CodeActionOrCommand, CodeActionParams, DiagnosticTag,
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, InitializeParams,
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

impl Client {
    fn start(root: Option<&std::path::Path>) -> Client {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || {
            sysmlv2_lsp::run_with_options(server_side, None, Duration::from_millis(50))
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
                    result,
                    error,
                }) if rid == id => {
                    assert!(error.is_none(), "{error:?}");
                    return serde_json::from_value(result.unwrap_or_default()).unwrap();
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
    let dir = std::env::temp_dir().join("sysmlv2-lsp-lint-test");
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
    let dir = std::env::temp_dir().join("sysmlv2-lsp-ws-test");
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
    assert_eq!(
        titles,
        [
            "Make the import private",
            "Make the import public",
            "Make the import protected"
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
