#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Refactoring harness: `refactor.extract` / `refactor.inline` code actions —
//! through the wire. Extract offered on an eligible usage's
//! declaration, Inline on the definition or a typing reference to it,
//! titles carrying the name, cross-file WorkspaceEdits, and the
//! code-action ancestor kind-filter semantics.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{CodeActionRequest, Initialize, Shutdown};
use lsp_types::{
    CodeAction, CodeActionContext, CodeActionKind, CodeActionOrCommand, CodeActionParams,
    DidOpenTextDocumentParams, InitializeParams, PartialResultParams, Position, Range,
    TextDocumentIdentifier, TextDocumentItem, Uri, WorkDoneProgressParams, WorkspaceEdit,
};
use std::str::FromStr;
use std::thread::JoinHandle;

struct Client {
    conn: Connection,
    server: Option<JoinHandle<Result<(), Box<dyn std::error::Error + Send + Sync>>>>,
    next_id: i32,
}

fn uri(name: &str) -> Uri {
    Uri::from_str(&format!("file:///w/{name}")).unwrap()
}

impl Client {
    fn start() -> Client {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || sysmlv2_lsp::run(server_side));
        let mut c = Client {
            conn: client_side,
            server: Some(server),
            next_id: 0,
        };
        let _: lsp_types::InitializeResult =
            c.request_ok::<Initialize>(InitializeParams::default());
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
        loop {
            if let Message::Notification(n) = self.conn.receiver.recv().unwrap() {
                if n.method == "textDocument/publishDiagnostics" {
                    return;
                }
            }
        }
    }

    fn actions(&mut self, uri: &Uri, at: Position, only: Option<Vec<&str>>) -> Vec<CodeAction> {
        let resp: Option<Vec<CodeActionOrCommand>> =
            self.request_ok::<CodeActionRequest>(CodeActionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                range: Range { start: at, end: at },
                context: CodeActionContext {
                    diagnostics: Vec::new(),
                    only: only.map(|ks| {
                        ks.into_iter()
                            .map(|k| CodeActionKind::from(k.to_string()))
                            .collect()
                    }),
                    trigger_kind: None,
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                partial_result_params: PartialResultParams::default(),
            });
        resp.unwrap_or_default()
            .into_iter()
            .filter_map(|a| match a {
                CodeActionOrCommand::CodeAction(a) => Some(a),
                CodeActionOrCommand::Command(_) => None,
            })
            .collect()
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

/// Position of `needle`'s first byte (ASCII texts only).
fn pos(text: &str, needle: &str) -> Position {
    let at = text.find(needle).expect("needle present");
    let before = &text[..at];
    let line = before.matches('\n').count() as u32;
    let character = (at - before.rfind('\n').map_or(0, |i| i + 1)) as u32;
    Position { line, character }
}

/// Apply one document's ranged edits (non-overlapping) to `text`.
fn apply(text: &str, edits: &[lsp_types::TextEdit]) -> String {
    let offset = |p: Position| -> usize {
        let line_start = text
            .split_inclusive('\n')
            .take(p.line as usize)
            .map(str::len)
            .sum::<usize>();
        line_start + p.character as usize
    };
    let mut spans: Vec<(usize, usize, &str)> = edits
        .iter()
        .map(|e| {
            (
                offset(e.range.start),
                offset(e.range.end),
                e.new_text.as_str(),
            )
        })
        .collect();
    spans.sort_by_key(|&(s, _, _)| std::cmp::Reverse(s));
    let mut out = text.to_string();
    for (s, e, t) in spans {
        out.replace_range(s..e, t);
    }
    out
}

fn changes_for<'a>(edit: &'a WorkspaceEdit, uri: &Uri) -> &'a Vec<lsp_types::TextEdit> {
    edit.changes
        .as_ref()
        .expect("changes-style edit")
        .get(uri)
        .expect("edits for the uri")
}

const RIG: &str = "package P {
    part def A;
    part engine : A {
        attribute mass = 100;
    }
}
";

#[test]
fn extract_action_offers_the_synthesized_name_and_round_trips() {
    let mut client = Client::start();
    let m = uri("m.sysml");
    client.open(&m, RIG);

    let actions = client.actions(&m, pos(RIG, "engine"), None);
    let extract = actions
        .iter()
        .find(|a| a.kind == Some(CodeActionKind::REFACTOR_EXTRACT))
        .expect("extract offered on an eligible usage");
    assert_eq!(extract.title, "Extract 'part def Engine'");

    let edit = extract.edit.as_ref().expect("carries the edit");
    let out = apply(RIG, changes_for(edit, &m));
    assert_eq!(
        out,
        "package P {
    part def A;
    part def Engine :> A {
        attribute mass = 100;
    }
    part engine : Engine;
}
"
    );
    client.shutdown();
}

#[test]
fn refactor_titles_use_the_engine_name_spelling() {
    let src = "package P {
    part 'a::b' { attribute x; }
    part def 'Tool::Special' { attribute t; }
    part tool : 'Tool::Special';
}
";
    let mut client = Client::start();
    let m = uri("m.sysml");
    client.open(&m, src);

    let extract = client
        .actions(&m, pos(src, "'a::b'"), Some(vec!["refactor.extract"]))
        .into_iter()
        .find(|a| a.kind == Some(CodeActionKind::REFACTOR_EXTRACT))
        .expect("extract offered");
    assert_eq!(extract.title, "Extract 'part def 'A::b''");

    let inline = client
        .actions(
            &m,
            pos(src, "'Tool::Special' {"),
            Some(vec!["refactor.inline"]),
        )
        .into_iter()
        .find(|a| a.kind == Some(CodeActionKind::REFACTOR_INLINE))
        .expect("inline offered");
    assert_eq!(inline.title, "Inline 'part def 'Tool::Special''");
    client.shutdown();
}

#[test]
fn kind_filters_use_ancestor_semantics() {
    let mut client = Client::start();
    let m = uri("m.sysml");
    client.open(&m, RIG);
    let at = pos(RIG, "engine");

    // `refactor` requests both members of the pair (ancestor match).
    let refactor = client.actions(&m, at, Some(vec!["refactor"]));
    assert!(
        refactor
            .iter()
            .any(|a| a.kind == Some(CodeActionKind::REFACTOR_EXTRACT)),
        "{refactor:?}"
    );
    // The exact kind requests it too.
    let exact = client.actions(&m, at, Some(vec!["refactor.extract"]));
    assert!(
        exact
            .iter()
            .any(|a| a.kind == Some(CodeActionKind::REFACTOR_EXTRACT)),
        "{exact:?}"
    );
    // A quickfix-only request must not surface refactorings, and a
    // refactor.inline request must not surface Extract.
    for only in [vec!["quickfix"], vec!["refactor.inline"]] {
        let filtered = client.actions(&m, at, Some(only.clone()));
        assert!(
            filtered
                .iter()
                .all(|a| a.kind != Some(CodeActionKind::REFACTOR_EXTRACT)),
            "{only:?}: {filtered:?}"
        );
    }
    client.shutdown();
}

#[test]
fn inline_action_is_offered_on_the_definition_and_crosses_files() {
    let defs_text = "package Defs {
    part def Kit;
    part def Tool {
        attribute t;
    }
}
";
    let use_text = "package Use {
    private import Defs::*;
    part tool : Tool;
}
";
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let usef = uri("use.sysml");
    client.open(&defs, defs_text);
    client.open(&usef, use_text);

    // Offered with the cursor on the definition's declaration…
    let on_def = client.actions(&defs, pos(defs_text, "Tool {"), None);
    let inline = on_def
        .iter()
        .find(|a| a.kind == Some(CodeActionKind::REFACTOR_INLINE))
        .expect("inline offered on the definition");
    assert_eq!(inline.title, "Inline 'part def Tool'");

    // …and the WorkspaceEdit crosses files: the definition's unit loses
    // it, the usage's unit gains the body.
    let edit = inline.edit.as_ref().expect("carries the edit");
    let new_defs = apply(defs_text, changes_for(edit, &defs));
    let new_use = apply(use_text, changes_for(edit, &usef));
    assert_eq!(new_defs, "package Defs {\n    part def Kit;\n}\n");
    assert_eq!(
        new_use,
        "package Use {
    private import Defs::*;
    part tool {
        attribute t;
    }
}
"
    );
    client.shutdown();
}

#[test]
fn inline_action_is_offered_on_a_typing_reference() {
    let defs_text = "package Defs {
    part def Kit;
    part def Tool {
        attribute t;
    }
}
";
    let use_text = "package Use {
    private import Defs::*;
    part tool : Tool;
}
";
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let usef = uri("use.sysml");
    client.open(&defs, defs_text);
    client.open(&usef, use_text);

    let on_ref = client.actions(&usef, pos(use_text, "Tool;"), None);
    assert!(
        on_ref
            .iter()
            .any(|a| a.kind == Some(CodeActionKind::REFACTOR_INLINE)),
        "{on_ref:?}"
    );
    client.shutdown();
}

#[test]
fn ineligible_cursors_offer_no_refactorings() {
    let src = "package P {
    part def A;
    part bare;
    action act { attribute x; }
}
";
    let mut client = Client::start();
    let m = uri("m.sysml");
    client.open(&m, src);

    // A bodyless usage, a gated kind, and a package name: nothing.
    for needle in ["bare", "act {", "P {"] {
        let actions = client.actions(&m, pos(src, needle), None);
        assert!(
            actions.iter().all(|a| {
                a.kind != Some(CodeActionKind::REFACTOR_EXTRACT)
                    && a.kind != Some(CodeActionKind::REFACTOR_INLINE)
            }),
            "`{needle}`: {actions:?}"
        );
    }
    client.shutdown();
}
