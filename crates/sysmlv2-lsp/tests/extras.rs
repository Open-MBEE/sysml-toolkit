#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Extras harness: completion, inlay hints (evaluated values + propagated
//! ranges), and verify code lenses — through the wire.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{CodeLensRequest, Completion, Initialize, InlayHintRequest, Shutdown};
use lsp_types::{
    CodeLensParams, CompletionItemKind, CompletionParams, CompletionResponse,
    DidOpenTextDocumentParams, InitializeParams, InlayHintLabel, InlayHintParams,
    PartialResultParams, Position, Range, TextDocumentIdentifier, TextDocumentItem,
    TextDocumentPositionParams, Uri, WorkDoneProgressParams,
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
        Self::start_with(InitializeParams::default())
    }

    fn start_with(init: InitializeParams) -> Client {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || sysmlv2_lsp::run(server_side));
        let mut c = Client {
            conn: client_side,
            server: Some(server),
            next_id: 0,
        };
        let _: lsp_types::InitializeResult = c.request_ok::<Initialize>(init);
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

#[test]
fn completion_offers_keywords_and_workspace_names() {
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let u = uri("u.sysml");
    client.open(&defs, "package Defs { part def Wheel; }\n");
    client.open(&u, "package U {\n    part w : \n}\n");

    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: u },
            position: Position {
                line: 1,
                character: 13,
            },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    let Some(CompletionResponse::Array(items)) = resp else {
        panic!("expected items: {resp:?}");
    };
    let part = items
        .iter()
        .find(|i| i.label == "part")
        .expect("keyword `part`");
    assert_eq!(part.kind, Some(CompletionItemKind::KEYWORD));
    let wheel = items
        .iter()
        .find(|i| i.label == "Wheel")
        .expect("cross-document name `Wheel`");
    assert_eq!(wheel.kind, Some(CompletionItemKind::CLASS));
    client.shutdown();
}

/// A workspace symbol from another package completes with the import
/// edit that makes the naked name resolve — and stays edit-free
/// once an admitting import exists.
#[test]
fn completion_auto_imports_cross_document_names() {
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let u = uri("u.sysml");
    client.open(&defs, "package Defs { part def Wheel; }\n");
    client.open(&u, "package U {\n    part w : \n}\n");

    let complete = |client: &mut Client| {
        let resp = client.request_ok::<Completion>(CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: u.clone() },
                position: Position {
                    line: 1,
                    character: 13,
                },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        });
        let Some(CompletionResponse::Array(items)) = resp else {
            panic!("expected items: {resp:?}");
        };
        items
    };

    let items = complete(&mut client);
    let wheel = items.iter().find(|i| i.label == "Wheel").expect("`Wheel`");
    let edits = wheel
        .additional_text_edits
        .as_ref()
        .expect("out-of-scope name carries the import edit");
    assert_eq!(edits.len(), 1);
    // No imports in `U` yet: the statement lands before the first
    // member, keeping its indentation.
    assert_eq!(
        edits[0].range.start,
        Position {
            line: 1,
            character: 4
        }
    );
    assert_eq!(edits[0].new_text, "private import Defs::Wheel;\n    ");
    assert_eq!(
        wheel
            .label_details
            .as_ref()
            .and_then(|d| d.description.as_deref()),
        Some("import Defs")
    );

    // With the import in place the name is visible — no edit.
    client.notify::<lsp_types::notification::DidChangeTextDocument>(
        lsp_types::DidChangeTextDocumentParams {
            text_document: lsp_types::VersionedTextDocumentIdentifier {
                uri: u.clone(),
                version: 2,
            },
            content_changes: vec![lsp_types::TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: "package U {\n    private import Defs::Wheel;\n    part w : \n}\n"
                    .to_string(),
            }],
        },
    );
    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            position: Position {
                line: 2,
                character: 13,
            },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    let Some(CompletionResponse::Array(items)) = resp else {
        panic!("expected items: {resp:?}");
    };
    let wheel = items.iter().find(|i| i.label == "Wheel").expect("`Wheel`");
    assert!(
        wheel.additional_text_edits.is_none(),
        "imported name needs no edit: {wheel:?}"
    );
    client.shutdown();
}

/// An unresolved reference to a cross-document workspace symbol offers
/// the import as a quick fix.
#[test]
fn code_action_imports_cross_document_name() {
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let u = uri("u.sysml");
    client.open(&defs, "package Defs { part def Wheel; }\n");
    client.open(&u, "package U {\n    part w : Wheel;\n}\n");

    let range = Range {
        start: Position {
            line: 1,
            character: 13,
        },
        end: Position {
            line: 1,
            character: 18,
        },
    };
    let resp =
        client.request_ok::<lsp_types::request::CodeActionRequest>(lsp_types::CodeActionParams {
            text_document: TextDocumentIdentifier { uri: u.clone() },
            range,
            context: lsp_types::CodeActionContext {
                diagnostics: vec![lsp_types::Diagnostic {
                    range,
                    message: "unresolved reference `Wheel`".to_string(),
                    ..Default::default()
                }],
                ..Default::default()
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        });
    let actions = resp.expect("actions");
    let fix = actions
        .iter()
        .find_map(|a| match a {
            lsp_types::CodeActionOrCommand::CodeAction(a)
                if a.title == "Add import Defs::Wheel" =>
            {
                Some(a)
            }
            _ => None,
        })
        .expect("import quick fix offered");
    let edits = fix
        .edit
        .as_ref()
        .and_then(|e| e.changes.as_ref())
        .and_then(|c| c.get(&u))
        .expect("edit on the referencing document");
    assert_eq!(edits[0].new_text, "private import Defs::Wheel;\n    ");
    assert_eq!(
        edits[0].range.start,
        Position {
            line: 1,
            character: 4
        }
    );
    client.shutdown();
}

#[test]
fn completion_items_carry_doc_bodies() {
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let u = uri("u.sysml");
    client.open(
        &defs,
        "package Defs {\n    part def Gadget {\n        doc /* A documented gadget. */\n    }\n    part def Plain;\n}\n",
    );
    client.open(&u, "package U {\n    part g : \n}\n");

    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: u },
            position: Position {
                line: 1,
                character: 13,
            },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    let Some(CompletionResponse::Array(items)) = resp else {
        panic!("expected items: {resp:?}");
    };
    let gadget = items
        .iter()
        .find(|i| i.label == "Gadget")
        .expect("`Gadget`");
    let Some(lsp_types::Documentation::MarkupContent(m)) = &gadget.documentation else {
        panic!(
            "expected markdown documentation: {:?}",
            gadget.documentation
        );
    };
    assert_eq!(m.value, "A documented gadget.");
    let plain = items.iter().find(|i| i.label == "Plain").expect("`Plain`");
    assert!(
        plain.documentation.is_none(),
        "undocumented symbol stays bare"
    );
    client.shutdown();
}

#[test]
fn inlay_hints_show_evaluated_values_and_ranges() {
    let mut client = Client::start();
    let u = uri("h.sysml");
    // `total` computes (evaluated-value hint after the expression);
    // `x` is unbound but constrained (propagated-range hint after the
    // declared name).
    client.open(
        &u,
        "part def P {\n    attribute a = 2;\n    attribute total = a + 3;\n    attribute x;\n    assert constraint { x > 10 }\n}\n",
    );
    let hints: Option<Vec<lsp_types::InlayHint>> =
        client.request_ok::<InlayHintRequest>(InlayHintParams {
            text_document: TextDocumentIdentifier { uri: u },
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 6,
                    character: 0,
                },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let hints = hints.unwrap();
    let labels: Vec<String> = hints
        .iter()
        .map(|h| match &h.label {
            InlayHintLabel::String(s) => s.clone(),
            other => panic!("unexpected label shape: {other:?}"),
        })
        .collect();
    assert!(
        labels.iter().any(|l| l.contains("= 5")),
        "evaluated value for `total`: {labels:?}"
    );
    assert!(
        labels.iter().any(|l| l.contains('∈') && l.contains("10")),
        "propagated range for `x`: {labels:?}"
    );
    // The value hint sits at the end of `a + 3`.
    let value_hint = hints
        .iter()
        .find(|h| matches!(&h.label, InlayHintLabel::String(s) if s.contains("= 5")))
        .unwrap();
    assert_eq!(value_hint.position.line, 2);
    client.shutdown();
}

#[test]
fn inlay_hints_show_non_terminating_rationals_as_approximate_decimals() {
    let mut client = Client::start();
    let u = uri("r.sysml");
    // Exact decimals hint exactly; a rational with no terminating
    // decimal expansion hints as a marked approximation rather than the
    // fraction the CLI prints.
    client.open(
        &u,
        "part def P {\n    attribute tenth = 0.1 + 0.2;\n    attribute third = 2 / 6;\n    attribute mm;\n    attribute pitch = (1 / 3) [mm];\n}\n",
    );
    let hints: Option<Vec<lsp_types::InlayHint>> =
        client.request_ok::<InlayHintRequest>(InlayHintParams {
            text_document: TextDocumentIdentifier { uri: u },
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 6,
                    character: 0,
                },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let labels: Vec<String> = hints
        .unwrap()
        .iter()
        .map(|h| match &h.label {
            InlayHintLabel::String(s) => s.clone(),
            other => panic!("unexpected label shape: {other:?}"),
        })
        .collect();
    assert!(labels.iter().any(|l| l == " = 0.3"), "{labels:?}");
    assert!(
        labels.iter().any(|l| l == " = ≈0.3333333333333333"),
        "{labels:?}"
    );
    assert!(
        labels.iter().any(|l| l == " = ≈0.3333333333333333 [mm]"),
        "{labels:?}"
    );
    assert!(!labels.iter().any(|l| l.contains("1/3")), "{labels:?}");
    client.shutdown();
}

#[test]
fn inlay_hints_land_after_closing_parenthesis() {
    let mut client = Client::start();
    let u = uri("paren.sysml");
    // The value expression ends in `)`; the hint belongs after it
    // (immediately before `;`), not after the last inner token.
    let line = "    attribute w = (1 + a)*(1 + a);";
    client.open(
        &u,
        &format!("part def P {{\n    attribute a = 2;\n{line}\n}}\n"),
    );
    let hints: Option<Vec<lsp_types::InlayHint>> =
        client.request_ok::<InlayHintRequest>(InlayHintParams {
            text_document: TextDocumentIdentifier { uri: u },
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 4,
                    character: 0,
                },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let hint = hints
        .unwrap()
        .into_iter()
        .find(|h| matches!(&h.label, InlayHintLabel::String(s) if s.contains("= 9")))
        .expect("evaluated value for `w`");
    assert_eq!(hint.position.line, 2);
    assert_eq!(
        hint.position.character as usize,
        line.find(';').unwrap(),
        "hint sits after the closing `)`"
    );
    client.shutdown();
}

#[test]
fn redundant_value_hints_hidden_by_default_and_by_option() {
    // `m`'s hint would restate the declared expression (` = -5` after
    // `-5`) — suppressed by default; `total` still computes.
    let text = "part def P {\n    attribute m = -5;\n    attribute total = 2 + 3;\n}\n";
    let pull = |client: &mut Client, u: &Uri| -> Vec<(u32, String)> {
        let hints: Option<Vec<lsp_types::InlayHint>> =
            client.request_ok::<InlayHintRequest>(InlayHintParams {
                text_document: TextDocumentIdentifier { uri: u.clone() },
                range: Range {
                    start: Position {
                        line: 0,
                        character: 0,
                    },
                    end: Position {
                        line: 4,
                        character: 0,
                    },
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
            });
        hints
            .unwrap()
            .iter()
            .map(|h| match &h.label {
                InlayHintLabel::String(s) => (h.position.line, s.clone()),
                other => panic!("unexpected label shape: {other:?}"),
            })
            .collect()
    };

    let mut client = Client::start();
    let u = uri("dup.sysml");
    client.open(&u, text);
    let labels = pull(&mut client, &u);
    assert!(
        !labels.iter().any(|(line, _)| *line == 1),
        "verbatim restatement stays unhinted: {labels:?}"
    );
    assert!(
        labels
            .iter()
            .any(|(line, l)| *line == 2 && l.contains("= 5")),
        "computed value still hinted: {labels:?}"
    );
    client.shutdown();

    // Opting out via initializationOptions brings the hint back.
    let mut client = Client::start_with(InitializeParams {
        initialization_options: Some(serde_json::json!({
            "hideRedundantValueHints": false
        })),
        ..InitializeParams::default()
    });
    let u = uri("dup2.sysml");
    client.open(&u, text);
    let labels = pull(&mut client, &u);
    assert!(
        labels
            .iter()
            .any(|(line, l)| *line == 1 && l.contains("= -5")),
        "opt-out restores the verbatim hint: {labels:?}"
    );
    client.shutdown();
}

#[test]
fn inlay_hints_name_element_values_but_skip_bare_references() {
    let mut client = Client::start();
    let u = uri("e.sysml");
    // `pick` *computes* an enum literal — hint it by name; `m` is a
    // bare reference to one — the source already spells it, no hint
    // (and never the opaque `<element>`).
    client.open(
        &u,
        "package Q {\n    enum def Mode { fast; slow; }\n    part def P {\n        attribute m : Mode = Mode::fast;\n        attribute cond = true;\n        attribute pick : Mode = if cond ? Mode::fast else Mode::slow;\n    }\n}\n",
    );
    let hints: Option<Vec<lsp_types::InlayHint>> =
        client.request_ok::<InlayHintRequest>(InlayHintParams {
            text_document: TextDocumentIdentifier { uri: u },
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 8,
                    character: 0,
                },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let labels: Vec<(u32, String)> = hints
        .unwrap()
        .iter()
        .map(|h| match &h.label {
            InlayHintLabel::String(s) => (h.position.line, s.clone()),
            other => panic!("unexpected label shape: {other:?}"),
        })
        .collect();
    assert!(
        labels
            .iter()
            .any(|(line, l)| *line == 5 && l.contains("= fast")),
        "computed element value named: {labels:?}"
    );
    assert!(
        !labels.iter().any(|(line, _)| *line == 3),
        "bare reference stays unhinted: {labels:?}"
    );
    assert!(
        !labels.iter().any(|(_, l)| l.contains("<element>")),
        "{labels:?}"
    );
    client.shutdown();
}

#[test]
fn code_lenses_carry_verify_verdicts() {
    let mut client = Client::start();
    let u = uri("v.sysml");
    client.open(
        &u,
        "part def P {\n    attribute a = 5;\n    assert constraint ok { a > 1 }\n    assert constraint bad { a > 9 }\n    attribute y;\n    assert constraint open { y > 0 }\n}\n",
    );
    let lenses: Option<Vec<lsp_types::CodeLens>> =
        client.request_ok::<CodeLensRequest>(CodeLensParams {
            text_document: TextDocumentIdentifier { uri: u },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        });
    let lenses = lenses.unwrap();
    let titles: Vec<(u32, String)> = lenses
        .iter()
        .map(|l| {
            (
                l.range.start.line,
                l.command.as_ref().unwrap().title.clone(),
            )
        })
        .collect();
    assert!(
        titles
            .iter()
            .any(|(line, t)| *line == 2 && t == "✓ satisfied"),
        "{titles:?}"
    );
    // Violated lenses explain themselves with the evaluated values.
    assert!(
        titles
            .iter()
            .any(|(line, t)| *line == 3 && t == "✗ VIOLATED (with a = 5)"),
        "{titles:?}"
    );
    assert!(
        titles.iter().any(
            |(line, t)| *line == 5 && (t.starts_with("undecided") || t.contains("propagation"))
        ),
        "{titles:?}"
    );
    client.shutdown();
}

/// A definition named by a reserved word completes as source: the
/// label is the raw name, the insert text and the auto-import path
/// quote it.
#[test]
fn completion_quotes_reserved_word_names_in_edits() {
    let mut client = Client::start();
    let defs = uri("defs.sysml");
    let u = uri("u.sysml");
    client.open(&defs, "package Defs { part def 'view'; }\n");
    client.open(&u, "package U {\n    part w : \n}\n");
    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: u },
            position: Position {
                line: 1,
                character: 13,
            },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    let Some(CompletionResponse::Array(items)) = resp else {
        panic!("expected items: {resp:?}");
    };
    let view = items
        .iter()
        .find(|i| i.label == "view" && i.kind == Some(CompletionItemKind::CLASS))
        .expect("cross-document name `view`");
    let Some(lsp_types::CompletionTextEdit::Edit(edit)) = &view.text_edit else {
        panic!("quoted insert text needs an edit: {view:?}");
    };
    assert!(edit.new_text.starts_with("'view'"), "{edit:?}");
    let edits = view
        .additional_text_edits
        .as_ref()
        .expect("out-of-scope name carries the import edit");
    assert_eq!(edits[0].new_text, "private import Defs::'view';\n    ");
    client.shutdown();
}

/// The document's dialect governs the spelling: in a KerML document a
/// word only SysML reserves is a plain name, so the insert text and the
/// auto-import path stay bare — quoting would be legal but the
/// formatter would immediately undo it.
#[test]
fn completion_spells_for_the_document_dialect() {
    let mut client = Client::start();
    let defs = uri("defs.kerml");
    let u = uri("u.kerml");
    client.open(&defs, "package Defs { classifier part; }\n");
    client.open(&u, "package U {\n    feature w : \n}\n");
    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: u },
            position: Position {
                line: 1,
                character: 16,
            },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    let Some(CompletionResponse::Array(items)) = resp else {
        panic!("expected items: {resp:?}");
    };
    let part = items
        .iter()
        .find(|i| i.label == "part" && i.kind == Some(CompletionItemKind::CLASS))
        .expect("cross-document name `part`");
    if let Some(lsp_types::CompletionTextEdit::Edit(edit)) = &part.text_edit {
        assert!(edit.new_text.starts_with("part"), "{edit:?}");
        assert!(!edit.new_text.starts_with("'"), "{edit:?}");
    }
    let edits = part
        .additional_text_edits
        .as_ref()
        .expect("out-of-scope name carries the import edit");
    assert_eq!(edits[0].new_text, "private import Defs::part;\n    ");
    client.shutdown();
}
