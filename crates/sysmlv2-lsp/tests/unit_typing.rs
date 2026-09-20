#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Unit-completion typing (the `inferUnitTypes` behavior): accepting a
//! unit completion inside an untyped attribute's quantity bracket also
//! declares the type the unit determines — exactly one, spelled
//! shortest-that-resolves — and the initialization option turns it off.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{Completion, Initialize, Shutdown};
use lsp_types::{
    CompletionParams, CompletionResponse, DidOpenTextDocumentParams, InitializeParams,
    PartialResultParams, Position, TextDocumentIdentifier, TextDocumentItem,
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
    fn start_with(init: InitializeParams) -> Client {
        let (server_side, client_side) = Connection::memory();
        let lib = sysmlv2_testkit::library_dir();
        let server =
            std::thread::spawn(move || sysmlv2_lsp::run_with_library(server_side, Some(lib)));
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
                _ => {}
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

fn complete(
    client: &mut Client,
    uri: &Uri,
    line: u32,
    character: u32,
) -> Vec<lsp_types::CompletionItem> {
    let resp = client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: Position { line, character },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    });
    match resp {
        Some(CompletionResponse::Array(items)) => items,
        other => panic!("expected items: {other:?}"),
    }
}

const DOC: &str = "package G {\n    private import ISQ::*;\n    private import SI::*;\n    attribute gravity = 9.8 [k\n}\n";

#[test]
fn accepting_a_unit_completion_declares_the_inferred_type() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("g.sysml");
    client.open(&u, DOC);
    // Cursor after `[k` on line 3.
    let items = complete(&mut client, &u, 3, 30);
    let kg = items.iter().find(|i| i.label == "kg").expect("`kg` item");
    let edits = kg.additional_text_edits.as_ref().expect("typing edit");
    let typing = edits
        .iter()
        .find(|e| e.new_text == " : MassValue")
        .unwrap_or_else(|| panic!("expected ` : MassValue` insert: {edits:?}"));
    // Right after the declared name `gravity`.
    assert_eq!(
        typing.range.start,
        Position {
            line: 3,
            character: 21
        }
    );
    assert_eq!(typing.range.end, typing.range.start);
    // The dimensionally ambiguous kelvin inserts nothing (two library
    // quantity types share the unit).
    let k = items.iter().find(|i| i.label == "K").expect("`K` item");
    let k_typing = k
        .additional_text_edits
        .iter()
        .flatten()
        .any(|e| e.new_text.starts_with(" : "));
    assert!(!k_typing, "{:?}", k.additional_text_edits);
    client.shutdown();
}

#[test]
fn compound_spelled_units_type_through_their_alias() {
    // The motivating flow: `= 9.8 [m/s` completing to the quoted
    // acceleration unit re-spells the whole bracket content and
    // declares the acceleration type alongside.
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("a.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    attribute gravity = 9.8 [m/s\n}\n",
    );
    let items = complete(&mut client, &u, 3, 32);
    let mut accel = items.iter().filter(|i| {
        i.additional_text_edits
            .iter()
            .flatten()
            .any(|e| e.new_text == " : AccelerationValue")
    });
    assert!(
        accel.next().is_some(),
        "expected an acceleration-unit item carrying the typing edit"
    );
    client.shutdown();
}

#[test]
fn typed_declarations_and_opt_out_insert_nothing() {
    // Already typed: no insert.
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("t.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    attribute gravity : MassValue = 9.8 [k\n}\n",
    );
    let items = complete(&mut client, &u, 3, 42);
    let kg = items.iter().find(|i| i.label == "kg").expect("`kg` item");
    let typing = kg
        .additional_text_edits
        .iter()
        .flatten()
        .any(|e| e.new_text.starts_with(" : "));
    assert!(!typing, "{:?}", kg.additional_text_edits);
    client.shutdown();

    // The initialization option turns the behavior off wholesale.
    let mut client = Client::start_with(InitializeParams {
        initialization_options: Some(serde_json::json!({ "inferUnitTypes": false })),
        ..InitializeParams::default()
    });
    let u = uri("g2.sysml");
    client.open(&u, DOC);
    let items = complete(&mut client, &u, 3, 30);
    let kg = items.iter().find(|i| i.label == "kg").expect("`kg` item");
    let typing = kg
        .additional_text_edits
        .iter()
        .flatten()
        .any(|e| e.new_text.starts_with(" : "));
    assert!(!typing, "{:?}", kg.additional_text_edits);
    client.shutdown();
}
