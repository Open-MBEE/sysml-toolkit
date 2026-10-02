#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Signatures of the standard library's callables — in signature help
//! and in hover — against the library itself.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{HoverRequest, Initialize, Shutdown, SignatureHelpRequest};
use lsp_types::{
    DidOpenTextDocumentParams, HoverParams, InitializeParams, Position, SignatureHelpParams,
    TextDocumentIdentifier, TextDocumentItem, TextDocumentPositionParams, Uri,
    WorkDoneProgressParams,
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
        let lib = sysmlv2_testkit::library_dir();
        let server =
            std::thread::spawn(move || sysmlv2_lsp::run_with_library(server_side, Some(lib)));
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

    /// The signature label signature help answers at the end of `line`
    /// (0-based) of `uri`.
    fn signature(&mut self, uri: &Uri, line: u32, character: u32) -> Option<String> {
        let help = self.request_ok::<SignatureHelpRequest>(SignatureHelpParams {
            context: None,
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position { line, character },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
        help.map(|h| h.signatures[0].label.clone())
    }

    /// The signature line a hover at `line`/`character` leads with.
    fn hover_signature(&mut self, uri: &Uri, line: u32, character: u32) -> Option<String> {
        let hover = self.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position { line, character },
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        })?;
        let lsp_types::HoverContents::Markup(m) = hover.contents else {
            panic!("markup hover")
        };
        let body = m.value.strip_prefix("```sysml-signature\n")?;
        Some(body[..body.find('\n')?].to_string())
    }
}

/// A library callable's signature spells its types from the model —
/// the library's text is not at hand to slice them from — the shortest
/// way that resolves where the signature is read, with a multiplicity
/// other than one: in signature help and hover alike.
#[test]
fn library_callables_spell_their_types_from_the_model() {
    let mut client = Client::start();
    let used = uri("used.sysml");
    client.open(
        &used,
        "package P {\n    private import RealFunctions::*;\n    attribute a = sqrt(2.0);\n    \
         attribute b = max(1.0, 2.0);\n    attribute c = RealFunctions::sum((1.0, 2.0));\n}\n",
    );
    // `Real` is visible through `RealFunctions`, which re-exports it.
    for (line, character, label) in [
        (2u32, 19u32, "sqrt(x: Real) → Real"),
        (3, 19, "max(x: Real, y: Real) → Real"),
        (4, 34, "sum(collection: Real[0..*]) → Real"),
    ] {
        assert_eq!(
            client.hover_signature(&used, line, character).as_deref(),
            Some(label)
        );
    }
    let typed = uri("typed.sysml");
    client.open(
        &typed,
        "package Q {\n    private import RealFunctions::*;\n    attribute d = sqrt(\n    \
         attribute f = max(1.0, \n    attribute g = RealFunctions::sum(\n}\n",
    );
    for (line, character, label) in [
        (2u32, 23u32, "sqrt(x: Real) → Real"),
        (3, 27, "max(x: Real, y: Real) → Real"),
        (4, 37, "sum(collection: Real[0..*]) → Real"),
    ] {
        assert_eq!(
            client.signature(&typed, line, character).as_deref(),
            Some(label)
        );
    }
    // Where nothing makes `Real` visible, its package qualifies it.
    for (name, text, character) in [
        (
            "bare.sysml",
            "package R {\n    attribute d = RealFunctions::sqrt(\n}\n",
            38u32,
        ),
        (
            "bare.kerml",
            "package S {\n    feature d = RealFunctions::sqrt(\n}\n",
            36,
        ),
    ] {
        let u = uri(name);
        client.open(&u, text);
        assert_eq!(
            client.signature(&u, 1, character).as_deref(),
            Some("sqrt(x: ScalarValues::Real) → ScalarValues::Real"),
            "{name}"
        );
    }
    client.shutdown();
}
