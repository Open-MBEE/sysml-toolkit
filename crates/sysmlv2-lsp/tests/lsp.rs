//! Protocol-level harness: drives the server in-process over
//! `Connection::memory()` — the full JSON-RPC surface without a child
//! process. Every assertion here is what a real editor would observe.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{Formatting, Initialize, Shutdown};
use lsp_types::{
    ClientCapabilities, DiagnosticSeverity, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
    DocumentFormattingParams, FormattingOptions, GeneralClientCapabilities, InitializeParams,
    InitializeResult, PositionEncodingKind, PublishDiagnosticsParams,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, TextEdit, Uri,
    VersionedTextDocumentIdentifier,
};
use std::str::FromStr;
use std::thread::JoinHandle;

/// An in-process LSP client: the other end of `Connection::memory()`.
struct Client {
    conn: Connection,
    server: Option<JoinHandle<Result<(), Box<dyn std::error::Error + Send + Sync>>>>,
    next_id: i32,
}

impl Client {
    /// Start a server thread and complete the initialize handshake.
    /// `utf8` opts the client into the utf-8 position encoding.
    fn start(utf8: bool) -> (Client, InitializeResult) {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || sysmlv2_lsp::run(server_side));
        let mut client = Client {
            conn: client_side,
            server: Some(server),
            next_id: 0,
        };
        let params = InitializeParams {
            capabilities: ClientCapabilities {
                general: utf8.then(|| GeneralClientCapabilities {
                    position_encodings: Some(vec![
                        PositionEncodingKind::UTF8,
                        PositionEncodingKind::UTF16,
                    ]),
                    ..Default::default()
                }),
                ..Default::default()
            },
            ..Default::default()
        };
        let init: InitializeResult = client.request::<Initialize>(params);
        client.notify::<Initialized>(lsp_types::InitializedParams {});
        (client, init)
    }

    fn request<R: lsp_types::request::Request>(&mut self, params: R::Params) -> R::Result {
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
                    assert!(error.is_none(), "{}: {error:?}", R::METHOD);
                    return serde_json::from_value(result.unwrap_or_default()).unwrap();
                }
                _ => continue, // interleaved notifications
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

    /// The next publishDiagnostics notification, skipping everything else.
    fn recv_diagnostics(&self) -> PublishDiagnosticsParams {
        loop {
            if let Message::Notification(n) = self.conn.receiver.recv().unwrap() {
                if n.method == "textDocument/publishDiagnostics" {
                    return serde_json::from_value(n.params).unwrap();
                }
            }
        }
    }

    fn open(&self, uri: &Uri, version: i32, text: &str) -> PublishDiagnosticsParams {
        self.notify::<DidOpenTextDocument>(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: uri.clone(),
                language_id: "sysml".to_string(),
                version,
                text: text.to_string(),
            },
        });
        self.recv_diagnostics()
    }

    fn change(&self, uri: &Uri, version: i32, text: &str) -> PublishDiagnosticsParams {
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
        self.recv_diagnostics()
    }

    fn format(&mut self, uri: &Uri) -> Option<Vec<TextEdit>> {
        self.request::<Formatting>(DocumentFormattingParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            options: FormattingOptions::default(),
            work_done_progress_params: Default::default(),
        })
    }

    /// shutdown + exit; asserts the server thread ends cleanly.
    fn shutdown(mut self) {
        self.request::<Shutdown>(());
        self.notify::<Exit>(());
        self.server
            .take()
            .unwrap()
            .join()
            .expect("server thread panicked")
            .expect("server main loop errored");
    }
}

fn uri(name: &str) -> Uri {
    Uri::from_str(&format!("file:///harness/{name}")).unwrap()
}

#[test]
fn initialize_negotiates_encoding_and_capabilities() {
    let (client, init) = Client::start(false);
    assert_eq!(
        init.capabilities.position_encoding,
        Some(PositionEncodingKind::UTF16)
    );
    assert!(init.capabilities.text_document_sync.is_some());
    assert!(init.capabilities.document_formatting_provider.is_some());
    client.shutdown();

    let (client, init) = Client::start(true);
    assert_eq!(
        init.capabilities.position_encoding,
        Some(PositionEncodingKind::UTF8)
    );
    client.shutdown();
}

#[test]
fn parse_error_diagnostics_then_fix_converges_to_zero() {
    let (client, _) = Client::start(false);
    let uri = uri("m.sysml");

    // Missing member semicolon: the parser repairs and reports at the
    // end of the declaration's own line (1, 0-based), not at the `}`
    // where the failure was discovered.
    let diags = client.open(&uri, 1, "part def P {\n    part q\n}\n");
    assert_eq!(diags.uri, uri);
    assert_eq!(diags.version, Some(1));
    assert!(!diags.diagnostics.is_empty(), "expected a parse diagnostic");
    let d = &diags.diagnostics[0];
    assert_eq!(d.severity, Some(DiagnosticSeverity::ERROR));
    assert_eq!(d.source.as_deref(), Some("sysmlv2"));
    assert!(d.message.contains("missing `;`"), "{d:?}");
    assert_eq!(
        d.range.start.line, 1,
        "reported at the end of the declaration: {d:?}"
    );
    assert_eq!(d.range.start.character, 10, "after `part q`: {d:?}");

    let diags = client.change(&uri, 2, "part def P {\n    part q;\n}\n");
    assert_eq!(diags.version, Some(2));
    assert!(
        diags.diagnostics.is_empty(),
        "fixed file still reports: {:?}",
        diags.diagnostics
    );
    client.shutdown();
}

#[test]
fn body_context_validation_reaches_the_wire() {
    let (client, _) = Client::start(false);
    // Parses fine; body-context validation rejects the variant
    // member outside a variation. This proves check::validate's
    // diagnostics ride the same publish as the parser's.
    let diags = client.open(&uri("v.sysml"), 1, "part def P {\n    variant part q;\n}\n");
    assert!(
        diags
            .diagnostics
            .iter()
            .any(|d| d.message.contains("variant")),
        "expected a variant-ownership finding: {:?}",
        diags.diagnostics
    );
    client.shutdown();
}

#[test]
fn kerml_documents_parse_in_the_kerml_dialect() {
    let (client, _) = Client::start(false);
    // `struct` is KerML-only: clean under .kerml, an error under .sysml.
    let diags = client.open(&uri("k.kerml"), 1, "package K {\n    struct S;\n}\n");
    assert!(diags.diagnostics.is_empty(), "{:?}", diags.diagnostics);
    let diags = client.open(&uri("k.sysml"), 1, "package K {\n    struct S;\n}\n");
    assert!(!diags.diagnostics.is_empty());
    client.shutdown();
}

#[test]
fn formatting_returns_formatter_output_and_is_idempotent() {
    let (mut client, _) = Client::start(false);
    let uri = uri("f.sysml");
    let ugly = "package  P   {part def Q ;}";
    client.open(&uri, 1, ugly);

    let edits = client.format(&uri).expect("formattable document");
    assert_eq!(edits.len(), 1);
    let expected = sysmlv2_parser::print::format_source(ugly, sysmlv2_parser::ast::Dialect::Sysml)
        .expect("fixture formats");
    assert_eq!(
        edits[0].new_text, expected,
        "LSP edit must be the formatter's output"
    );
    assert_eq!(
        edits[0].range.start,
        lsp_types::Position {
            line: 0,
            character: 0
        }
    );

    // Apply the edit (full-document range) and re-format: no edits left.
    client.change(&uri, 2, &expected);
    let edits = client.format(&uri).expect("still formattable");
    assert!(edits.is_empty(), "formatted document must produce no edits");
    client.shutdown();
}

#[test]
fn formatting_a_broken_document_warns_and_leaves_it_alone() {
    let (client, _) = Client::start(false);
    let uri = uri("b.sysml");
    client.open(&uri, 1, "part def P {");
    // Manual request: the refusal warning rides ahead of the response,
    // and the generic helper would skip it.
    let id = lsp_server::RequestId::from(9001);
    client
        .conn
        .sender
        .send(Message::Request(lsp_server::Request::new(
            id.clone(),
            "textDocument/formatting".to_string(),
            DocumentFormattingParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                options: FormattingOptions::default(),
                work_done_progress_params: Default::default(),
            },
        )))
        .unwrap();
    let mut warned: Option<lsp_types::ShowMessageParams> = None;
    let edits: Option<Vec<TextEdit>> = loop {
        match client.conn.receiver.recv().unwrap() {
            Message::Notification(n) if n.method == "window/showMessage" => {
                warned = Some(serde_json::from_value(n.params).unwrap());
            }
            Message::Response(Response {
                id: rid,
                result,
                error,
            }) if rid == id => {
                assert!(error.is_none(), "{error:?}");
                break serde_json::from_value(result.unwrap_or_default()).unwrap();
            }
            _ => continue,
        }
    };
    assert_eq!(edits, None, "refusal answers null, not an empty edit list");
    let w = warned.expect("the refusal is announced, not silent");
    assert_eq!(w.typ, lsp_types::MessageType::WARNING);
    assert!(w.message.contains("syntax error"), "{}", w.message);
    client.shutdown();
}

#[test]
fn utf16_and_utf8_columns_differ_after_an_astral_character() {
    // "😀" (4 bytes, 2 UTF-16 units) sits inside a quoted name *before*
    // a parse error on the same line, so the two encodings must report
    // different columns for the same byte offset.
    let text = "part def '😀' ,;\n";
    let err_byte = text.find(',').unwrap() as u32;
    let (client, _) = Client::start(false);
    let d16 = client.open(&uri("e.sysml"), 1, text);
    client.shutdown();
    let (client, _) = Client::start(true);
    let d8 = client.open(&uri("e.sysml"), 1, text);
    client.shutdown();
    assert!(!d16.diagnostics.is_empty() && !d8.diagnostics.is_empty());
    let (p16, p8) = (
        d16.diagnostics[0].range.start,
        d8.diagnostics[0].range.start,
    );
    assert_eq!(p16.line, 0);
    assert_eq!(p8.line, 0);
    assert_eq!(p8.character, err_byte, "utf-8 characters are byte columns");
    assert_eq!(
        p16.character,
        err_byte - 2,
        "utf-16 counts the astral char as 2 units, not 4 bytes"
    );
}

#[test]
fn document_symbols_form_the_expected_tree() {
    use lsp_types::request::DocumentSymbolRequest;
    use lsp_types::{DocumentSymbolParams, DocumentSymbolResponse, SymbolKind};
    let (mut client, _) = Client::start(false);
    let uri = uri("o.sysml");
    client.open(
        &uri,
        1,
        "package Demo {\n\
         \x20   import Lib::*;\n\
         \x20   part def Vehicle :> Base {\n\
         \x20       attribute mass : Real [1];\n\
         \x20       part wheels : Wheel [4];\n\
         \x20       part ;\n\
         \x20   }\n\
         \x20   enum def Phase { halt; mid; }\n\
         }\n",
    );
    let resp: Option<DocumentSymbolResponse> =
        client.request::<DocumentSymbolRequest>(DocumentSymbolParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let Some(DocumentSymbolResponse::Nested(top)) = resp else {
        panic!("expected a nested response: {resp:?}");
    };
    assert_eq!(top.len(), 1);
    let demo = &top[0];
    assert_eq!(
        (demo.name.as_str(), demo.kind),
        ("Demo", SymbolKind::PACKAGE)
    );
    let children = demo.children.as_ref().unwrap();
    let names: Vec<&str> = children.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(names, ["Lib", "Vehicle", "Phase"]);
    assert_eq!(children[1].kind, SymbolKind::CLASS);
    assert_eq!(children[1].detail.as_deref(), Some(":> Base"));

    let vehicle = children[1].children.as_ref().unwrap();
    let entries: Vec<(&str, SymbolKind, Option<&str>)> = vehicle
        .iter()
        .map(|c| (c.name.as_str(), c.kind, c.detail.as_deref()))
        .collect();
    assert_eq!(
        entries,
        [
            ("mass", SymbolKind::PROPERTY, Some(": Real [1]")),
            ("wheels", SymbolKind::FIELD, Some(": Wheel [4]")),
            // Anonymous member: labeled by keyword, still present.
            ("«part»", SymbolKind::FIELD, None),
        ]
    );

    let color = children[2].children.as_ref().unwrap();
    assert!(color.iter().all(|c| c.kind == SymbolKind::ENUM_MEMBER));
    assert_eq!(color.len(), 2);

    // Selection ranges point at the names, inside the member ranges.
    let v = &children[1];
    assert!(v.range.start <= v.selection_range.start && v.selection_range.end <= v.range.end);
    assert_eq!(v.selection_range.start.line, 2);
    client.shutdown();
}

#[test]
fn semantic_tokens_are_dialect_aware() {
    use lsp_types::request::SemanticTokensFullRequest;
    use lsp_types::{SemanticTokensParams, SemanticTokensResult};

    // Decode the wire deltas into (line, char, len, type_index).
    fn decode(result: Option<SemanticTokensResult>) -> Vec<(u32, u32, u32, u32)> {
        let Some(SemanticTokensResult::Tokens(t)) = result else {
            panic!("expected tokens: {result:?}");
        };
        let (mut line, mut ch) = (0u32, 0u32);
        t.data
            .iter()
            .map(|d| {
                if d.delta_line > 0 {
                    line += d.delta_line;
                    ch = d.delta_start;
                } else {
                    ch += d.delta_start;
                }
                (line, ch, d.length, d.token_type)
            })
            .collect()
    }
    let fetch = |client: &mut Client, uri: &Uri| {
        decode(
            client.request::<SemanticTokensFullRequest>(SemanticTokensParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            }),
        )
    };
    // Legend indices (see tokens::legend_types): 1 = type, 3 = variable,
    // 5 = keyword, 6 = comment, 8 = number.
    let (mut client, init) = Client::start(false);
    let legend = match init.capabilities.semantic_tokens_provider.unwrap() {
        lsp_types::SemanticTokensServerCapabilities::SemanticTokensOptions(o) => o.legend,
        other => panic!("unexpected provider shape: {other:?}"),
    };
    assert_eq!(legend.token_types[5], lsp_types::SemanticTokenType::KEYWORD);

    // The canary: `part` is a keyword in SysML…
    let s = uri("d.sysml");
    client.open(&s, 1, "part def Wheel;\npart w : Wheel = 4; // note\n");
    let toks = fetch(&mut client, &s);
    // line 0: `part`(kw) `def`(kw) `Wheel`(type+decl)
    assert_eq!(toks[0], (0, 0, 4, 5), "sysml `part` is a keyword: {toks:?}");
    assert_eq!(toks[1], (0, 5, 3, 5), "`def` is a keyword");
    assert_eq!(toks[2], (0, 9, 5, 1), "`Wheel` declares a type");
    // line 1: `part`(kw) `w`(var) `Wheel`(type ref) `4`(number) note(comment)
    assert_eq!(toks[3], (1, 0, 4, 5));
    assert_eq!(toks[4].3, 3, "`w` is a variable: {toks:?}");
    assert_eq!(toks[5].3, 1, "`: Wheel` is a type reference");
    assert_eq!(toks[6].3, 8, "`4` is a number");
    assert_eq!(toks[7].3, 6, "the note is a comment");

    // …and a legal *name* in KerML: `feature part : Wheel;`
    let k = uri("d.kerml");
    client.open(&k, 1, "feature part : Wheel;\n");
    let toks = fetch(&mut client, &k);
    assert_eq!(toks[0], (0, 0, 7, 5), "`feature` is the keyword");
    assert_eq!(
        toks[1],
        (0, 8, 4, 3),
        "kerml `part` is a declared name, not a keyword: {toks:?}"
    );
    client.shutdown();
}

#[test]
fn unknown_request_gets_method_not_found() {
    let (client, _) = Client::start(false);
    client
        .conn
        .sender
        .send(Message::Request(Request::new(
            RequestId::from(99),
            "textDocument/signatureHelp".to_string(),
            serde_json::json!({}),
        )))
        .unwrap();
    loop {
        if let Message::Response(r) = client.conn.receiver.recv().unwrap() {
            assert_eq!(r.id, RequestId::from(99));
            assert!(r.error.is_some(), "signatureHelp is not implemented");
            break;
        }
    }
    client.shutdown();
}
