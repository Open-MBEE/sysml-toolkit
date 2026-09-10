//! `sysmlv2-lsp` — Language Server Protocol server for SysML v2 / KerML
//! (server skeleton, full-text document sync, syntax-tier diagnostics,
//! formatting).
//!
//! Architecture: a synchronous main loop over `lsp-server` — no async
//! runtime. Every operation served here is syntax-tier (whole-file reparse
//! is sub-millisecond), so requests are answered in-line in arrival order;
//! the debounced model tier (library-aware diagnostics) lives in the
//! background worker.
//! Documents sync as full text — the parser is the only authority on
//! syntax, and reparsing beats patching. Position encoding negotiates
//! UTF-8 when the client offers it (LSP 3.17), UTF-16 otherwise.
//!
//! The entry points are [`run_stdio`] (the `sysmlv2 lsp` verb) and [`run`]
//! over an arbitrary [`Connection`] (the in-process test harness).

// lsp-types mandates `Uri` map keys (WorkspaceEdit::changes, the
// document store); the type is never mutated while keyed.
#![allow(clippy::mutable_key_type)]

use lsp_server::{Connection, ErrorCode, Message, Notification, Request, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{
    CodeActionRequest, CodeLensRequest, Completion, DocumentHighlightRequest,
    DocumentSymbolRequest, Formatting, GotoDefinition, HoverRequest, InlayHintRequest, References,
    Rename, Request as _, SemanticTokensFullRequest, WorkspaceSymbolRequest,
};
use lsp_types::{
    DiagnosticSeverity, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DocumentFormattingParams, DocumentSymbolParams,
    DocumentSymbolResponse, InitializeParams, InitializeResult, OneOf, PositionEncodingKind,
    PublishDiagnosticsParams, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextEdit, Uri,
};
use std::collections::HashMap;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::check;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

mod autofix;
mod autoimport;
mod nav;
mod outline;
mod position;
mod push;
pub mod tokens;
mod worker;

pub use outline::document_symbols;
pub use position::{Encoding, Mapper};
pub use push::PushServer;

type Error = Box<dyn std::error::Error + Send + Sync>;

/// Serve LSP over stdio until the client shuts the session down.
/// `library`: standard-library directory for the model tier (hover,
/// definition, references, rename resolve against it when given).
pub fn run_stdio(library: Option<std::path::PathBuf>) -> Result<(), Error> {
    let (connection, io_threads) = Connection::stdio();
    run_with_library(connection, library)?;
    io_threads.join()?;
    Ok(())
}

/// Serve LSP over any transport (the test harness uses
/// `Connection::memory()`), without a standard library.
pub fn run(connection: Connection) -> Result<(), Error> {
    run_with_library(connection, None)
}

/// [`run`], resolving against a standard-library directory.
pub fn run_with_library(
    connection: Connection,
    library: Option<std::path::PathBuf>,
) -> Result<(), Error> {
    run_with_options(connection, library, std::time::Duration::from_millis(300))
}

/// [`run_with_library`] with a configurable workspace-tier debounce (the
/// test harness shortens it).
pub fn run_with_options(
    connection: Connection,
    library: Option<std::path::PathBuf>,
    debounce: std::time::Duration,
) -> Result<(), Error> {
    let (init_id, init_params) = connection.initialize_start()?;
    let init: InitializeParams = serde_json::from_value(init_params)?;
    let encoding = negotiate_encoding(&init);
    #[allow(deprecated)] // root_uri: universally sent, successor optional
    let root = init
        .workspace_folders
        .as_ref()
        .and_then(|f| f.first().map(|w| w.uri.clone()))
        .or_else(|| init.root_uri.clone())
        .as_ref()
        .and_then(worker::path_for_uri);
    let result = InitializeResult {
        capabilities: capabilities(encoding),
        server_info: Some(ServerInfo {
            name: "sysmlv2-lsp".to_string(),
            version: Some(env!("CARGO_PKG_VERSION").to_string()),
        }),
    };
    connection.initialize_finish(init_id, serde_json::to_value(result)?)?;
    let worker = worker::Worker::spawn(
        connection.sender.clone(),
        library.clone(),
        encoding,
        debounce,
    );
    let mut nav = nav::Nav::new(library, root.clone());
    nav.set_hide_redundant_value_hints(hide_redundant_value_hints(&init).unwrap_or(true));
    nav.set_infer_unit_types(infer_unit_types(&init).unwrap_or(true));
    nav.set_snippet_completions(snippet_completions(&init));
    Server {
        connection,
        encoding,
        docs: HashMap::new(),
        nav,
        worker,
        root,
    }
    .main_loop()
}

/// `initializationOptions.hideRedundantValueHints`: suppress
/// evaluated-value inlay hints that restate the declared expression
/// verbatim. `None` when the client sent no verdict (the default is
/// `true`).
pub(crate) fn hide_redundant_value_hints(init: &InitializeParams) -> Option<bool> {
    init.initialization_options
        .as_ref()
        .and_then(|o| o.get("hideRedundantValueHints"))
        .and_then(|v| v.as_bool())
}

/// `initializationOptions.inferUnitTypes`: accepting a unit completion
/// inside an untyped attribute's quantity bracket also declares the
/// type the unit determines. `None` when the client sent no verdict
/// (the default is `true`).
pub(crate) fn infer_unit_types(init: &InitializeParams) -> Option<bool> {
    init.initialization_options
        .as_ref()
        .and_then(|o| o.get("inferUnitTypes"))
        .and_then(|v| v.as_bool())
}

/// The client's `completionItem.snippetSupport` capability: whether
/// completion edits may carry snippet syntax (the `$0` cursor stop on
/// statement-repair suffixes). Absent means no.
pub(crate) fn snippet_completions(init: &InitializeParams) -> bool {
    init.capabilities
        .text_document
        .as_ref()
        .and_then(|t| t.completion.as_ref())
        .and_then(|c| c.completion_item.as_ref())
        .and_then(|i| i.snippet_support)
        .unwrap_or(false)
}

/// UTF-8 when the client lists it in `general.positionEncodings`
/// (LSP 3.17), else the mandatory UTF-16 default.
pub(crate) fn negotiate_encoding(init: &InitializeParams) -> Encoding {
    let offers_utf8 = init
        .capabilities
        .general
        .as_ref()
        .and_then(|g| g.position_encodings.as_ref())
        .is_some_and(|encs| encs.contains(&PositionEncodingKind::UTF8));
    if offers_utf8 {
        Encoding::Utf8
    } else {
        Encoding::Utf16
    }
}

pub(crate) fn capabilities(encoding: Encoding) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(match encoding {
            Encoding::Utf8 => PositionEncodingKind::UTF8,
            Encoding::Utf16 => PositionEncodingKind::UTF16,
        }),
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        document_formatting_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        code_action_provider: Some(lsp_types::CodeActionProviderCapability::Options(
            lsp_types::CodeActionOptions {
                code_action_kinds: Some(vec![
                    lsp_types::CodeActionKind::QUICKFIX,
                    lsp_types::CodeActionKind::SOURCE,
                    lsp_types::CodeActionKind::SOURCE_ORGANIZE_IMPORTS,
                    lsp_types::CodeActionKind::new("source.sortImports"),
                    lsp_types::CodeActionKind::REFACTOR_EXTRACT,
                    lsp_types::CodeActionKind::REFACTOR_INLINE,
                ]),
                ..Default::default()
            },
        )),
        completion_provider: Some(lsp_types::CompletionOptions {
            // `:` opens after a `::` qualifier, `.` after a feature
            // chain step (member completions).
            trigger_characters: Some(vec![":".to_string(), ".".to_string()]),
            ..Default::default()
        }),
        inlay_hint_provider: Some(OneOf::Left(true)),
        code_lens_provider: Some(lsp_types::CodeLensOptions {
            resolve_provider: Some(false),
        }),
        hover_provider: Some(lsp_types::HoverProviderCapability::Simple(true)),
        rename_provider: Some(OneOf::Left(true)),
        workspace_symbol_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(
            lsp_types::SemanticTokensOptions {
                legend: lsp_types::SemanticTokensLegend {
                    token_types: tokens::legend_types(),
                    token_modifiers: tokens::legend_modifiers(),
                },
                full: Some(lsp_types::SemanticTokensFullOptions::Bool(true)),
                range: None,
                work_done_progress_options: Default::default(),
            }
            .into(),
        ),
        ..Default::default()
    }
}

/// One open document: the full current text plus the client's version
/// counter (echoed back on diagnostics so stale publishes are discarded).
pub(crate) struct Document {
    pub(crate) text: String,
    pub(crate) version: i32,
}

pub(crate) struct Server {
    pub(crate) connection: Connection,
    pub(crate) encoding: Encoding,
    pub(crate) docs: HashMap<Uri, Document>,
    pub(crate) nav: nav::Nav,
    pub(crate) worker: worker::Worker,
    pub(crate) root: Option<std::path::PathBuf>,
}

impl Server {
    fn main_loop(mut self) -> Result<(), Error> {
        while let Ok(msg) = self.connection.receiver.recv() {
            match msg {
                Message::Request(req) => {
                    if self.connection.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    self.handle_request(req)?;
                }
                Message::Notification(n) => self.handle_notification(n)?,
                Message::Response(_) => {}
            }
        }
        Ok(())
    }

    pub(crate) fn handle_request(&mut self, req: Request) -> Result<(), Error> {
        let response = match req.method.as_str() {
            Formatting::METHOD => {
                let params: DocumentFormattingParams = serde_json::from_value(req.params)?;
                let (edits, refusal) = self.format(&params.text_document.uri);
                if let Some(message) = refusal {
                    // A silent no-op reads as "formatting is broken" —
                    // say why the document was left alone, and answer
                    // null (refused) rather than [] (nothing to do) so
                    // clients can tell the cases apart.
                    self.connection
                        .sender
                        .send(Message::Notification(Notification::new(
                            lsp_types::notification::ShowMessage::METHOD.to_string(),
                            lsp_types::ShowMessageParams {
                                typ: lsp_types::MessageType::WARNING,
                                message,
                            },
                        )))?;
                    Response::new_ok(req.id, serde_json::Value::Null)
                } else {
                    Response::new_ok(req.id, edits)
                }
            }
            DocumentSymbolRequest::METHOD => {
                let params: DocumentSymbolParams = serde_json::from_value(req.params)?;
                Response::new_ok(req.id, self.symbols(&params.text_document.uri))
            }
            SemanticTokensFullRequest::METHOD => {
                let params: lsp_types::SemanticTokensParams = serde_json::from_value(req.params)?;
                Response::new_ok(req.id, self.semantic_tokens(&params.text_document.uri))
            }
            GotoDefinition::METHOD => {
                let p: lsp_types::GotoDefinitionParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position_params;
                let loc = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav
                            .definition(&self.docs, &d.text_document.uri, o, self.encoding)
                    });
                Response::new_ok(req.id, loc.map(lsp_types::GotoDefinitionResponse::Scalar))
            }
            References::METHOD => {
                let p: lsp_types::ReferenceParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position;
                let locs = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav.references(
                            &self.docs,
                            &d.text_document.uri,
                            o,
                            p.context.include_declaration,
                            self.encoding,
                        )
                    });
                Response::new_ok(req.id, locs)
            }
            DocumentHighlightRequest::METHOD => {
                let p: lsp_types::DocumentHighlightParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position_params;
                let hl = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav
                            .references(&self.docs, &d.text_document.uri, o, true, self.encoding)
                            .map(|locs| nav::highlights_in(locs, &d.text_document.uri))
                    });
                Response::new_ok(req.id, hl)
            }
            HoverRequest::METHOD => {
                let p: lsp_types::HoverParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position_params;
                let hover = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav
                            .hover(&self.docs, &d.text_document.uri, o, self.encoding)
                            .map(|(value, range)| lsp_types::Hover {
                                contents: lsp_types::HoverContents::Markup(
                                    lsp_types::MarkupContent {
                                        kind: lsp_types::MarkupKind::Markdown,
                                        value,
                                    },
                                ),
                                range: Some(range),
                            })
                    });
                Response::new_ok(req.id, hover)
            }
            Rename::METHOD => {
                let p: lsp_types::RenameParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position;
                let result = match self.offset_of(&d.text_document.uri, d.position) {
                    Some(o) => self.nav.rename(
                        &self.docs,
                        &d.text_document.uri,
                        o,
                        &p.new_name,
                        self.encoding,
                    ),
                    None => Err("document is not open".to_string()),
                };
                match result {
                    Ok(edit) => {
                        // The cached session advanced past the client's
                        // text; resync via the client's didChange.
                        self.nav.invalidate();
                        Response::new_ok(req.id, Some(edit))
                    }
                    Err(msg) => {
                        self.nav.invalidate();
                        Response::new_err(req.id, ErrorCode::RequestFailed as i32, msg)
                    }
                }
            }
            Completion::METHOD => {
                let p: lsp_types::CompletionParams = serde_json::from_value(req.params)?;
                let d = &p.text_document_position;
                let offset = self.offset_of(&d.text_document.uri, d.position);
                let items =
                    self.nav
                        .completions(&self.docs, &d.text_document.uri, offset, self.encoding);
                Response::new_ok(req.id, Some(lsp_types::CompletionResponse::Array(items)))
            }
            InlayHintRequest::METHOD => {
                let p: lsp_types::InlayHintParams = serde_json::from_value(req.params)?;
                let hints = self
                    .nav
                    .inlay_hints(&self.docs, &p.text_document.uri, self.encoding);
                Response::new_ok(req.id, Some(hints))
            }
            CodeLensRequest::METHOD => {
                let p: lsp_types::CodeLensParams = serde_json::from_value(req.params)?;
                let lenses = self
                    .nav
                    .code_lenses(&self.docs, &p.text_document.uri, self.encoding);
                Response::new_ok(req.id, Some(lenses))
            }
            CodeActionRequest::METHOD => {
                let p: lsp_types::CodeActionParams = serde_json::from_value(req.params)?;
                let actions = self.code_actions(&p);
                Response::new_ok(req.id, Some(actions))
            }
            WorkspaceSymbolRequest::METHOD => {
                let p: lsp_types::WorkspaceSymbolParams = serde_json::from_value(req.params)?;
                let mut out = Vec::new();
                for (uri, doc) in &self.docs {
                    let parse = match dialect_of(uri) {
                        Dialect::Kerml => parse_kerml_source(&doc.text),
                        Dialect::Sysml => parse_source(&doc.text),
                    };
                    let mapper = Mapper::new(&doc.text, self.encoding);
                    let symbols = outline::document_symbols(&parse.unit, &doc.text, &mapper);
                    nav::flatten_symbols(&symbols, uri, &p.query, &mut out);
                }
                Response::new_ok(req.id, Some(out))
            }
            _ => Response::new_err(
                req.id,
                ErrorCode::MethodNotFound as i32,
                format!("unsupported method: {}", req.method),
            ),
        };
        self.connection.sender.send(Message::Response(response))?;
        Ok(())
    }

    pub(crate) fn handle_notification(&mut self, n: Notification) -> Result<(), Error> {
        match n.method.as_str() {
            DidOpenTextDocument::METHOD => {
                let p: DidOpenTextDocumentParams = serde_json::from_value(n.params)?;
                let doc = Document {
                    text: p.text_document.text,
                    version: p.text_document.version,
                };
                self.publish_diagnostics(&p.text_document.uri, &doc)?;
                self.docs.insert(p.text_document.uri, doc);
                self.schedule_workspace();
            }
            DidChangeTextDocument::METHOD => {
                let p: DidChangeTextDocumentParams = serde_json::from_value(n.params)?;
                // Full sync: the last change carries the whole new text.
                let Some(change) = p.content_changes.into_iter().last() else {
                    return Ok(());
                };
                let doc = Document {
                    text: change.text,
                    version: p.text_document.version,
                };
                self.publish_diagnostics(&p.text_document.uri, &doc)?;
                self.docs.insert(p.text_document.uri, doc);
                self.schedule_workspace();
            }
            DidCloseTextDocument::METHOD => {
                let p: DidCloseTextDocumentParams = serde_json::from_value(n.params)?;
                self.docs.remove(&p.text_document.uri);
                // Clear the document's diagnostics from the editor.
                self.send_diagnostics(&p.text_document.uri, Vec::new(), None)?;
                self.schedule_workspace();
            }
            _ => {} // initialized, $/cancelRequest, …: nothing to do
        }
        Ok(())
    }

    /// Syntax-tier diagnostics: parse + body-context validation,
    /// no model, no cross-file coupling.
    fn publish_diagnostics(&self, uri: &Uri, doc: &Document) -> Result<(), Error> {
        let parse = match dialect_of(uri) {
            Dialect::Kerml => parse_kerml_source(&doc.text),
            Dialect::Sysml => parse_source(&doc.text),
        };
        let mapper = Mapper::new(&doc.text, self.encoding);
        let diagnostics = parse
            .diagnostics
            .iter()
            .chain(check::validate(&parse.unit).iter())
            .map(|d| lsp_types::Diagnostic {
                range: mapper.range(d.span),
                severity: Some(match d.severity {
                    sysmlv2_parser::diag::Severity::Error => DiagnosticSeverity::ERROR,
                    sysmlv2_parser::diag::Severity::Warning => DiagnosticSeverity::WARNING,
                }),
                source: Some("sysmlv2".to_string()),
                message: d.message.clone(),
                ..Default::default()
            })
            .collect();
        self.send_diagnostics(uri, diagnostics, Some(doc.version))
    }

    fn send_diagnostics(
        &self,
        uri: &Uri,
        diagnostics: Vec<lsp_types::Diagnostic>,
        version: Option<i32>,
    ) -> Result<(), Error> {
        let params = PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics,
            version,
        };
        self.connection
            .sender
            .send(Message::Notification(Notification::new(
                PublishDiagnostics::METHOD.to_string(),
                params,
            )))?;
        Ok(())
    }

    /// Document outline: the syntax AST as nested symbols —
    /// works on broken documents too (the parse tree is partial, never
    /// absent), which is exactly what keeps the Outline view alive while
    /// typing.
    fn symbols(&self, uri: &Uri) -> Option<DocumentSymbolResponse> {
        let doc = self.docs.get(uri)?;
        let parse = match dialect_of(uri) {
            Dialect::Kerml => parse_kerml_source(&doc.text),
            Dialect::Sysml => parse_source(&doc.text),
        };
        let mapper = Mapper::new(&doc.text, self.encoding);
        Some(DocumentSymbolResponse::Nested(outline::document_symbols(
            &parse.unit,
            &doc.text,
            &mapper,
        )))
    }

    /// Hand the workspace tier a fresh snapshot of the open documents.
    fn schedule_workspace(&self) {
        self.worker.schedule(worker::Job {
            docs: self
                .docs
                .iter()
                .map(|(u, d)| (u.to_string(), d.version, d.text.clone()))
                .collect(),
            root: self.root.clone(),
        });
    }

    /// Code actions: quickfixes riding published diagnostics
    /// (remove an unused import — the diagnostic's range is the removal
    /// span) plus the explicit source action collapsing qualified names
    /// to their minimal spelling (only offered when the
    /// client asks for source actions, since it costs a model pass).
    fn code_actions(
        &mut self,
        params: &lsp_types::CodeActionParams,
    ) -> Vec<lsp_types::CodeActionOrCommand> {
        let uri = &params.text_document.uri;
        let mut out = Vec::new();
        for d in &params.context.diagnostics {
            if d.message == worker::UNUSED_IMPORT_MESSAGE {
                let mut changes = HashMap::new();
                changes.insert(
                    uri.clone(),
                    vec![TextEdit {
                        range: d.range,
                        new_text: String::new(),
                    }],
                );
                out.push(lsp_types::CodeActionOrCommand::CodeAction(
                    lsp_types::CodeAction {
                        title: "Remove unused import".to_string(),
                        kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                        diagnostics: Some(vec![d.clone()]),
                        edit: Some(lsp_types::WorkspaceEdit {
                            changes: Some(changes),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ));
            }
            // Unresolved references: intent-dependent suggestions —
            // near-miss respellings ("Did you mean …?") and, when the
            // qualifier names a workspace enum, declaring the missing
            // literal. The name is re-read from the document at the
            // diagnostic's start, so clients with approximate ranges
            // still get exact edits.
            if d.message.starts_with("unresolved reference `") {
                if let Some(offset) = self.offset_of(uri, d.range.start) {
                    let fixes =
                        self.nav
                            .unresolved_reference_fixes(&self.docs, uri, offset, self.encoding);
                    for (title, target_uri, edit, preferred) in fixes {
                        let mut changes = HashMap::new();
                        changes.insert(target_uri, vec![edit]);
                        out.push(lsp_types::CodeActionOrCommand::CodeAction(
                            lsp_types::CodeAction {
                                title,
                                kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                                diagnostics: Some(vec![d.clone()]),
                                is_preferred: preferred.then_some(true),
                                edit: Some(lsp_types::WorkspaceEdit {
                                    changes: Some(changes),
                                    ..Default::default()
                                }),
                                ..Default::default()
                            },
                        ));
                    }
                }
            }
            // The mandatory-visibility finding: offer each legal
            // keyword, `private` first (the conservative default —
            // public re-exports).
            if d.message
                .starts_with("an import must declare an explicit visibility")
            {
                for vis in ["private", "public", "protected"] {
                    let mut changes = HashMap::new();
                    changes.insert(
                        uri.clone(),
                        vec![TextEdit {
                            range: lsp_types::Range {
                                start: d.range.start,
                                end: d.range.start,
                            },
                            new_text: format!("{vis} "),
                        }],
                    );
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title: format!("Make the import {vis}"),
                            kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                            diagnostics: Some(vec![d.clone()]),
                            is_preferred: (vis == "private").then_some(true),
                            edit: Some(lsp_types::WorkspaceEdit {
                                changes: Some(changes),
                                ..Default::default()
                            }),
                            ..Default::default()
                        },
                    ));
                }
            }
        }
        // Kind-filter semantics: an action is requested when an `only`
        // entry equals its kind or is a dot-separated ancestor of it
        // (`source` requests `source.organizeImports`; the reverse does
        // not hold).
        let requested = |kind: &str| -> bool {
            params.context.only.as_ref().is_some_and(|ks| {
                ks.iter().any(|k| {
                    let k = k.as_str();
                    kind == k
                        || (kind.starts_with(k) && kind.as_bytes().get(k.len()) == Some(&b'.'))
                })
            })
        };

        // "Optimize imports" (source.organizeImports): drop the unused
        // private imports, keep everything else — order included.
        if requested("source.organizeImports") {
            if let Some(edits) = self.nav.optimize_imports(&self.docs, uri, self.encoding) {
                if !edits.is_empty() {
                    let mut changes = HashMap::new();
                    changes.insert(uri.clone(), edits);
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title: "Optimize imports".to_string(),
                            kind: Some(lsp_types::CodeActionKind::SOURCE_ORGANIZE_IMPORTS),
                            edit: Some(lsp_types::WorkspaceEdit {
                                changes: Some(changes),
                                ..Default::default()
                            }),
                            ..Default::default()
                        },
                    ));
                }
            }
        }

        // "Sort imports" (source.sortImports): alphabetize contiguous
        // import runs; a syntax-tier reshuffle, no model pass.
        if requested("source.sortImports") {
            if let Some(doc) = self.docs.get(uri) {
                let edits = nav::sort_import_edits(
                    &doc.text,
                    matches!(dialect_of(uri), Dialect::Kerml),
                    self.encoding,
                );
                if !edits.is_empty() {
                    let mut changes = HashMap::new();
                    changes.insert(uri.clone(), edits);
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title: "Sort imports".to_string(),
                            kind: Some(lsp_types::CodeActionKind::new("source.sortImports")),
                            edit: Some(lsp_types::WorkspaceEdit {
                                changes: Some(changes),
                                ..Default::default()
                            }),
                            ..Default::default()
                        },
                    ));
                }
            }
        }

        // Refactorings: offered on the unfiltered request (the
        // lightbulb / context menu sends no `only`) and under `refactor`
        // kind filters — the same ancestor semantics as the source
        // actions, so `refactor` requests both members of the pair.
        // Eligibility gates run first and are cheap; the dry-run that
        // computes the edit only happens for admitted cursors, and it
        // leaves the session untouched (no invalidation).
        let unfiltered = params.context.only.is_none();
        if unfiltered || requested("refactor.extract") {
            if let Some(offset) = self.offset_of(uri, params.range.start) {
                if let Some((title, edit)) =
                    self.nav
                        .refactor_extract_action(&self.docs, uri, offset, self.encoding)
                {
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title,
                            kind: Some(lsp_types::CodeActionKind::REFACTOR_EXTRACT),
                            edit: Some(edit),
                            ..Default::default()
                        },
                    ));
                }
            }
        }
        if unfiltered || requested("refactor.inline") {
            if let Some(offset) = self.offset_of(uri, params.range.start) {
                if let Some((title, edit)) =
                    self.nav
                        .refactor_inline_action(&self.docs, uri, offset, self.encoding)
                {
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title,
                            kind: Some(lsp_types::CodeActionKind::REFACTOR_INLINE),
                            edit: Some(edit),
                            ..Default::default()
                        },
                    ));
                }
            }
        }

        let wants_source = params
            .context
            .only
            .as_ref()
            .is_some_and(|kinds| kinds.iter().any(|k| k.as_str().starts_with("source")));
        if wants_source {
            if let Ok(edit) = self.nav.minimize(&self.docs, self.encoding) {
                self.nav.invalidate();
                if edit.changes.as_ref().is_some_and(|c| !c.is_empty()) {
                    out.push(lsp_types::CodeActionOrCommand::CodeAction(
                        lsp_types::CodeAction {
                            title: "Minimize qualified names".to_string(),
                            kind: Some(lsp_types::CodeActionKind::SOURCE),
                            edit: Some(edit),
                            ..Default::default()
                        },
                    ));
                }
            } else {
                self.nav.invalidate();
            }
        }
        out
    }

    /// A position's byte offset in an open document.
    fn offset_of(&self, uri: &Uri, pos: lsp_types::Position) -> Option<u32> {
        let doc = self.docs.get(uri)?;
        Some(nav::offset_in(&doc.text, pos, self.encoding))
    }

    /// Semantic tokens: exact dialect-aware highlighting — see
    /// `tokens` for the classification scheme.
    fn semantic_tokens(&self, uri: &Uri) -> Option<lsp_types::SemanticTokensResult> {
        let doc = self.docs.get(uri)?;
        let parse = match dialect_of(uri) {
            Dialect::Kerml => parse_kerml_source(&doc.text),
            Dialect::Sysml => parse_source(&doc.text),
        };
        let toks = tokens::lex(&doc.text);
        let classified = tokens::classify(&parse.unit, &doc.text, &toks);
        let mapper = Mapper::new(&doc.text, self.encoding);
        Some(lsp_types::SemanticTokensResult::Tokens(
            lsp_types::SemanticTokens {
                result_id: None,
                data: tokens::encode(classified, &doc.text, &mapper),
            },
        ))
    }

    /// Whole-document formatting via the gated formatter. A document that
    /// does not parse is never touched (a formatter must not guess at
    /// broken input) — the second return explains the refusal, for the
    /// caller to surface; an already-formatted document returns an empty
    /// edit list. Formatter style is fixed (4-space indent) — the
    /// request's `FormattingOptions` are deliberately not consulted.
    fn format(&self, uri: &Uri) -> (Vec<TextEdit>, Option<String>) {
        let Some(doc) = self.docs.get(uri) else {
            return (Vec::new(), None);
        };
        // Project style: the `multiline-conditions` rule's `min` option
        // in the workspace's sysmlint.json carries the chain threshold
        // (0 = keep chains inline); absent or unreadable config keeps
        // the formatter's default.
        let chain_min = self
            .root
            .as_ref()
            .and_then(|r| std::fs::read_to_string(r.join("sysmlint.json")).ok())
            .and_then(|text| sysmlv2_lint::Config::from_json(&text).ok())
            .map(|c| c.format_chain_min())
            .unwrap_or(Some(sysmlv2_parser::print::FORMAT_CHAIN_MIN));
        let opts = sysmlv2_parser::print::PrintOptions {
            multiline_chains: chain_min,
            ..Default::default()
        };
        match sysmlv2_parser::print::format_source_opts(&doc.text, dialect_of(uri), opts) {
            Err(diags) => {
                let n = diags.len();
                (
                    Vec::new(),
                    Some(format!(
                        "cannot format: the document has {n} syntax error{} — fix {} first",
                        if n == 1 { "" } else { "s" },
                        if n == 1 { "it" } else { "them" },
                    )),
                )
            }
            Ok(formatted) if formatted == doc.text => (Vec::new(), None),
            Ok(formatted) => {
                let mapper = Mapper::new(&doc.text, self.encoding);
                (
                    vec![TextEdit {
                        range: mapper.full_range(),
                        new_text: formatted,
                    }],
                    None,
                )
            }
        }
    }
}

/// Dialect by file extension: `.kerml` is KerML, everything else SysML.
fn dialect_of(uri: &Uri) -> Dialect {
    if uri.path().as_str().ends_with(".kerml") {
        Dialect::Kerml
    } else {
        Dialect::Sysml
    }
}
