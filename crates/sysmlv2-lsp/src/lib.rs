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

// Every span in the toolkit is a `u32` byte range, so document
// offsets and lengths cross between `usize` and `u32` constantly; the
// conversion goes through `position::offset32`, which says so once and
// refuses rather than wrapping.
#![warn(clippy::cast_possible_truncation)]

use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
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
use serde::de::DeserializeOwned;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::check;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

mod autofix;
mod autoimport;
// lsp-types mandates `Uri` map keys (`WorkspaceEdit::changes`, the
// document store), and `Uri` has interior mutability; nothing here
// mutates one while it is a key.
#[allow(clippy::mutable_key_type)]
mod nav;
mod outline;
mod position;
mod push;
pub mod tokens;
mod worker;

pub use outline::{document_symbols, spell_name, spell_symbols};
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
///
/// The syntax tier parses on the loop's own thread, and the parser's
/// nesting bound assumes a stack sized for it, which a host's thread is
/// not: the loop runs on a thread that reserves one
/// ([`sysmlv2_parser::parser::on_parsing_stack`]). The workspace tier
/// reserves the same size on the worker it spawns.
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
    let client = connection.sender.clone();
    let server = Server {
        connection,
        encoding,
        docs: BTreeMap::new(),
        nav,
        worker,
        root,
        reported: HashSet::new(),
    };
    sysmlv2_parser::parser::on_parsing_stack(
        "sysmlv2-lsp",
        |err| say_the_stack_was_refused(&client, err),
        move || server.main_loop(),
    )
}

/// Tell the client's log that the loop's stack could not be reserved.
///
/// The session still serves: the loop runs on the thread the host started
/// it on, which holds a fraction of the nesting the parser accepts. What
/// it cannot survive is a document nested past that — the descent runs
/// the stack out, and the overflow ends the whole server, with no
/// diagnostic, no unwind and no session left to show a popup in. So this
/// goes to the log, where it is there to be read afterwards.
fn say_the_stack_was_refused(client: &crossbeam_channel::Sender<Message>, err: &std::io::Error) {
    let _ = client.send(Message::Notification(Notification::new(
        lsp_types::notification::LogMessage::METHOD.to_string(),
        lsp_types::LogMessageParams {
            typ: lsp_types::MessageType::ERROR,
            message: format!(
                "could not reserve the stack the parser's nesting bound assumes: {err}. \
                 A deeply nested document may end this server without a diagnostic."
            ),
        },
    )));
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
                    lsp_types::CodeActionKind::SOURCE_FIX_ALL,
                    lsp_types::CodeActionKind::SOURCE_ORGANIZE_IMPORTS,
                    lsp_types::CodeActionKind::new("source.sortImports"),
                    lsp_types::CodeActionKind::REFACTOR_EXTRACT,
                    lsp_types::CodeActionKind::REFACTOR_INLINE,
                    lsp_types::CodeActionKind::new("refactor.move"),
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
    /// Shared: a document's text is snapshotted into every workspace
    /// job and out of the document store on most requests (to escape
    /// the borrow the model build takes), which on a large unit made
    /// per-keystroke copies of the whole file.
    pub(crate) text: std::sync::Arc<str>,
    pub(crate) version: i32,
}

/// `sysmlv2/splitPlan`: plan a package's split into one unit per nested
/// package (the file tree, collisions and renames), for an editor's
/// wizard. Params: [`SplitRequestParams`]; result: the plan.
pub const SPLIT_PLAN_METHOD: &str = "sysmlv2/splitPlan";
/// `sysmlv2/split`: the same plan with its annotated workspace edit
/// (file creations and the root rewrite under one change annotation
/// naming the split). Refusals answer `RequestFailed` with the reason.
pub const SPLIT_METHOD: &str = "sysmlv2/split";

/// Parameters of [`SPLIT_PLAN_METHOD`] and [`SPLIT_METHOD`].
#[derive(serde::Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct SplitRequestParams {
    /// The open document `position` points into; unused with `package`.
    #[serde(default)]
    pub text_document: Option<lsp_types::TextDocumentIdentifier>,
    /// The package under this position's name.
    #[serde(default)]
    pub position: Option<lsp_types::Position>,
    /// The package by qualified name (quoted segments allowed); takes
    /// precedence over `position`.
    #[serde(default)]
    pub package: Option<String>,
    #[serde(default)]
    pub naming: SplitNamingParam,
    /// The uri prefix the new units are named under; by default the
    /// root unit's uri without its extension.
    #[serde(default)]
    pub directory: Option<String>,
}

/// File naming of a split request.
#[derive(serde::Deserialize, Debug, Clone, Copy, Default, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum SplitNamingParam {
    /// The package name as written.
    #[default]
    Keep,
    /// Letters, digits, `.`, `_` and `-` only.
    Slug,
}

enum SplitRefusal {
    /// Malformed or incomplete parameters.
    Params(String),
    /// A well-formed request the model refuses (not a package, nothing
    /// nested, a failed dry run).
    Refused(String),
}

pub(crate) struct Server {
    pub(crate) connection: Connection,
    pub(crate) encoding: Encoding,
    /// Ordered, so the unit order every tier derives from it is the
    /// same run to run: unit indexes, the resolver's "first declaration
    /// wins" tie-break on an ambiguity, and the order of workspace
    /// symbols all follow it, and a hash order made them drift between
    /// the background worker and navigation on the same model.
    pub(crate) docs: BTreeMap<Uri, Document>,
    pub(crate) nav: nav::Nav,
    pub(crate) worker: worker::Worker,
    pub(crate) root: Option<std::path::PathBuf>,
    /// Client-facing failure messages already sent, so a failure that
    /// recurs per keystroke is announced once (see
    /// [`Server::show_message_once`]).
    pub(crate) reported: HashSet<String>,
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

    /// Answer one request. A request the server cannot serve as asked
    /// — unknown method, malformed parameters, an answer the model
    /// panicked computing — is answered with the matching error; only
    /// a closed transport is an `Err` here.
    pub(crate) fn handle_request(&mut self, req: Request) -> Result<(), Error> {
        let (id, method) = (req.id.clone(), req.method.clone());
        // A panic deep in the model, evaluator or solver would
        // otherwise take the whole session down with one request. The
        // server's own state may be part-updated afterwards, so the
        // caveat `AssertUnwindSafe` waives is real — but a stale cache
        // an edit invalidates beats a dead editor.
        let response = match catch_unwind(AssertUnwindSafe(|| self.respond(req))) {
            Ok(Ok(response) | Err(response)) => response,
            Err(payload) => {
                let reason = panic_reason(payload.as_ref());
                self.show_message_once(
                    lsp_types::MessageType::ERROR,
                    format!("{method} failed: {reason}"),
                );
                Response::new_err(
                    id,
                    ErrorCode::InternalError as i32,
                    format!("{method}: {reason}"),
                )
            }
        };
        self.report_nav_failures();
        self.connection.sender.send(Message::Response(response))?;
        Ok(())
    }

    /// The response to one request. `Err` carries the response to a
    /// request whose parameters did not deserialize ([`cast`]'s
    /// `InvalidParams`), so a handler bails with `?` and the request
    /// is still answered.
    fn respond(&mut self, req: Request) -> Result<Response, Response> {
        Ok(match req.method.as_str() {
            Formatting::METHOD => {
                let (id, params): (_, DocumentFormattingParams) = cast(req)?;
                let (edits, refusal) = self.format(&params.text_document.uri);
                if let Some(message) = refusal {
                    // A silent no-op reads as "formatting is broken" —
                    // say why the document was left alone, and answer
                    // null (refused) rather than [] (nothing to do) so
                    // clients can tell the cases apart.
                    self.show_message(lsp_types::MessageType::WARNING, message);
                    Response::new_ok(id, serde_json::Value::Null)
                } else {
                    Response::new_ok(id, edits)
                }
            }
            DocumentSymbolRequest::METHOD => {
                let (id, params): (_, DocumentSymbolParams) = cast(req)?;
                Response::new_ok(id, self.symbols(&params.text_document.uri))
            }
            SemanticTokensFullRequest::METHOD => {
                let (id, params): (_, lsp_types::SemanticTokensParams) = cast(req)?;
                Response::new_ok(id, self.semantic_tokens(&params.text_document.uri))
            }
            GotoDefinition::METHOD => {
                let (id, p): (_, lsp_types::GotoDefinitionParams) = cast(req)?;
                let d = &p.text_document_position_params;
                let loc = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav
                            .definition(&self.docs, &d.text_document.uri, o, self.encoding)
                    });
                Response::new_ok(id, loc.map(lsp_types::GotoDefinitionResponse::Scalar))
            }
            References::METHOD => {
                let (id, p): (_, lsp_types::ReferenceParams) = cast(req)?;
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
                Response::new_ok(id, locs)
            }
            DocumentHighlightRequest::METHOD => {
                let (id, p): (_, lsp_types::DocumentHighlightParams) = cast(req)?;
                let d = &p.text_document_position_params;
                let hl = self
                    .offset_of(&d.text_document.uri, d.position)
                    .and_then(|o| {
                        self.nav
                            .references(&self.docs, &d.text_document.uri, o, true, self.encoding)
                            .map(|locs| nav::highlights_in(locs, &d.text_document.uri))
                    });
                Response::new_ok(id, hl)
            }
            HoverRequest::METHOD => {
                let (id, p): (_, lsp_types::HoverParams) = cast(req)?;
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
                Response::new_ok(id, hover)
            }
            Rename::METHOD => {
                let (id, p): (_, lsp_types::RenameParams) = cast(req)?;
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
                        Response::new_ok(id, Some(edit))
                    }
                    Err(msg) => {
                        self.nav.invalidate();
                        Response::new_err(id, ErrorCode::RequestFailed as i32, msg)
                    }
                }
            }
            Completion::METHOD => {
                let (id, p): (_, lsp_types::CompletionParams) = cast(req)?;
                let d = &p.text_document_position;
                let offset = self.offset_of(&d.text_document.uri, d.position);
                let items =
                    self.nav
                        .completions(&self.docs, &d.text_document.uri, offset, self.encoding);
                Response::new_ok(id, Some(lsp_types::CompletionResponse::Array(items)))
            }
            InlayHintRequest::METHOD => {
                let (id, p): (_, lsp_types::InlayHintParams) = cast(req)?;
                let hints = self
                    .nav
                    .inlay_hints(&self.docs, &p.text_document.uri, self.encoding);
                Response::new_ok(id, Some(hints))
            }
            CodeLensRequest::METHOD => {
                let (id, p): (_, lsp_types::CodeLensParams) = cast(req)?;
                let lenses = self
                    .nav
                    .code_lenses(&self.docs, &p.text_document.uri, self.encoding);
                Response::new_ok(id, Some(lenses))
            }
            CodeActionRequest::METHOD => {
                let (id, p): (_, lsp_types::CodeActionParams) = cast(req)?;
                let actions = self.code_actions(&p);
                Response::new_ok(id, Some(actions))
            }
            WorkspaceSymbolRequest::METHOD => {
                let (id, p): (_, lsp_types::WorkspaceSymbolParams) = cast(req)?;
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
                Response::new_ok(id, Some(out))
            }
            SPLIT_PLAN_METHOD | SPLIT_METHOD => {
                let with_edit = req.method == SPLIT_METHOD;
                let (id, p): (_, SplitRequestParams) = cast(req)?;
                match self.split_request(p, with_edit) {
                    Ok(v) => Response::new_ok(id, v),
                    Err(SplitRefusal::Params(m)) => {
                        Response::new_err(id, ErrorCode::InvalidParams as i32, m)
                    }
                    Err(SplitRefusal::Refused(m)) => {
                        Response::new_err(id, ErrorCode::RequestFailed as i32, m)
                    }
                }
            }
            #[cfg(test)]
            PANIC_METHOD => panic!("{PANIC_REASON}"),
            _ => Response::new_err(
                req.id,
                ErrorCode::MethodNotFound as i32,
                format!("unsupported method: {}", req.method),
            ),
        })
    }

    /// Handle one notification. A malformed one — or one whose
    /// handling panics — is reported and dropped: notifications have
    /// no reply to carry the error, and one bad message must not end
    /// the session.
    pub(crate) fn handle_notification(&mut self, n: Notification) -> Result<(), Error> {
        let method = n.method.clone();
        match catch_unwind(AssertUnwindSafe(|| self.dispatch_notification(n))) {
            Ok(result) => result,
            Err(payload) => {
                let reason = panic_reason(payload.as_ref());
                self.show_message_once(
                    lsp_types::MessageType::ERROR,
                    format!("{method} failed: {reason}"),
                );
                Ok(())
            }
        }
    }

    fn dispatch_notification(&mut self, n: Notification) -> Result<(), Error> {
        match n.method.as_str() {
            DidOpenTextDocument::METHOD => {
                let Some(p): Option<DidOpenTextDocumentParams> = self.notification_params(n) else {
                    return Ok(());
                };
                let doc = Document {
                    text: p.text_document.text.into(),
                    version: p.text_document.version,
                };
                self.publish_diagnostics(&p.text_document.uri, &doc)?;
                self.docs.insert(p.text_document.uri, doc);
                self.schedule_workspace();
            }
            DidChangeTextDocument::METHOD => {
                let Some(p): Option<DidChangeTextDocumentParams> = self.notification_params(n)
                else {
                    return Ok(());
                };
                // Full sync: the last change carries the whole new text.
                let Some(change) = p.content_changes.into_iter().last() else {
                    return Ok(());
                };
                let doc = Document {
                    text: change.text.into(),
                    version: p.text_document.version,
                };
                self.publish_diagnostics(&p.text_document.uri, &doc)?;
                self.docs.insert(p.text_document.uri, doc);
                self.schedule_workspace();
            }
            DidCloseTextDocument::METHOD => {
                let Some(p): Option<DidCloseTextDocumentParams> = self.notification_params(n)
                else {
                    return Ok(());
                };
                self.docs.remove(&p.text_document.uri);
                // Clear the document's diagnostics from the editor.
                self.send_diagnostics(&p.text_document.uri, Vec::new(), None)?;
                self.schedule_workspace();
            }
            #[cfg(test)]
            PANIC_METHOD => panic!("{PANIC_REASON}"),
            _ => {} // initialized, $/cancelRequest, …: nothing to do
        }
        Ok(())
    }

    /// A notification's parameters; a malformed notification logs the
    /// problem to the client and yields `None`.
    fn notification_params<P: DeserializeOwned>(&self, n: Notification) -> Option<P> {
        match serde_json::from_value(n.params) {
            Ok(p) => Some(p),
            Err(e) => {
                self.log_message(
                    lsp_types::MessageType::WARNING,
                    format!("{}: invalid params: {e}", n.method),
                );
                None
            }
        }
    }

    /// Pass on what navigation could not do and had no channel of its
    /// own to say — an unreadable library leaves hover, definition,
    /// references and rename answering nothing at all.
    fn report_nav_failures(&mut self) {
        for report in self.nav.take_reports() {
            // What the user has to act on is an error; the rest is
            // background for whoever reads the log.
            if report.show {
                self.show_message_once(lsp_types::MessageType::ERROR, report.message);
            } else {
                self.log_message_once(lsp_types::MessageType::WARNING, report.message);
            }
        }
    }

    /// [`Self::log_message`] the first time this exact message comes
    /// up; see [`Self::show_message_once`].
    fn log_message_once(&mut self, typ: lsp_types::MessageType, message: String) {
        if self.reported.insert(message.clone()) {
            self.log_message(typ, message);
        }
    }

    /// [`Self::show_message`] the first time this exact message comes
    /// up. A failure that recurs — a request that panics on every
    /// hover, a library that stays unreadable — would otherwise put a
    /// popup on screen per keystroke.
    fn show_message_once(&mut self, typ: lsp_types::MessageType, message: String) {
        if self.reported.insert(message.clone()) {
            self.show_message(typ, message);
        }
    }

    /// `window/showMessage` to the client. A closed transport is not
    /// reported here: the loop ends at its next receive.
    fn show_message(&self, typ: lsp_types::MessageType, message: String) {
        let _ = self
            .connection
            .sender
            .send(Message::Notification(Notification::new(
                lsp_types::notification::ShowMessage::METHOD.to_string(),
                lsp_types::ShowMessageParams { typ, message },
            )));
    }

    /// `window/logMessage` to the client (its output channel).
    fn log_message(&self, typ: lsp_types::MessageType, message: String) {
        let _ = self
            .connection
            .sender
            .send(Message::Notification(Notification::new(
                lsp_types::notification::LogMessage::METHOD.to_string(),
                lsp_types::LogMessageParams { typ, message },
            )));
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
        let mut symbols = outline::document_symbols(&parse.unit, &doc.text, &mapper);
        outline::spell_symbols(&mut symbols);
        Some(DocumentSymbolResponse::Nested(symbols))
    }

    /// Hand the workspace tier a fresh snapshot of the open documents.
    fn schedule_workspace(&self) {
        // By uri, the order navigation assembles its own sources in:
        // the two tiers answer over the same model, and a unit order
        // that differed between them would decide an ambiguity one way
        // in a diagnostic and the other way in a definition.
        let mut docs: Vec<(String, i32, std::sync::Arc<str>)> = self
            .docs
            .iter()
            .map(|(u, d)| (u.to_string(), d.version, d.text.clone()))
            .collect();
        docs.sort_by(|a, b| a.0.cmp(&b.0));
        self.worker.schedule(worker::Job {
            docs,
            root: self.root.clone(),
        });
    }

    /// Code actions: one provider per kind, in the order a client
    /// renders them — the quickfixes riding published diagnostics
    /// first (each provider looks at the diagnostics it knows), then
    /// the lint's fixes, the import source actions, the refactorings,
    /// and last the source actions that cost a committing model pass.
    fn code_actions(
        &mut self,
        params: &lsp_types::CodeActionParams,
    ) -> Vec<lsp_types::CodeActionOrCommand> {
        let uri = &params.text_document.uri;
        let mut out = Vec::new();
        for d in &params.context.diagnostics {
            self.unused_import_fix(uri, d, &mut out);
            self.unresolved_reference_fixes(uri, d, &mut out);
            self.import_visibility_fixes(uri, d, &mut out);
        }
        self.lint_fix_actions(params, &mut out);
        if requested(params, "source.organizeImports") {
            self.optimize_imports_action(uri, &mut out);
        }
        if requested(params, "source.sortImports") {
            self.sort_imports_action(uri, &mut out);
        }
        self.refactor_actions(params, &mut out);
        // Minimizing qualified names is a committing model pass: only an
        // explicit "source" request runs it, never a `source.fixAll`
        // on-save sweep (which would also discard the session and the
        // lint cache).
        if requested(params, "source") {
            self.minimize_names_action(&mut out);
        }
        out
    }

    /// The unused-private-import quickfix riding its own diagnostic —
    /// the diagnostic's range is the removal span.
    fn unused_import_fix(
        &self,
        uri: &Uri,
        d: &lsp_types::Diagnostic,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        if d.message != worker::UNUSED_IMPORT_MESSAGE {
            return;
        }
        out.push(quick_fix(
            "Remove unused import".to_string(),
            d,
            one_file_edit(
                uri,
                vec![TextEdit {
                    range: d.range,
                    new_text: String::new(),
                }],
            ),
            false,
        ));
    }

    /// Unresolved references: intent-dependent suggestions — near-miss
    /// respellings ("Did you mean …?") and, when the qualifier names a
    /// workspace enum, declaring the missing literal. The name is
    /// re-read from the document at the diagnostic's start, so clients
    /// with approximate ranges still get exact edits.
    #[allow(clippy::mutable_key_type)] // see the note on `mod nav`
    fn unresolved_reference_fixes(
        &mut self,
        uri: &Uri,
        d: &lsp_types::Diagnostic,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        if !d.message.starts_with("unresolved reference `") {
            return;
        }
        let Some(offset) = self.offset_of(uri, d.range.start) else {
            return;
        };
        let fixes = self
            .nav
            .unresolved_reference_fixes(&self.docs, uri, offset, self.encoding);
        for (title, target_uri, edit, preferred) in fixes {
            let mut changes = HashMap::new();
            changes.insert(target_uri, vec![edit]);
            out.push(quick_fix(
                title,
                d,
                lsp_types::WorkspaceEdit {
                    changes: Some(changes),
                    ..Default::default()
                },
                preferred,
            ));
        }
    }

    /// The mandatory-visibility finding: one action per legal keyword.
    /// The keyword the import's dependents require leads (computed from
    /// the reference sites that resolve through it); without a model,
    /// `private` — the conservative default, since public re-exports.
    fn import_visibility_fixes(
        &mut self,
        uri: &Uri,
        d: &lsp_types::Diagnostic,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        if !d
            .message
            .starts_with("an import must declare an explicit visibility")
        {
            return;
        }
        let advice = self
            .offset_of(uri, d.range.start)
            .and_then(|offset| self.nav.import_visibility_advice(&self.docs, uri, offset));
        let recommended = advice.as_ref().map_or("private", |a| a.recommended);
        let mut keywords = vec![recommended];
        keywords.extend(
            ["private", "public", "protected"]
                .into_iter()
                .filter(|k| *k != recommended),
        );
        for vis in keywords {
            let edits = vec![TextEdit {
                range: lsp_types::Range {
                    start: d.range.start,
                    end: d.range.start,
                },
                new_text: format!("{vis} "),
            }];
            let title = match &advice {
                Some(a) if vis == a.recommended && a.outside_sites.is_empty() => {
                    format!("Make the import `{vis}` (nothing outside uses it)")
                }
                Some(a) if vis == a.recommended => format!(
                    "Make the import `{vis}` ({} reference(s) beyond the importing \
                     namespace resolve through it)",
                    a.outside_sites.len()
                ),
                _ => format!("Make the import `{vis}`"),
            };
            out.push(quick_fix(
                title,
                d,
                one_file_edit(uri, edits),
                vis == recommended,
            ));
        }
    }

    /// Lint fixes: the finding under each lint diagnostic in the
    /// request as quick fixes (a semantic or deleting fix labeled as
    /// such and never preferred, alternatives unpreferred), beside each
    /// one the rule-wide "fix every finding of this rule", and on
    /// `source.fixAll` one edit applying every safe fix of the
    /// document, each fix whole or not at all, that does not overlap an
    /// earlier one. The syntax tier's own visibility quick fix already
    /// covers a bare import when that diagnostic is in the request, so
    /// the lint twin steps aside there.
    fn lint_fix_actions(
        &mut self,
        params: &lsp_types::CodeActionParams,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        let uri = &params.text_document.uri;
        let lint_diags: Vec<&lsp_types::Diagnostic> = params
            .context
            .diagnostics
            .iter()
            .filter(|d| d.source.as_deref() == Some("sysmlv2 lint"))
            .collect();
        let wants_fix_all = requested(params, "source.fixAll");
        if lint_diags.is_empty() && !wants_fix_all {
            return;
        }
        let fixes = self.nav.lint_fixes(&self.docs, uri, self.encoding);
        let syntax_visibility_at = |start: lsp_types::Position| {
            params.context.diagnostics.iter().any(|d| {
                d.range.start == start
                    && d.message
                        .starts_with("an import must declare an explicit visibility")
            })
        };
        let mut rule_wide_offered: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for d in &lint_diags {
            let Some(lsp_types::NumberOrString::String(code)) = &d.code else {
                continue;
            };
            if code == "import-visibility" && syntax_visibility_at(d.range.start) {
                continue;
            }
            let mut fixed = false;
            for f in fixes
                .iter()
                .filter(|f| f.rule == code && f.range.start == d.range.start)
            {
                fixed = true;
                let mut push = |title: String,
                                semantic: bool,
                                edit: &lsp_types::WorkspaceEdit,
                                preferred: bool| {
                    let title = if semantic {
                        format!("{title} (rewrites the declaration)")
                    } else if f.deletes {
                        format!("{title} (deletes model text)")
                    } else {
                        title
                    };
                    out.push(quick_fix(title, d, edit.clone(), preferred));
                };
                push(
                    f.label.clone(),
                    f.semantic,
                    &f.edit,
                    !f.semantic && !f.deletes,
                );
                for (label, semantic, edit) in &f.alternatives {
                    push(label.clone(), *semantic, edit, false);
                }
            }
            if fixed && rule_wide_offered.insert(code.clone()) {
                self.rule_wide_fix_actions(uri, d, code, out);
            }
        }
        if wants_fix_all {
            // Each fix whole or not at all: a fix that touches another
            // document, or whose edits collide with what is already
            // kept, is left for a quick fix.
            let (changes, n) = merge_fixes(
                fixes
                    .iter()
                    .filter(|f| !f.semantic && !f.deletes)
                    .map(|f| &f.edit),
                Some(uri),
            );
            if n > 0 {
                out.push(source_action(
                    format!("Fix all auto-fixable lint findings ({n})"),
                    lsp_types::CodeActionKind::SOURCE_FIX_ALL,
                    lsp_types::WorkspaceEdit {
                        changes: Some(changes),
                        ..Default::default()
                    },
                ));
            }
        }
    }

    /// Beside a finding's own fix: every finding of its rule at once,
    /// in this document and across the workspace (each finding's
    /// primary fix, whole or not at all; the user chose the rule, so
    /// semantic and deleting fixes go in, labeled). Offered only where
    /// there is more than the one finding to fix.
    fn rule_wide_fix_actions(
        &mut self,
        uri: &Uri,
        d: &lsp_types::Diagnostic,
        code: &str,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        let rule_fixes = self
            .nav
            .lint_rule_fixes(&self.docs, uri, self.encoding, code);
        let suffix = if rule_fixes.iter().any(|f| f.semantic) {
            " (rewrites the declarations)"
        } else if rule_fixes.iter().any(|f| f.deletes) {
            " (deletes model text)"
        } else {
            ""
        };
        let mut rule_wide = |title: String, changes: HashMap<Uri, Vec<TextEdit>>| {
            out.push(lsp_types::CodeActionOrCommand::CodeAction(
                lsp_types::CodeAction {
                    title,
                    kind: Some(lsp_types::CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![d.clone()]),
                    edit: Some(lsp_types::WorkspaceEdit {
                        changes: Some(changes),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ));
        };
        let (in_file, n_file) = merge_fixes(rule_fixes.iter().map(|f| &f.edit), Some(uri));
        if n_file >= 2 {
            rule_wide(
                format!("Fix all {n_file} `{code}` findings in this file{suffix}"),
                in_file,
            );
        }
        let (everywhere, n_all) = merge_fixes(rule_fixes.iter().map(|f| &f.edit), None);
        let files = everywhere.len();
        if n_all > n_file && files >= 2 {
            rule_wide(
                format!("Fix all {n_all} `{code}` findings across {files} files{suffix}"),
                everywhere,
            );
        }
    }

    /// "Optimize imports" (`source.organizeImports`): drop the unused
    /// private imports, keep everything else — order included.
    fn optimize_imports_action(
        &mut self,
        uri: &Uri,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        let Some(edits) = self.nav.optimize_imports(&self.docs, uri, self.encoding) else {
            return;
        };
        if edits.is_empty() {
            return;
        }
        out.push(source_action(
            "Optimize imports".to_string(),
            lsp_types::CodeActionKind::SOURCE_ORGANIZE_IMPORTS,
            one_file_edit(uri, edits),
        ));
    }

    /// "Sort imports" (`source.sortImports`): alphabetize contiguous
    /// import runs; a syntax-tier reshuffle, no model pass.
    fn sort_imports_action(&self, uri: &Uri, out: &mut Vec<lsp_types::CodeActionOrCommand>) {
        let Some(doc) = self.docs.get(uri) else {
            return;
        };
        let edits = nav::sort_import_edits(
            &doc.text,
            matches!(dialect_of(uri), Dialect::Kerml),
            self.encoding,
        );
        if edits.is_empty() {
            return;
        }
        out.push(source_action(
            "Sort imports".to_string(),
            lsp_types::CodeActionKind::new("source.sortImports"),
            one_file_edit(uri, edits),
        ));
    }

    /// Refactorings: offered on the unfiltered request (the lightbulb /
    /// context menu sends no `only`) and under `refactor` kind filters
    /// — the same ancestor semantics as the source actions, so
    /// `refactor` requests every member of the set. Eligibility gates
    /// run first and are cheap; the dry run that computes the edit only
    /// happens for admitted cursors, and it leaves the session
    /// untouched (no invalidation).
    fn refactor_actions(
        &mut self,
        params: &lsp_types::CodeActionParams,
        out: &mut Vec<lsp_types::CodeActionOrCommand>,
    ) {
        let uri = &params.text_document.uri;
        let unfiltered = params.context.only.is_none();
        let Some(offset) = self.offset_of(uri, params.range.start) else {
            return;
        };
        if unfiltered || requested(params, "refactor.extract") {
            if let Some((title, edit)) =
                self.nav
                    .refactor_extract_action(&self.docs, uri, offset, self.encoding)
            {
                out.push(refactoring(
                    title,
                    lsp_types::CodeActionKind::REFACTOR_EXTRACT,
                    edit,
                ));
            }
        }
        if unfiltered || requested(params, "refactor.move") {
            for (title, edit) in self
                .nav
                .split_actions(&self.docs, uri, offset, self.encoding)
            {
                out.push(refactoring(
                    title,
                    lsp_types::CodeActionKind::new("refactor.move"),
                    edit,
                ));
            }
        }
        if unfiltered || requested(params, "refactor.inline") {
            if let Some((title, edit)) =
                self.nav
                    .refactor_inline_action(&self.docs, uri, offset, self.encoding)
            {
                out.push(refactoring(
                    title,
                    lsp_types::CodeActionKind::REFACTOR_INLINE,
                    edit,
                ));
            }
        }
    }

    /// "Minimize qualified names": collapse every qualified name to its
    /// minimal spelling. A committing model pass, so the session and
    /// the lint cache go either way.
    fn minimize_names_action(&mut self, out: &mut Vec<lsp_types::CodeActionOrCommand>) {
        let edit = self.nav.minimize(&self.docs, self.encoding);
        self.nav.invalidate();
        let Ok(edit) = edit else {
            return;
        };
        if edit.changes.as_ref().is_some_and(|c| !c.is_empty()) {
            out.push(source_action(
                "Minimize qualified names".to_string(),
                lsp_types::CodeActionKind::SOURCE,
                edit,
            ));
        }
    }

    /// The editor's split wizard: plan (and, for `sysmlv2/split`, the
    /// annotated edit of) a package's split under the requested naming
    /// scheme and directory. The package is the declaration under
    /// `position` in `textDocument` (which must be open) or the
    /// qualified `package` name.
    fn split_request(
        &mut self,
        p: SplitRequestParams,
        with_edit: bool,
    ) -> Result<nav::SplitResponse, SplitRefusal> {
        let target = match (p.package, p.position, p.text_document) {
            (Some(name), _, _) => nav::SplitTarget::Package(name),
            (None, Some(pos), Some(doc)) => {
                let offset = self.offset_of(&doc.uri, pos).ok_or_else(|| {
                    SplitRefusal::Params(format!("{} is not an open document", doc.uri.as_str()))
                })?;
                nav::SplitTarget::Offset {
                    uri: doc.uri,
                    offset,
                }
            }
            (None, Some(_), None) => {
                return Err(SplitRefusal::Params(
                    "a position needs its textDocument".to_string(),
                ));
            }
            (None, None, _) => {
                return Err(SplitRefusal::Params(
                    "a split request names a package or a position".to_string(),
                ));
            }
        };
        let options = sysmlv2_transform::SplitOptions {
            naming: match p.naming {
                SplitNamingParam::Keep => sysmlv2_transform::SplitNaming::Keep,
                SplitNamingParam::Slug => sysmlv2_transform::SplitNaming::Slug,
            },
            directory: p.directory,
            ..Default::default()
        };
        self.nav
            .split_request(&self.docs, &target, options, with_edit, self.encoding)
            .map_err(SplitRefusal::Refused)
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
    fn format(&mut self, uri: &Uri) -> (Vec<TextEdit>, Option<String>) {
        if !self.docs.contains_key(uri) {
            return (Vec::new(), None);
        }
        // Project style: the `multiline-conditions` rule's `min` option
        // in the workspace's sysmlint.json carries the chain threshold
        // (0 = keep chains inline); absent or unreadable config keeps
        // the formatter's default.
        let chain_min = self.nav.lint_config().format_chain_min();
        let doc = &self.docs[uri];
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
            Ok(formatted) if formatted == *doc.text => (Vec::new(), None),
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

/// A method whose handling panics, so the tests can pin what a
/// panicking handler does: answer the request, say so, keep serving.
#[cfg(test)]
pub(crate) const PANIC_METHOD: &str = "sysmlv2/panicForTest";
#[cfg(test)]
pub(crate) const PANIC_REASON: &str = "the handler gave up";

/// The message a session failure deserves at the client, if any. A
/// unit that does not parse is the ordinary state of a document being
/// typed — the syntax tier already shows those errors, and repeating
/// them here would drown the real news — but a library that cannot be
/// read, or a payload that does not decode, leaves whole tiers
/// silently empty with nothing said.
fn session_failure(e: &sysmlv2_transform::SessionError) -> Option<String> {
    match e {
        sysmlv2_transform::SessionError::Parse { .. } => None,
        e => Some(e.to_string()),
    }
}

/// Something a tier could not do, with no channel of its own to say so:
/// `show` puts it in front of the user — a library that cannot be read
/// leaves every model-backed answer empty until it is fixed — and
/// anything else goes to the client's log.
pub(crate) struct Report {
    pub(crate) show: bool,
    pub(crate) message: String,
}

impl Report {
    /// The report a session failure deserves, if it deserves one (see
    /// [`session_failure`]). `library`: the failure came from loading
    /// the configured standard library, which the user has to fix.
    pub(crate) fn for_session_failure(
        e: &sysmlv2_transform::SessionError,
        library: bool,
    ) -> Option<Report> {
        let message = session_failure(e)?;
        Some(Report {
            show: library,
            message: match library {
                true => format!("the standard library could not be read: {message}"),
                false => format!("the model could not be built: {message}"),
            },
        })
    }
}

/// The message a caught panic carried, for the client-facing report.
/// Payloads that are neither `&str` nor `String` have no message to
/// show.
pub(crate) fn panic_reason(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "internal error".to_string())
}

/// A request's id and deserialized parameters, or the `InvalidParams`
/// response answering a request whose parameters do not deserialize
/// (an oddly encoded uri, a null in a required field, a fuzzed
/// message) — the request is answered and the session goes on.
fn cast<P: DeserializeOwned>(req: Request) -> Result<(RequestId, P), Response> {
    let Request { id, method, params } = req;
    match serde_json::from_value(params) {
        Ok(p) => Ok((id, p)),
        Err(e) => Err(Response::new_err(
            id,
            ErrorCode::InvalidParams as i32,
            format!("{method}: invalid params: {e}"),
        )),
    }
}

/// Dialect by file extension: `.kerml` is KerML, everything else SysML.
pub(crate) fn dialect_of(uri: &Uri) -> Dialect {
    if is_kerml(uri.path().as_str()) {
        Dialect::Kerml
    } else {
        Dialect::Sysml
    }
}

/// Whether a unit name, path or uri names a KerML file. The extension
/// decides which grammar a unit is read with, and case is not part of
/// it: a file system that preserves case but matches without it hands
/// back `Model.KerML` as readily as `model.kerml`, and reading that as
/// SysML would report the whole file as broken.
pub(crate) fn is_kerml(path: &str) -> bool {
    ends_with_extension(path, b".kerml")
}

/// Whether a file name is a model unit — `.sysml` or `.kerml`, in
/// whatever case it is spelled (see [`is_kerml`]).
pub(crate) fn is_model_file(name: &str) -> bool {
    ends_with_extension(name, b".sysml") || is_kerml(name)
}

/// `path` ends with `extension`, ignoring ASCII case. Compared over
/// bytes: a name is not guaranteed to have a character boundary six
/// bytes from its end.
fn ends_with_extension(path: &str, extension: &[u8]) -> bool {
    let bytes = path.as_bytes();
    bytes
        .len()
        .checked_sub(extension.len())
        .is_some_and(|at| bytes[at..].eq_ignore_ascii_case(extension))
}

/// Kind-filter semantics: an action is requested when an `only` entry
/// equals its kind or is a dot-separated ancestor of it (`source`
/// requests `source.organizeImports`; the reverse does not hold).
fn requested(params: &lsp_types::CodeActionParams, kind: &str) -> bool {
    params.context.only.as_ref().is_some_and(|ks| {
        ks.iter().any(|k| {
            let k = k.as_str();
            kind == k || (kind.starts_with(k) && kind.as_bytes().get(k.len()) == Some(&b'.'))
        })
    })
}

/// A workspace edit confined to one document.
#[allow(clippy::mutable_key_type)] // see the note on `mod nav`
fn one_file_edit(uri: &Uri, edits: Vec<TextEdit>) -> lsp_types::WorkspaceEdit {
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), edits);
    lsp_types::WorkspaceEdit {
        changes: Some(changes),
        ..Default::default()
    }
}

/// A quick fix riding the diagnostic it answers, so the client offers
/// it at that diagnostic's lightbulb.
fn quick_fix(
    title: String,
    diagnostic: &lsp_types::Diagnostic,
    edit: lsp_types::WorkspaceEdit,
    preferred: bool,
) -> lsp_types::CodeActionOrCommand {
    lsp_types::CodeActionOrCommand::CodeAction(lsp_types::CodeAction {
        title,
        kind: Some(lsp_types::CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![diagnostic.clone()]),
        is_preferred: preferred.then_some(true),
        edit: Some(edit),
        ..Default::default()
    })
}

/// A source action: whole-document, tied to no diagnostic.
fn source_action(
    title: String,
    kind: lsp_types::CodeActionKind,
    edit: lsp_types::WorkspaceEdit,
) -> lsp_types::CodeActionOrCommand {
    lsp_types::CodeActionOrCommand::CodeAction(lsp_types::CodeAction {
        title,
        kind: Some(kind),
        edit: Some(edit),
        ..Default::default()
    })
}

/// A refactoring offered at the cursor.
fn refactoring(
    title: String,
    kind: lsp_types::CodeActionKind,
    edit: lsp_types::WorkspaceEdit,
) -> lsp_types::CodeActionOrCommand {
    lsp_types::CodeActionOrCommand::CodeAction(lsp_types::CodeAction {
        title,
        kind: Some(kind),
        edit: Some(edit),
        ..Default::default()
    })
}

/// Merge whole lint fixes into one set of changes: a fix whose edits
/// collide with what is already kept — or, under `only`, that touches any
/// other document — is left out whole, for its own quick fix. Identical
/// edits (two findings inserting the same text at one spot) count once.
/// Returns the changes per document, each sorted, and how many fixes
/// went in.
#[allow(clippy::mutable_key_type)] // see the note on `mod nav`
fn merge_fixes<'a>(
    fixes: impl Iterator<Item = &'a lsp_types::WorkspaceEdit>,
    only: Option<&Uri>,
) -> (HashMap<Uri, Vec<TextEdit>>, usize) {
    let overlaps = |e: &TextEdit, k: &TextEdit| {
        (e.range.start < k.range.end && k.range.start < e.range.end)
            || (e.range.start == k.range.start
                && e.range.end == e.range.start
                && k.range.end == k.range.start
                && e.new_text != k.new_text)
    };
    let mut kept: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
    let mut applied = 0usize;
    for fix in fixes {
        let Some(changes) = fix.changes.as_ref() else {
            continue;
        };
        if changes.is_empty() || only.is_some_and(|u| changes.keys().any(|k| k != u)) {
            continue;
        }
        let fresh: Vec<(&Uri, Vec<TextEdit>)> = changes
            .iter()
            .map(|(u, edits)| {
                let have = kept.get(u);
                let mut edits: Vec<TextEdit> = edits
                    .iter()
                    .filter(|e| !have.is_some_and(|h| h.contains(e)))
                    .cloned()
                    .collect();
                edits.sort_by_key(|e| (e.range.start, e.range.end));
                (u, edits)
            })
            .collect();
        let collides = fresh.iter().any(|(u, edits)| {
            kept.get(*u)
                .is_some_and(|have| edits.iter().any(|e| have.iter().any(|k| overlaps(e, k))))
        });
        if collides {
            continue;
        }
        for (u, edits) in fresh {
            kept.entry(u.clone()).or_default().extend(edits);
        }
        applied += 1;
    }
    for edits in kept.values_mut() {
        edits.sort_by_key(|e| (e.range.start, e.range.end));
    }
    (kept, applied)
}

#[cfg(test)]
mod stack_tests {
    use super::*;

    /// A loop whose thread could not be given the stack the parser's
    /// bound assumes used to run on the host's own stack with nothing
    /// said — and a document nested past that stack ends the server
    /// outright, too late for any channel. The log carries what the
    /// system said and what the session risks by it.
    #[test]
    fn a_loop_whose_stack_is_refused_says_so() {
        let (out, messages) = crossbeam_channel::unbounded();
        let refused = std::io::Error::new(std::io::ErrorKind::OutOfMemory, "no room for a thread");
        say_the_stack_was_refused(&out, &refused);

        let sent: Vec<(String, String)> = messages
            .try_iter()
            .map(|m| {
                let Message::Notification(n) = m else {
                    panic!("{m:?}")
                };
                let message = n.params["message"].as_str().expect("a message").to_string();
                (n.method, message)
            })
            .collect();
        assert_eq!(sent.len(), 1, "{sent:?}");
        assert_eq!(sent[0].0, "window/logMessage", "{sent:?}");
        assert!(sent[0].1.contains("no room for a thread"), "{sent:?}");
        assert!(sent[0].1.contains("nesting bound"), "{sent:?}");
    }
}
