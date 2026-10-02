//! Push-driven frontend: drive the server one
//! message at a time — no threads, no blocking reads, no filesystem of
//! its own.
//! This is the WASM host shape: a web worker feeds client→server
//! JSON-RPC strings in and relays the returned server→client strings.
//!
//! Internally this reuses the whole stdio server: a [`Connection`]
//! memory pair carries outgoing messages (every handler sends into
//! `connection.sender`), drained non-blockingly after each dispatch.
//! Differences from the threaded server, by design:
//! - the workspace model tier is disabled ([`worker::Worker::disabled`])
//!   — in the browser, semantic/library-aware diagnostics are the
//!   kernel worker's job, and this server serves the syntax tier;
//! - no root-directory walk (the browser host has no disk); the standard
//!   library, when wanted, is handed over as sources
//!   ([`PushServer::with_library_sources`]) or as any library form,
//!   prepared ones included ([`PushServer::with_library`]), and feeds
//!   navigation and completions, and the workspace's units arrive as
//!   sources ([`PushServer::set_workspace_sources`]) so navigation
//!   crosses into units the client has not opened.

use lsp_server::{Connection, ErrorCode, Message, Request, Response};
use lsp_types::request::{Initialize, Request as _, Shutdown};
use lsp_types::{InitializeParams, InitializeResult, ServerInfo};
use std::collections::BTreeMap;

use crate::{Error, Server, capabilities, negotiate_encoding, worker};

/// The server endpoint is held from construction until `initialize`
/// builds the server around it, and `server` is `Some` from then on, so
/// exactly one of the two is always available to answer on.
const HELD_UNTIL_BUILT: &str = "the server endpoint is held until the server is built";

/// A server driven by [`PushServer::handle`] calls instead of a
/// blocking main loop.
pub struct PushServer {
    server: Option<Server>,
    /// In-memory standard library for navigation/completions (the WASM
    /// host has no filesystem); `None` = syntax tier only.
    library: Option<sysmlv2_transform::Library>,
    /// In-memory workspace units, held when seeded before `initialize`
    /// (applied to the server's navigation at build time).
    workspace: Option<std::sync::Arc<Vec<(String, String)>>>,
    /// Held until `initialize` arrives (the server is built from its
    /// params); `None` afterwards.
    server_conn: Option<Connection>,
    /// The client-side endpoint: outgoing server messages pile up in
    /// its receiver and are drained after every dispatch.
    client_conn: Connection,
    /// Client capabilities recorded at `initialize`: whether the client
    /// honors `workspace/inlayHint/refresh` and
    /// `workspace/codeLens/refresh`. A workspace re-seed invalidates
    /// answers those tiers already pulled, so the server asks
    /// supporting clients to pull again.
    inlay_refresh: bool,
    code_lens_refresh: bool,
    /// Server-initiated request id counter (its own namespace —
    /// server→client ids are independent of client→server ids).
    next_refresh_id: u64,
    /// Suppress evaluated-value inlay hints restating the declared
    /// expression verbatim. Held here so a host setting applied before
    /// `initialize` survives to the server build; `initialize` itself
    /// may also override it via
    /// `initializationOptions.hideRedundantValueHints`.
    hide_redundant_hints: bool,
    /// Accepting a unit completion inside an untyped attribute's
    /// quantity bracket also declares the type the unit determines.
    /// Held like `hide_redundant_hints`; `initialize` may override it
    /// via `initializationOptions.inferUnitTypes`.
    infer_unit_types: bool,
}

impl Default for PushServer {
    fn default() -> Self {
        Self::new()
    }
}

impl PushServer {
    #[must_use]
    pub fn new() -> PushServer {
        Self::new_with(None)
    }

    /// A push server whose navigation and completions see an in-memory
    /// standard library (`(unit name, text)` units, optionally with a
    /// sealed resolution snapshot recorded against the same units).
    #[must_use]
    pub fn with_library_sources(
        units: Vec<(String, String)>,
        snapshot: Option<Vec<u8>>,
    ) -> PushServer {
        Self::new_with(Some(match snapshot {
            Some(bytes) => sysmlv2_transform::Library::sources_with_snapshot(units, bytes),
            None => sysmlv2_transform::Library::sources(units),
        }))
    }

    /// A push server whose navigation and completions see `library`. A
    /// prepared library was resolved when it was prepared, so a session
    /// resolves the workspace's units against it instead of reading and
    /// resolving the library's sources again; a workspace that may change
    /// what the library's own names resolve to (for example a root name the
    /// library looked up and missed, a root declaration named like one of
    /// the library's, or a root filter) has the library resolved again with
    /// it. Any other library form works too: a directory library reads the
    /// directory and reads and writes an on-disk cache, which a host
    /// without a filesystem avoids by passing sources or a prepared
    /// library.
    #[must_use]
    pub fn with_library(library: sysmlv2_transform::Library) -> PushServer {
        Self::new_with(Some(library))
    }

    fn new_with(library: Option<sysmlv2_transform::Library>) -> PushServer {
        let (server_conn, client_conn) = Connection::memory();
        PushServer {
            server: None,
            library,
            workspace: None,
            server_conn: Some(server_conn),
            client_conn,
            inlay_refresh: false,
            code_lens_refresh: false,
            next_refresh_id: 0,
            hide_redundant_hints: true,
            infer_unit_types: true,
        }
    }

    /// Set whether evaluated-value inlay hints that restate the
    /// declared expression verbatim are suppressed (default on). On a
    /// running server this changes pull-tier answers without any
    /// source changing, so supporting clients are asked to re-pull —
    /// drain with [`Self::take_outbound`].
    pub fn set_hide_redundant_value_hints(&mut self, on: bool) {
        self.hide_redundant_hints = on;
        if let Some(server) = &mut self.server {
            server.nav.set_hide_redundant_value_hints(on);
            self.send_refreshes();
        }
    }

    /// Set whether accepting a unit completion inside an untyped
    /// attribute's quantity bracket also declares the type the unit
    /// determines (default on). Takes effect on the next completion
    /// request — nothing already rendered needs a refresh.
    pub fn set_infer_unit_types(&mut self, on: bool) {
        self.infer_unit_types = on;
        if let Some(server) = &mut self.server {
            server.nav.set_infer_unit_types(on);
        }
    }

    /// Seed (or replace) the navigation workspace: every model unit the
    /// host knows about, as `(uri string, text)` — the same uri strings
    /// the client opens documents under. Open-document texts overlay
    /// these at session build, so definition/references/hover cross
    /// into units that are not open. Callable before or after
    /// `initialize`; each call replaces the previous set.
    ///
    /// A re-seed on a running server invalidates inlay hints and code
    /// lenses the client already pulled (both answer from the seeded
    /// session), so refresh requests go out to clients that support
    /// them — drain with [`Self::take_outbound`] (the host relays them
    /// like any [`Self::handle`] output; without the drain they ride
    /// along with the next dispatch).
    pub fn set_workspace_sources(&mut self, units: Vec<(String, String)>) {
        let units = std::sync::Arc::new(units);
        if let Some(server) = &mut self.server {
            server.nav.set_workspace_sources(units.clone());
            self.send_refreshes();
        }
        self.workspace = Some(units);
    }

    /// Drop the running server's cached navigation sessions and ask the
    /// client to re-pull the pull-model tiers — for host-side engine
    /// reconfiguration (an evaluator switch) that changes answers
    /// without any source changing.
    pub fn invalidate_sessions(&mut self) {
        if let Some(server) = &mut self.server {
            server.nav.invalidate();
            self.send_refreshes();
        }
    }

    /// Ask the client to re-pull inlay hints and code lenses (where it
    /// declared refresh support).
    fn send_refreshes(&mut self) {
        let Some(server) = &self.server else {
            return;
        };
        for (supported, method) in [
            (self.inlay_refresh, "workspace/inlayHint/refresh"),
            (self.code_lens_refresh, "workspace/codeLens/refresh"),
        ] {
            if !supported {
                continue;
            }
            self.next_refresh_id += 1;
            let id =
                lsp_server::RequestId::from(format!("sysmlv2-refresh-{}", self.next_refresh_id));
            let _ = server.connection.sender.send(Message::Request(Request::new(
                id,
                method.to_string(),
                serde_json::Value::Null,
            )));
        }
    }

    /// Serialized server→client messages produced outside a
    /// [`Self::handle`] dispatch (the refresh requests a workspace
    /// re-seed emits).
    pub fn take_outbound(&mut self) -> Result<Vec<String>, Error> {
        let mut out = Vec::new();
        while let Ok(m) = self.client_conn.receiver.try_recv() {
            out.push(serde_json::to_string(&m)?);
        }
        Ok(out)
    }

    /// Feed one client→server JSON-RPC message; returns the
    /// server→client messages it produced, in order, serialized.
    pub fn handle(&mut self, msg: &str) -> Result<Vec<String>, Error> {
        let msg: Message = serde_json::from_str(msg)?;
        match msg {
            Message::Request(req) if req.method == Initialize::METHOD => {
                self.initialize(req)?;
            }
            Message::Request(req) => match &mut self.server {
                Some(server) if req.method == Shutdown::METHOD => {
                    server
                        .connection
                        .sender
                        .send(Message::Response(Response::new_ok(
                            req.id,
                            serde_json::Value::Null,
                        )))?;
                }
                Some(server) => server.handle_request(req)?,
                None => self.reply(Response::new_err(
                    req.id,
                    ErrorCode::ServerNotInitialized as i32,
                    "initialize first".to_string(),
                ))?,
            },
            Message::Notification(n) => {
                // `initialized` and `exit` need nothing here; the rest
                // only make sense on a built server.
                if let Some(server) = &mut self.server {
                    server.handle_notification(n)?;
                }
            }
            Message::Response(_) => {}
        }
        let mut out = Vec::new();
        while let Ok(m) = self.client_conn.receiver.try_recv() {
            out.push(serde_json::to_string(&m)?);
        }
        Ok(out)
    }

    /// A response produced outside a built server's own dispatch, on
    /// the server→client channel [`Self::handle`] drains — the channel
    /// the built server answers on, or, before `initialize`, the one it
    /// will be built around. (The client endpoint's sender feeds the
    /// server's inbox, which nothing here reads.)
    fn reply(&self, response: Response) -> Result<(), Error> {
        let sender = match &self.server {
            Some(server) => &server.connection.sender,
            None => &self.server_conn.as_ref().expect(HELD_UNTIL_BUILT).sender,
        };
        sender.send(Message::Response(response))?;
        Ok(())
    }

    fn initialize(&mut self, req: Request) -> Result<(), Error> {
        if self.server.is_some() {
            // Double initialize: protocol error.
            return self.reply(Response::new_err(
                req.id,
                ErrorCode::InvalidRequest as i32,
                "already initialized".to_string(),
            ));
        }
        let init: InitializeParams = match serde_json::from_value(req.params) {
            Ok(init) => init,
            Err(e) => {
                // Malformed: answered, and still initializable.
                return self.reply(Response::new_err(
                    req.id,
                    ErrorCode::InvalidParams as i32,
                    format!("initialize: invalid params: {e}"),
                ));
            }
        };
        let connection = self.server_conn.take().expect(HELD_UNTIL_BUILT);
        let encoding = negotiate_encoding(&init);
        let ws = init.capabilities.workspace.as_ref();
        self.inlay_refresh = ws
            .and_then(|w| w.inlay_hint.as_ref())
            .and_then(|c| c.refresh_support)
            .unwrap_or(false);
        self.code_lens_refresh = ws
            .and_then(|w| w.code_lens.as_ref())
            .and_then(|c| c.refresh_support)
            .unwrap_or(false);
        let result = InitializeResult {
            capabilities: capabilities(encoding),
            server_info: Some(ServerInfo {
                name: "sysmlv2-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        };
        connection
            .sender
            .send(Message::Response(Response::new_ok(req.id, result)))?;
        let mut nav = crate::nav::Nav::new_with(self.library.clone());
        if let Some(units) = &self.workspace {
            nav.set_workspace_sources(units.clone());
        }
        if let Some(on) = crate::hide_redundant_value_hints(&init) {
            self.hide_redundant_hints = on;
        }
        nav.set_hide_redundant_value_hints(self.hide_redundant_hints);
        if let Some(on) = crate::infer_unit_types(&init) {
            self.infer_unit_types = on;
        }
        nav.set_infer_unit_types(self.infer_unit_types);
        nav.set_snippet_completions(crate::snippet_completions(&init));
        nav.set_insert_replace_completions(crate::insert_replace_completions(&init));
        nav.set_signature_label_offsets(crate::signature_label_offsets(&init));
        self.server = Some(Server {
            connection,
            encoding,
            docs: BTreeMap::new(),
            nav,
            worker: worker::Worker::disabled(),
            root: None,
            reported: std::collections::HashSet::new(),
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::PushServer;

    fn responses(server: &mut PushServer, msg: &serde_json::Value) -> Vec<serde_json::Value> {
        server
            .handle(&msg.to_string())
            .expect("handled")
            .iter()
            .map(|s| serde_json::from_str(s).expect("valid json"))
            .collect()
    }

    /// The push driver speaks the whole protocol without a thread or a
    /// blocking read: initialize → didOpen (diagnostics push) →
    /// documentSymbol → shutdown.
    #[test]
    fn push_conversation() {
        let mut s = PushServer::new();
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        assert_eq!(out.len(), 1);
        assert_eq!(out[0]["result"]["serverInfo"]["name"], "sysmlv2-lsp");
        assert_eq!(
            out[0]["result"]["capabilities"]["positionEncoding"],
            "utf-8"
        );

        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        );

        // A document with a syntax-tier problem publishes diagnostics.
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///workspace/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": "package P { part def X; part x : X; "}}}),
        );
        let diag = out
            .iter()
            .find(|m| m["method"] == "textDocument/publishDiagnostics")
            .expect("diagnostics published");
        assert!(!diag["params"]["diagnostics"].as_array().unwrap().is_empty());

        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": "file:///workspace/m.sysml"}}}),
        );
        let symbols = out[0]["result"].as_array().expect("symbol tree");
        assert_eq!(symbols[0]["name"], "P");
        assert!(symbols[0]["children"].as_array().unwrap().len() >= 2);

        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": null}),
        );
        assert_eq!(out[0]["result"], serde_json::Value::Null);
    }

    /// Malformed messages are answered (requests) or logged
    /// (notifications) and never end the session — a bad `initialize`
    /// included, which leaves the server initializable.
    #[test]
    fn malformed_messages_do_not_end_the_session() {
        let mut s = PushServer::new();
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 0, "method": "textDocument/hover",
                "params": {}}),
        );
        assert_eq!(out[0]["error"]["code"], -32002, "{out:?}");
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": 7}}),
        );
        assert_eq!(out[0]["error"]["code"], -32602, "{out:?}");
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        assert_eq!(out[0]["result"]["serverInfo"]["name"], "sysmlv2-lsp");
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        assert_eq!(out[0]["error"]["code"], -32600, "{out:?}");

        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": "one"}}}),
        );
        assert_eq!(out.len(), 1, "{out:?}");
        assert_eq!(out[0]["method"], "window/logMessage");
        assert!(
            out[0]["params"]["message"]
                .as_str()
                .unwrap()
                .starts_with("textDocument/didOpen: invalid params"),
            "{out:?}"
        );

        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": null}}}),
        );
        assert_eq!(out[0]["id"], 3);
        assert_eq!(out[0]["error"]["code"], -32602, "{out:?}");

        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": "package P { part def X; }"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"}}}),
        );
        assert_eq!(out[0]["result"][0]["name"], "P", "{out:?}");
    }

    /// A handler that panics answers the request with an internal
    /// error, says so once, and leaves the session serving — the same
    /// for a notification, which has no reply to carry the error. (The
    /// panics these two messages provoke print to stderr as usual; the
    /// point is that the session outlives them.)
    #[test]
    fn a_panicking_handler_does_not_end_the_session() {
        let mut s = PushServer::new();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": "package P { part def X; }"}}}),
        );

        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": crate::PANIC_METHOD,
                "params": null}),
        );
        let shown: Vec<&serde_json::Value> = out
            .iter()
            .filter(|m| m["method"] == "window/showMessage")
            .collect();
        assert_eq!(shown.len(), 1, "{out:?}");
        assert!(
            shown[0]["params"]["message"]
                .as_str()
                .unwrap()
                .contains(crate::PANIC_REASON),
            "{out:?}"
        );
        let answer = out.iter().find(|m| m["id"] == 2).expect("answered");
        assert_eq!(answer["error"]["code"], -32603, "{out:?}");

        // The same failure a second time is not announced again.
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": crate::PANIC_METHOD,
                "params": null}),
        );
        assert!(
            !out.iter().any(|m| m["method"] == "window/showMessage"),
            "{out:?}"
        );
        assert_eq!(out[0]["error"]["code"], -32603, "{out:?}");

        // A notification whose handling panics is dropped, not fatal.
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": crate::PANIC_METHOD, "params": null}),
        );
        assert!(out.is_empty(), "{out:?}");

        // Still serving.
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"}}}),
        );
        assert_eq!(out[0]["result"][0]["name"], "P", "{out:?}");
    }

    /// With in-memory library sources, completions offer the library's
    /// packages and direct members alongside workspace names.
    #[test]
    fn library_sources_feed_completions() {
        let mut s = PushServer::with_library_sources(
            vec![(
                "MiniLib.kerml".to_string(),
                "standard library package MiniLib { class Widget; class Gadget; }".to_string(),
            )],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": "package P { part def X; ref w : }"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 0, "character": 32}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let labels: Vec<&str> = items.iter().filter_map(|i| i["label"].as_str()).collect();
        assert!(labels.contains(&"X"), "workspace name offered");
        assert!(labels.contains(&"MiniLib"), "library package offered");
        assert!(labels.contains(&"Widget"), "library member offered");
        let widget = items.iter().find(|i| i["label"] == "Widget").unwrap();
        assert_eq!(widget["detail"], "MiniLib::Widget");
    }

    /// A naked reference to an out-of-scope library member is offered
    /// with the import edit that makes it resolve; names an
    /// existing import already admits, and top-level packages (root
    /// visible), stay edit-free.
    #[test]
    fn completion_auto_imports_out_of_scope_names() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    private import OtherLib::*;\n    ref w : \n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 2, "character": 12}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        assert_eq!(
            widget["additionalTextEdits"],
            serde_json::json!([{
                "range": {"start": {"line": 1, "character": 31},
                          "end": {"line": 1, "character": 31}},
                "newText": "\n    private import MiniLib::Widget;"
            }]),
            "import inserted after the last import, matching its style"
        );
        assert_eq!(widget["labelDetails"]["description"], "import MiniLib");
        let bolt = items.iter().find(|i| i["label"] == "Bolt").expect("Bolt");
        assert!(
            bolt.get("additionalTextEdits").is_none(),
            "already admitted by `import OtherLib::*`: {bolt}"
        );
        let pkg = items
            .iter()
            .find(|i| i["label"] == "MiniLib")
            .expect("MiniLib");
        assert!(
            pkg.get("additionalTextEdits").is_none(),
            "top-level package resolves from the root: {pkg}"
        );
    }

    /// A restricted short name (`<'m/s²'>`) is offered as its own item
    /// and completes QUOTED at the reference — typed `[m/s` becomes
    /// `['m/s²']` — with the matching quoted import inserted.
    #[test]
    fn completion_quotes_restricted_names() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute g = 9.8 [m/s];\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 26}}}),
        );
        let items = &completion_items(&out[0]["result"]);
        let unit = items
            .iter()
            .find(|i| i["label"] == "m/s²")
            .expect("short symbol offered as its own item");
        assert_eq!(
            unit["textEdit"],
            serde_json::json!({
                "range": {"start": {"line": 1, "character": 23},
                          "end": {"line": 1, "character": 26}},
                "newText": "'m/s²'"
            }),
            "typed `m/s` replaced by the quoted spelling"
        );
        let import = &unit["additionalTextEdits"][0]["newText"];
        assert_eq!(import, "private import MiniLib::'m/s²';\n    ");
        // The long spelling is offered too, quoting the same way.
        let long = items
            .iter()
            .find(|i| i["label"] == "metre per second squared")
            .expect("regular name offered");
        assert_eq!(long["textEdit"]["newText"], "'metre per second squared'");
    }

    /// Inside a quoted name being typed, accepting replaces the whole
    /// typed spelling from its opening quote — every word, and the
    /// closing quote an editor inserts along with the opening one — not
    /// just the last word; each item filters by its quoted spelling,
    /// which is what an editor matches the text from the quote against.
    #[test]
    fn completion_replaces_the_quoted_name_being_typed() {
        let complete = |text: &str, character: u32| -> Vec<serde_json::Value> {
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 1, "character": character}}}),
            );
            completion_items(&out[0]["result"])
        };
        let edit = |start: u32, end: u32, new_text: &str| {
            serde_json::json!({
                "range": {"start": {"line": 1, "character": start},
                          "end": {"line": 1, "character": end}},
                "newText": new_text
            })
        };
        let item = |items: &[serde_json::Value], label: &str, text: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered: {text:?}"))
                .clone()
        };
        // The cursor after `sec`; the opening quote at 23.
        for (text, end, long) in [
            // Unterminated: the edit brings the closing quote, and the
            // bracket repair rides behind it.
            (
                "package P {\n    attribute g = 9.8 ['metre per sec\n}\n",
                37,
                "'metre per second squared']",
            ),
            // Closed: the closing quote is replaced too.
            (
                "package P {\n    attribute g = 9.8 ['metre per sec'\n}\n",
                38,
                "'metre per second squared']",
            ),
            (
                "package P {\n    attribute g = 9.8 ['metre per sec']\n}\n",
                38,
                "'metre per second squared'",
            ),
        ] {
            let items = complete(text, 37);
            let unit = item(&items, "metre per second squared", text);
            assert_eq!(unit["textEdit"], edit(23, end, long), "{text:?}");
            assert_eq!(unit["filterText"], "'metre per second squared'");
        }
        // A basic name typed quoted is accepted bare; the cursor after
        // `Wid`, the opening quote at 16. (`alias … for` takes any
        // element, a class included.)
        for (text, end) in [
            ("package P {\n    alias a for 'Wid\n}\n", 20),
            ("package P {\n    alias a for 'Wid'\n}\n", 21),
        ] {
            let items = complete(text, 20);
            let w = item(&items, "Widget", text);
            assert_eq!(w["textEdit"], edit(16, end, "Widget"), "{text:?}");
            assert_eq!(w["filterText"], "'Widget'");
        }

        // No closing quote on the line: the rest of the word the cursor
        // sits in is part of the name being typed, replaced with it.
        let items = complete(
            "package P {\n    attribute g = 9.8 ['metre per sec\n}\n",
            35,
        );
        let unit = items
            .iter()
            .find(|i| i["label"] == "metre per second squared")
            .expect("unit offered mid-word");
        assert_eq!(
            unit["textEdit"],
            edit(23, 37, "'metre per second squared']")
        );
        // A later quoted name on the line does not close the one being
        // typed: its opening quote would leave the rest of the line
        // with an unterminated name.
        let items = complete("package P {\n    ref a : 'Wid, 'Gadget';\n}\n", 16);
        let w = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget offered");
        assert_eq!(w["textEdit"], edit(12, 16, "Widget"));
        // A quote left open on an earlier line — of a quoted name, or of
        // a string running to the end — does not flip the pairing on this
        // one: the quote being typed still opens the name.
        for open in ["'open;", "\"open;"] {
            let text = format!(
                "package P {{\n    doc /* it's */\n    attribute s = {open}\n    attribute g = 9.8 ['m/\n}}\n"
            );
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 3, "character": 26}}}),
            );
            let unit = out[0]["result"]
                .as_array()
                .expect("completion items")
                .iter()
                .find(|i| i["label"] == "m/s²")
                .expect("m/s² offered")
                .clone();
            assert_eq!(
                unit["textEdit"],
                serde_json::json!({
                    "range": {"start": {"line": 3, "character": 23},
                              "end": {"line": 3, "character": 26}},
                    "newText": "'m/s²']"
                }),
                "{open}"
            );
        }

        // A quote that opens nothing at the cursor — a closed quoted
        // name, a comment's apostrophe — leaves the partial word alone.
        for (text, character) in [
            ("package P {\n    attribute 'g 1' = 9.8 [m/s\n}\n", 30u32),
            (
                "package P {\n    attribute g /* it's */ = 9.8 [m/s\n}\n",
                37,
            ),
        ] {
            let items = complete(text, character);
            let unit = items
                .iter()
                .find(|i| i["label"] == "m/s²")
                .unwrap_or_else(|| panic!("m/s² offered: {text:?}"));
            assert_eq!(
                unit["textEdit"],
                edit(character - 3, character, "'m/s²']"),
                "{text:?}"
            );
            assert!(unit["filterText"].is_null(), "{text:?}");
        }
    }

    /// Multi-word library names (`'metre per second squared'`) are
    /// offered only inside an open bracket, where a unit is written —
    /// never in a plain expression or an import path — while their
    /// short symbols stay offered there, a qualifier still lists them,
    /// and the workspace's own multi-word names are unaffected.
    #[test]
    fn multiword_library_names_only_inside_brackets() {
        const LONG: &str = "metre per second squared";
        for (text, line, character, offered) in [
            ("package P {\n    ref w = \n}\n", 1u32, 12u32, false),
            ("package P {\n    attribute g = \n}\n", 1, 18, false),
            ("package P {\n    attribute g = 9.8 [m\n}\n", 1, 24, true),
            ("package P {\n    attribute g = 9.8 ['met\n}\n", 1, 27, true),
            (
                "package P {\n    attribute g = 9.8 [m] + \n}\n",
                1,
                28,
                false,
            ),
            ("package P {\n    private import metre\n}\n", 1, 24, false),
            ("package P {\n    part w : MiniLib::\n}\n", 1, 22, true),
        ] {
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": line, "character": character}}}),
            );
            let items = out[0]["result"].as_array().expect("completion items");
            let labels = completion_labels(items);
            assert_eq!(labels.contains(&LONG), offered, "{text:?}: {labels:?}");
            assert!(labels.contains(&"m/s²"), "short symbol offered: {text:?}");
        }

        // The workspace's own multi-word names stay offered everywhere.
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    part def 'Vehicle One';\n    part w : \n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 2, "character": 13}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let labels = completion_labels(items);
        assert!(labels.contains(&"Vehicle One"), "{labels:?}");
        assert!(!labels.contains(&LONG), "{labels:?}");
    }

    /// A unit name containing whitespace typed word by word without its
    /// quotes inside a bracket: once the words typed begin the name,
    /// accepting it replaces them all, and it filters by its own
    /// spelling, spaces included. Outside a bracket the words before the
    /// partial one keep their own meaning — a type followed by a keyword,
    /// a keyword followed by a declared name — and every name stays with
    /// the partial word, filtering without whitespace.
    #[test]
    fn completion_takes_a_multiword_name_typed_word_by_word() {
        let complete = |text: &str, line: u32, character: u32| -> Vec<serde_json::Value> {
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": line, "character": character}}}),
            );
            out[0]["result"]
                .as_array()
                .expect("completion items")
                .clone()
        };
        let item = |items: &[serde_json::Value], label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"))
                .clone()
        };
        let edit = |line: u32, start: u32, end: u32, new_text: &str| {
            serde_json::json!({
                "range": {"start": {"line": line, "character": start},
                          "end": {"line": line, "character": end}},
                "newText": new_text
            })
        };

        let items = complete("package P {\n    attribute g = 9.8 [metre per\n}\n", 1, 32);
        let unit = item(&items, "metre per second squared");
        assert_eq!(
            unit["textEdit"],
            edit(1, 23, 32, "'metre per second squared']")
        );
        assert!(unit["filterText"].is_null(), "{unit}");
        // Case aside, in any alphabet. (A unit: a unit bracket lists
        // nothing else.)
        let items = complete(
            "package P {\n    attribute 'Øre per mark' : MeasurementReferences::TensorMeasurementReference;\n    \
             attribute g = 9.8 [Øre p\n}\n",
            2,
            29,
        );
        let unit = item(&items, "Øre per mark");
        assert_eq!(unit["textEdit"], edit(2, 23, 29, "'Øre per mark']"));

        let model = "package P {\n    part def 'Vehicle One'; part def 'Part Number'; \
                     item def 'Fuel Oil'; part def 'Fuel Tank'; attribute 'Flow Rate'; \
                     part def 'Front Left Wheel';\n    LINE\n}\n";
        for (line, character, start, label, filter) in [
            // A type, then the start of `ordered`.
            ("part w : Vehicle o", 22, 21, "Vehicle One", "Vehicle_One"),
            // A declared name, then another word.
            ("in item fuel O", 18, 17, "Fuel Oil", "Fuel_Oil"),
            // A feature, then the start of `then`.
            ("first fuel t", 16, 15, "Fuel Tank", "Fuel_Tank"),
            // A keyword, then a declared name.
            ("flow r", 10, 9, "Flow Rate", "Flow_Rate"),
            // Words that do not begin the name.
            ("part w : Truck O", 20, 19, "Vehicle One", "Vehicle_One"),
            // Three words: a typed space still closes the list.
            (
                "part w : Front L",
                20,
                19,
                "Front Left Wheel",
                "Front_Left_Wheel",
            ),
        ] {
            let items = complete(&model.replace("LINE", line), 2, character);
            let one = item(&items, label);
            let spelled = format!("'{label}'");
            assert_eq!(
                one["textEdit"],
                edit(2, start, character, &spelled),
                "{line:?}"
            );
            assert_eq!(one["filterText"], filter, "{line:?}");
        }
        // A declared name after its keyword takes no element name at all,
        // so none can replace the keyword either.
        let items = complete(&model.replace("LINE", "part n"), 2, 10);
        assert!(
            items.iter().all(|i| i["label"] != "Part Number"),
            "{items:?}"
        );
    }

    /// A name containing whitespace (a model's own `'Vehicle One'`)
    /// cannot keep an editor's list open past a typed space. The editor
    /// refilters an open list by the text typed since each item's range
    /// start, spaces included, and closes it only when nothing matches;
    /// a list the `:` trigger opened must therefore empty on the space
    /// that follows, so the next word opens a fresh list instead of
    /// being filtered against this one. The name stays reachable by
    /// typing it: a word of it, or its quoted spelling.
    #[test]
    fn a_typed_space_closes_the_list_on_multiword_names() {
        // The editor's filter, reduced to what decides here: the typed
        // characters occur in order in the item's filter text.
        let keeps = |item: &serde_json::Value, typed: &str| {
            let filter = item["filterText"]
                .as_str()
                .or(item["label"].as_str())
                .expect("label")
                .to_lowercase();
            let mut rest = filter.chars();
            typed.to_lowercase().chars().all(|t| rest.any(|c| c == t))
        };
        let mut s = two_package_server();
        let mut complete = |version: i32, line: &str, character: u32| {
            let text = format!("package P {{\n    part def 'Vehicle One';\n{line}\n}}\n");
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": format!("file:///w/m{version}.sysml"),
                                     "languageId": "sysml", "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": version, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": format!("file:///w/m{version}.sysml")},
                               "position": {"line": 2, "character": character}}}),
            );
            out[0]["result"]
                .as_array()
                .expect("completion items")
                .clone()
        };

        // The list the `:` trigger opens: every item's range starts at
        // the cursor, so a typed space is the text each is filtered by.
        let items = complete(1, "    part w :", 12);
        let one = items
            .iter()
            .find(|i| i["label"] == "Vehicle One")
            .expect("the workspace's multi-word name is offered");
        assert_eq!(one["textEdit"]["range"]["start"]["character"], 12);
        let alive: Vec<&str> = items
            .iter()
            .filter(|i| keeps(i, " "))
            .filter_map(|i| i["label"].as_str())
            .collect();
        assert!(alive.is_empty(), "a typed space keeps {alive:?}");

        // Typed after the space: a fresh list finds it by a word.
        let items = complete(2, "    part w : Veh", 16);
        let one = items
            .iter()
            .find(|i| i["label"] == "Vehicle One")
            .expect("offered after its first word");
        assert!(keeps(one, "Veh") && keeps(one, "One"), "{one}");
        assert_eq!(one["textEdit"]["newText"], "'Vehicle One'");

        // Inside quotes the space is part of the name being typed.
        let items = complete(3, "    part w : 'Vehicle O'", 23);
        let one = items
            .iter()
            .find(|i| i["label"] == "Vehicle One")
            .expect("offered inside quotes");
        assert!(keeps(one, "'Vehicle O"), "{one}");

        // In a bracket, where multi-word units are offered too.
        let items = complete(4, "    attribute g = 9.8 [", 23);
        assert!(
            completion_labels(&items).contains(&"metre per second squared"),
            "units offered in a bracket"
        );
        let alive: Vec<&str> = items
            .iter()
            .filter(|i| keeps(i, " "))
            .filter_map(|i| i["label"].as_str())
            .collect();
        assert!(alive.is_empty(), "a typed space keeps {alive:?}");
    }

    /// Accepting a suggestion also repairs the statement being typed
    /// (autofix): an unclosed quantity bracket closes, riding the main
    /// edit on a bare tail. The terminal `;` is never inserted — not on
    /// a bare tail, not behind an already-auto-closed bracket.
    #[test]
    fn completion_repairs_the_statement() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute gravity = 9.8 [m\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(
            unit["textEdit"],
            serde_json::json!({
                "range": {"start": {"line": 1, "character": 29},
                          "end": {"line": 1, "character": 30}},
                "newText": "'m/s²']"
            }),
            "the bracket close rides the main edit, no terminator"
        );
        // The import edit rides along as before.
        assert_eq!(
            unit["additionalTextEdits"][0]["newText"],
            "private import MiniLib::'m/s²';\n    "
        );

        // Auto-closed variant: `]` already after the cursor — nothing
        // left to repair.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                "contentChanges": [
                    {"text": "package P {\n    attribute gravity = 9.8 [m]\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = &completion_items(&out[0]["result"]);
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(
            unit["textEdit"]["newText"], "'m/s²'",
            "no suffix on the main edit"
        );
        let extras = unit["additionalTextEdits"].as_array().expect("extras");
        assert_eq!(extras.len(), 1, "the import only: {extras:?}");
        assert_eq!(
            extras[0]["newText"],
            "private import MiniLib::'m/s²';\n    "
        );

        // Already terminated: nothing to repair.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 3},
                "contentChanges": [
                    {"text": "package P {\n    attribute gravity = 9.8 [m];\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = &completion_items(&out[0]["result"]);
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(unit["textEdit"]["newText"], "'m/s²'");
        assert_eq!(
            unit["additionalTextEdits"].as_array().map(|a| a.len()),
            Some(1),
            "import only — no repairs on a terminated statement"
        );
    }

    /// Unit typing reads where accepted text goes as well as the
    /// accepts themselves: one read of the text ahead of the cursor
    /// serves both.
    #[test]
    fn completion_reads_the_quoted_name_once_per_request() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute g = 9.8 ['m\n}\n"}}}),
        );
        crate::accept::QUOTE_READS.with(|n| n.set(0));
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 24}}}),
        );
        assert!(
            completion_labels(out[0]["result"].as_array().expect("items")).contains(&"m/s²"),
            "{out:?}"
        );
        assert_eq!(crate::accept::QUOTE_READS.with(std::cell::Cell::get), 1);
    }

    /// The statement is scanned for repairs once per replacement start
    /// the request's items share, not once per item: after `[m/` every
    /// name starts at the cursor but `m/s²`, which reaches back over its
    /// own characters.
    #[test]
    fn completion_scans_the_statement_once_per_replacement_start() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    \
                                          attribute <u1> unitOne : MeasurementReferences::TensorMeasurementReference;\n    \
                                          attribute <u2> unitTwo : MeasurementReferences::TensorMeasurementReference;\n    \
                                          attribute gravity = 9.8 [m/\n}\n"}}}),
        );
        crate::autofix::SCANS.with(|n| n.set(0));
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 3, "character": 31}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let repaired: Vec<&str> = items
            .iter()
            .filter_map(|i| i["textEdit"]["newText"].as_str())
            .filter(|t| t.ends_with(']'))
            .collect();
        assert!(repaired.len() > 2, "names carry the `]`: {repaired:?}");
        assert!(repaired.contains(&"'m/s²']"), "{repaired:?}");
        assert_eq!(
            crate::autofix::SCANS.with(std::cell::Cell::get),
            2,
            "one scan per distinct replacement start"
        );
    }

    /// A snippet-capable client gets the repair suffix behind a `$0`
    /// stop: accepting leaves the cursor after the accepted name,
    /// before the auto-inserted `]`, where typing continues.
    #[test]
    fn snippet_client_gets_cursor_stop_before_repairs() {
        let mut s = two_package_server_with_caps(&serde_json::json!({
            "general": {"positionEncodings": ["utf-8"]},
            "textDocument": {"completion": {"completionItem": {"snippetSupport": true}}}}));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute gravity = 9.8 [m\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(
            unit["textEdit"]["newText"], "'m/s²'$0]",
            "cursor stop between the name and the repair suffix"
        );
        assert_eq!(unit["insertTextFormat"], 2, "snippet format declared");

        // An import-context accept adds no terminator, so no snippet.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                "contentChanges": [
                    {"text": "package P {\n    private import Widge\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 24}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        assert_eq!(widget["textEdit"]["newText"], "MiniLib::Widget");
        assert!(
            widget["insertTextFormat"].is_null(),
            "plain edit stays plain"
        );

        // No repairs → no snippet: the plain quoting edit stays plain.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 3},
                "contentChanges": [
                    {"text": "package P {\n    attribute gravity = 9.8 [m];\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = &completion_items(&out[0]["result"]);
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(unit["textEdit"]["newText"], "'m/s²'");
        assert!(unit["insertTextFormat"].is_null(), "plain edit stays plain");

        // A filter condition's open bracket closes behind the path.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 5},
                "contentChanges": [
                    {"text": "package P {\n    private import OtherLib::*[@Widge\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 9, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 37}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        assert_eq!(widget["textEdit"]["newText"], "MiniLib::Widget$0]");
        assert_eq!(widget["insertTextFormat"], 2);

        // A terminator right at the cursor: the `]` rides the main edit
        // ahead of it — never an extra edit at the main edit's end.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 6},
                "contentChanges": [
                    {"text": "package P {\n    attribute gravity = 9.8 [m;\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 10, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 30}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(unit["textEdit"]["newText"], "'m/s²'$0]");
        let extras = unit["additionalTextEdits"].as_array().expect("extras");
        assert_eq!(extras.len(), 1, "the import only: {extras:?}");
    }

    /// With the cursor inside a word (`Wid|get`), a client that takes
    /// insert/replace edits gets both ranges on every item, keywords
    /// included — insert up to the cursor, replace through the rest of
    /// the word — so its own setting decides. Quoting holds in both; a
    /// repair behind the word is dropped (it would overlap the
    /// replacement), one past it stays. Other clients keep the insert
    /// range alone.
    #[test]
    fn mid_word_completions_carry_insert_and_replace_ranges() {
        let complete = |caps: &serde_json::Value, line: &str, character: u32| {
            let mut s = two_package_server_with_caps(caps);
            let text = format!("package P {{\n{line}\n}}\n");
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 1, "character": character}}}),
            );
            out[0]["result"]
                .as_array()
                .expect("completion items")
                .clone()
        };
        let range = |start: u32, end: u32| {
            serde_json::json!({"start": {"line": 1, "character": start},
                               "end": {"line": 1, "character": end}})
        };
        let find = |items: &[serde_json::Value], label: &str, kind: Option<u32>| {
            items
                .iter()
                .find(|i| i["label"] == label && kind.is_none_or(|k| i["kind"] == k))
                .unwrap_or_else(|| panic!("{label} offered"))
                .clone()
        };
        let both = serde_json::json!({
            "general": {"positionEncodings": ["utf-8"]},
            "textDocument": {"completion": {"completionItem": {"insertReplaceSupport": true}}}});
        let insert_only = serde_json::json!({"general": {"positionEncodings": ["utf-8"]}});
        const CLASS: Option<u32> = Some(7);
        const KEYWORD: Option<u32> = Some(14);

        // A plain name: `Wid|get` over 12..18.
        let items = complete(&both, "    ref w : Widget;", 15);
        let widget = find(&items, "Widget", CLASS);
        assert_eq!(
            widget["textEdit"],
            serde_json::json!({"newText": "Widget", "insert": range(12, 15),
                               "replace": range(12, 18)})
        );
        assert_eq!(
            widget["additionalTextEdits"][0]["newText"], "private import MiniLib::Widget;\n    ",
            "the import rides as before"
        );
        // A keyword: `pa|rt` over 4..8.
        let items = complete(&both, "    part w : Widget;", 6);
        let part = find(&items, "part", KEYWORD);
        assert_eq!(
            part["textEdit"],
            serde_json::json!({"newText": "part", "insert": range(4, 6),
                               "replace": range(4, 8)})
        );
        let items = complete(&insert_only, "    ref w : Widget;", 15);
        assert!(find(&items, "Widget", CLASS)["textEdit"].is_null());
        let items = complete(&insert_only, "    part w : Widget;", 6);
        assert!(find(&items, "part", KEYWORD)["textEdit"].is_null());
        // At a word's end the two ranges would be one: no edit either.
        let items = complete(&both, "    ref w : Widget;", 18);
        assert!(find(&items, "Widget", CLASS)["textEdit"].is_null());
        let items = complete(&both, "    part w : Widget;", 8);
        assert!(find(&items, "part", KEYWORD)["textEdit"].is_null());

        // `[m|s` with the bracket open: the `]` would land where the
        // replacement ends — it rides the main edit with both ranges,
        // and lands behind the word for an inserting client.
        let items = complete(&both, "    attribute g = 9.8 [ms", 24);
        let unit = find(&items, "m/s²", None);
        assert_eq!(
            unit["textEdit"],
            serde_json::json!({"newText": "'m/s²']", "insert": range(23, 24),
                               "replace": range(23, 25)})
        );
        let extras = unit["additionalTextEdits"].as_array().expect("extras");
        assert_eq!(extras.len(), 1, "the import only: {extras:?}");
        let items = complete(&insert_only, "    attribute g = 9.8 [ms", 24);
        let unit = find(&items, "m/s²", None);
        assert_eq!(
            unit["textEdit"],
            serde_json::json!({"newText": "'m/s²'", "range": range(23, 24)})
        );
        assert_eq!(
            unit["additionalTextEdits"][1],
            serde_json::json!({"newText": "]", "range": range(25, 25)})
        );

        // `[m|s.x`: the `]` lands past the chain tail, strictly past
        // either range — kept.
        let items = complete(&both, "    attribute g = 9.8 [ms.x", 24);
        let unit = find(&items, "m/s²", None);
        assert_eq!(
            unit["textEdit"],
            serde_json::json!({"newText": "'m/s²'", "insert": range(23, 24),
                               "replace": range(23, 25)})
        );
        assert_eq!(
            unit["additionalTextEdits"][1],
            serde_json::json!({"newText": "]", "range": range(27, 27)})
        );
    }

    /// An accept landing mid-chain (`fuelTank.over|.volume`) keeps the
    /// tail and inserts nothing behind it: the only extra edit is the
    /// name's import.
    #[test]
    fn accept_mid_chain_adds_no_terminator() {
        // A library feature: the operand an expression names.
        let mut s = PushServer::with_library_sources(
            vec![(
                "MiniLib.kerml".to_string(),
                "standard library package MiniLib { class Widget; feature widgets : Widget; }"
                    .to_string(),
            )],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute g = widge.value\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 23}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widgets = items
            .iter()
            .find(|i| i["label"] == "widgets")
            .expect("widgets");
        let extras = widgets["additionalTextEdits"].as_array().expect("extras");
        assert_eq!(extras.len(), 1, "the import only: {extras:?}");
        assert_eq!(
            extras[0]["newText"],
            "private import MiniLib::widgets;\n    "
        );
        assert!(widgets["textEdit"].is_null(), "plain insertion: {widgets}");
    }

    /// After a feature-chain dot (`oxidizerTank.`) the list is the
    /// members the step can reach — the feature's own body, its
    /// declared type's features, and inherited ones — not the
    /// position-blind pile.
    #[test]
    fn dot_completions_offer_chain_members() {
        let mut s = two_package_server();
        let text = "package P {\n\
                    \x20   part def Vessel {\n\
                    \x20       attribute capacity;\n\
                    \x20   }\n\
                    \x20   part def Tank :> Vessel {\n\
                    \x20       part containedliquid;\n\
                    \x20       attribute liquidMass;\n\
                    \x20   }\n\
                    \x20   part propSys {\n\
                    \x20       part oxidizerTank : Tank {\n\
                    \x20           attribute extra;\n\
                    \x20       }\n\
                    \x20       attribute test = oxidizerTank.\n\
                    \x20   }\n\
                    }\n";
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": text}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 12, "character": 38}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let labels = completion_labels(items);
        assert_eq!(
            labels,
            vec![
                "extra",
                "containedliquid",
                "liquidMass",
                "capacity",
                "metadata"
            ],
            "own body, declared type, then inherited — nothing else"
        );
        let mass = items
            .iter()
            .find(|i| i["label"] == "liquidMass")
            .expect("liquidMass");
        assert!(
            mass["textEdit"].is_null(),
            "plain insertion, no terminator: {mass}"
        );
        assert_eq!(mass["detail"], "P::Tank::liquidMass");

        // Two hops from the enclosing package scope.
        let two = text.replace(
            "attribute test = oxidizerTank.",
            "attribute test = propSys.oxidizerTank.",
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                "contentChanges": [{"text": two}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 12, "character": 46}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        assert_eq!(
            completion_labels(items),
            vec!["extra", "containedliquid", "liquidMass", "capacity"],
            "the chain resolves hop by hop"
        );

        // An unresolvable head offers nothing: after a dot, keywords and
        // the library's names are never what is wanted.
        let broken = text.replace("= oxidizerTank.", "= noSuchTank.");
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 3},
                "contentChanges": [{"text": broken}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 12, "character": 36}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        assert!(items.is_empty(), "nothing to offer: {items:?}");
    }

    /// The model the member-access tests complete in; `§` marks where
    /// the statement being typed goes.
    const VEHICLES: &str = "package P {\n\
                            \x20   port def FuelPort { out item fuel; }\n\
                            \x20   part def Wheel { attribute diameter; }\n\
                            \x20   part def Vehicle {\n\
                            \x20       attribute mass;\n\
                            \x20       port fuelIn : ~FuelPort;\n\
                            \x20       part wheels : Wheel [4];\n\
                            \x20   }\n\
                            \x20   part vehicle1 : Vehicle;\n\
                            \x20   attribute def Energy { attribute joules; }\n\
                            \x20   attribute def Scalar;\n\
                            \x20   calc def KineticEnergy { in m; in v; return : Energy; }\n\
                            \x20   calc def Ratio { in a; in b; return : Scalar; }\n\
                            \x20   part def Q {\n\
                            \x20       port fp : ~FuelPort;\n\
                            \x20       calc k : KineticEnergy;\n\
                            \x20       §\n\
                            \x20   }\n\
                            }\n";

    /// The labels completion offers at the `|` in `marked`, opened as
    /// `uri` on `s` (utf-8 positions, as the fixture negotiates).
    fn labels_at_mark_in(s: &mut PushServer, uri: &str, marked: &str) -> Vec<String> {
        completion_labels(&items_at_mark_in(s, uri, marked))
            .into_iter()
            .map(str::to_string)
            .collect()
    }

    /// The items completion offers at the `|` in `marked` (see
    /// [`labels_at_mark_in`]).
    fn items_at_mark_in(s: &mut PushServer, uri: &str, marked: &str) -> Vec<serde_json::Value> {
        let at = marked.find('|').expect("a cursor mark");
        let line = marked[..at].matches('\n').count();
        let character = at - marked[..at].rfind('\n').map_or(0, |i| i + 1);
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "sysml", "version": 1,
                                 "text": marked.replacen('|', "", 1)}}}),
        );
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": line, "character": character}}}),
        );
        completion_items(&out[0]["result"])
    }

    /// [`labels_at_mark_in`] on a fresh server, `statement` typed at
    /// [`VEHICLES`]' mark.
    fn vehicle_labels(statement: &str) -> Vec<String> {
        let mut s = two_package_server();
        labels_at_mark_in(
            &mut s,
            "file:///w/m.sysml",
            &VEHICLES.replace('§', statement),
        )
    }

    /// A closing brace after the cursor on the same line closes the body
    /// around the statement being typed: the completion session cuts
    /// the statement and keeps the brace.
    #[test]
    fn member_access_before_a_closing_brace_on_the_same_line() {
        for statement in [
            "assert constraint { vehicle1.| }",
            "assert constraint { vehicle1.|}",
            "part def R { attribute m = vehicle1.| }",
        ] {
            assert_eq!(
                vehicle_labels(statement),
                ["mass", "fuelIn", "wheels", "metadata"],
                "{statement}"
            );
        }
    }

    /// Syntax errors elsewhere — an earlier statement of the document, a
    /// body left open above, another unit — do not switch member
    /// completion off.
    #[test]
    fn member_access_survives_syntax_errors_elsewhere() {
        let typed = VEHICLES.replace('§', "attribute m = vehicle1.|");
        for broken in [
            typed.replace(
                "    part def Q {\n",
                "    part def Broken {\n        attribute x = ;\n    }\n    part def Q {\n",
            ),
            typed.replace(
                "    part def Q {\n",
                "    part def Broken {\n        attribute x;\n    part def Q {\n",
            ),
        ] {
            let mut s = two_package_server();
            assert_eq!(
                labels_at_mark_in(&mut s, "file:///w/m.sysml", &broken),
                ["mass", "fuelIn", "wheels", "metadata"],
                "{broken}"
            );
        }
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/other.kerml", "languageId": "kerml",
                                 "version": 1, "text": "package K {\n    feature m\n"}}}),
        );
        assert_eq!(
            labels_at_mark_in(&mut s, "file:///w/m.sysml", &typed),
            ["mass", "fuelIn", "wheels", "metadata"],
            "another unit that does not parse"
        );
    }

    /// A member the parser cannot read elsewhere in the document — a
    /// value left out before its `;` (which then reads as a value), a
    /// group or a name left open at the end of a line — leaves the rest
    /// of the document in the completion model: member access still
    /// reaches the declared and the inherited members, above the broken
    /// member and below it.
    #[test]
    fn member_access_survives_an_unreadable_member_elsewhere() {
        let text = "package P {\n\
                    \x20   part def Vessel { attribute capacity; }\n\
                    \x20   part def Tank :> Vessel { attribute liquidMass; }\n\
                    \x20   §\n\
                    \x20   part tank : Tank;\n\
                    \x20   part def Q {\n\
                    \x20       attribute t = tank.|\n\
                    \x20       ¶\n\
                    \x20   }\n\
                    }\n";
        for broken in [
            "part z { attribute = ; }",
            "part z { attribute q = (1 + ; }",
            "perform action a { in x = ; }",
            "attribute q = (1 + ;",
            "attribute q = f(1, ;",
            "attribute m = 5 [kg",
            "attribute q = tank.",
            "part x : Tank::",
        ] {
            for (above, below) in [(broken, ""), ("", broken)] {
                let mut s = two_package_server();
                let marked = text.replace('§', above).replace('¶', below);
                assert_eq!(
                    labels_at_mark_in(&mut s, "file:///w/m.sysml", &marked),
                    ["liquidMass", "capacity", "metadata"],
                    "{marked}"
                );
            }
        }
    }

    /// A port typed by a conjugated port definition (`~FuelPort`) has
    /// the original definition's features.
    #[test]
    fn member_access_follows_conjugated_port_types() {
        assert_eq!(vehicle_labels("ref f = vehicle1.fuelIn.|"), ["fuel"]);
        assert_eq!(vehicle_labels("ref x = fp.|"), ["fuel", "metadata"]);
    }

    /// An indexed feature's elements have the feature's own type, and an
    /// invocation evaluates to its callee's result — through a usage
    /// typed by the callee too; a result type without features offers
    /// nothing.
    #[test]
    fn member_access_after_an_index_or_an_invocation() {
        assert_eq!(
            vehicle_labels("attribute d = vehicle1.wheels#(1).|"),
            ["diameter"]
        );
        assert_eq!(
            vehicle_labels("attribute d = vehicle1.wheels#(1).dia|"),
            ["diameter"]
        );
        assert_eq!(
            vehicle_labels("attribute e = KineticEnergy(1, 2).|"),
            ["joules"]
        );
        assert_eq!(vehicle_labels("attribute e = k(1, 2).|"), ["joules"]);
        assert!(vehicle_labels("attribute r = Ratio(1, 2).|").is_empty());
    }

    /// A receiver whose head is qualified resolves as written, not by its
    /// last segment alone.
    #[test]
    fn member_access_through_a_qualified_head() {
        assert_eq!(
            vehicle_labels("attribute d = P::Vehicle::wheels.|"),
            ["diameter", "metadata"]
        );
        assert_eq!(
            vehicle_labels("attribute d = P::vehicle1.wheels.|"),
            ["diameter"]
        );
        // The same name nearer the cursor does not capture it.
        let mut s = two_package_server();
        let text = VEHICLES
            .replace(
                "    part vehicle1 : Vehicle;\n",
                "    part vehicle1 : Vehicle;\n    package Inner { part vehicle1 : Wheel; }\n",
            )
            .replace('§', "attribute d = Inner::vehicle1.|");
        assert_eq!(
            labels_at_mark_in(&mut s, "file:///w/m.sysml", &text),
            ["diameter", "metadata"]
        );
        // Rooted at the global namespace (`$::`, as a lifted model spells
        // it): past a nearer declaration of the same name.
        let mut s = two_package_server();
        let text = format!(
            "part def W {{ attribute d; }}\npart vehicle1 : W;\n{}",
            VEHICLES.replace('§', "attribute d = $::vehicle1.|")
        );
        assert_eq!(
            labels_at_mark_in(&mut s, "file:///w/m.sysml", &text),
            ["d", "metadata"]
        );
        assert_eq!(
            vehicle_labels("attribute d = $::P::vehicle1.wheels.|"),
            ["diameter"]
        );
    }

    /// A receiver named by a reference also takes the `metadata` keyword
    /// of a metadata access (`vehicle1.metadata`), listed after its
    /// members; a package, a chain step, or a name that does not resolve
    /// does not.
    #[test]
    fn member_access_offers_metadata_after_a_reference() {
        let mut s = two_package_server();
        let items = items_at_mark_in(
            &mut s,
            "file:///w/m.sysml",
            &VEHICLES.replace('§', "attribute m = vehicle1.|"),
        );
        let metadata = items.last().expect("items");
        assert_eq!(metadata["label"], "metadata");
        assert_eq!(metadata["kind"], 14, "a keyword: {metadata}");
        // Listed after every member, which keep their labels' order.
        for member in &items[..items.len() - 1] {
            let label = member["label"].as_str().expect("a label");
            assert_eq!(member["sortText"], format!("0{label}"));
            assert!(
                member["sortText"].as_str() < metadata["sortText"].as_str(),
                "{member} after {metadata}"
            );
        }
        // A package's dot is usually a slip for `::`: nothing there.
        assert!(vehicle_labels("attribute m = P.|").is_empty());
        assert_eq!(
            vehicle_labels("attribute m = vehicle1.wheels.|"),
            ["diameter"]
        );
        assert!(vehicle_labels("attribute m = noSuch.|").is_empty());
    }

    /// A member name typed quoted right after the dot (`vehicle1.'ma|`,
    /// or `vehicle1.'ma|'` where an editor closes quotes) lists the
    /// receiver's members, accepting one replacing the quoted name.
    #[test]
    fn member_access_takes_a_member_typed_quoted() {
        for (statement, end) in [
            ("attribute m = vehicle1.'ma|", 34),
            ("attribute m = vehicle1.'ma|'", 35),
        ] {
            let text = VEHICLES.replace('§', statement);
            let line = text[..text.find('|').expect("a cursor mark")]
                .matches('\n')
                .count();
            let mut s = two_package_server();
            let items = items_at_mark_in(&mut s, "file:///w/m.sysml", &text);
            assert_eq!(
                completion_labels(&items),
                ["mass", "fuelIn", "wheels"],
                "{statement}"
            );
            // The quote opens at 31, after `        attribute m = vehicle1.`.
            assert_eq!(
                items[0]["textEdit"],
                serde_json::json!({
                    "range": {"start": {"line": line, "character": 31},
                              "end": {"line": line, "character": end}},
                    "newText": "mass"
                }),
                "{statement}"
            );
        }
    }

    /// In KerML a receiver may use a word the SysML notation reserves as
    /// a name (`part`): it is read in the document's own dialect.
    #[test]
    fn member_access_reads_a_kerml_receiver_in_kerml() {
        let mut s = two_package_server();
        assert_eq!(
            labels_at_mark_in(
                &mut s,
                "file:///w/k.kerml",
                "package K {\n    classifier Wheel { feature diameter; }\n    \
                 feature part : Wheel[4];\n    feature d = part#(1).|\n}\n",
            ),
            ["diameter"]
        );
    }

    /// A member an owned feature redefines is offered once, as the
    /// redefinition (an unnamed `:>> mass` keyed by the name it
    /// redefines); a private member of the type is not offered.
    #[test]
    fn member_access_offers_a_redefinition_once_and_no_private_members() {
        let text = VEHICLES
            .replace(
                "    part vehicle1 : Vehicle;\n",
                "    part vehicle1 : Vehicle { attribute :>> mass = 1500; }\n",
            )
            .replace(
                "        attribute mass;\n",
                "        attribute mass;\n        private attribute secret;\n",
            )
            .replace('§', "attribute m = vehicle1.|");
        let mut s = two_package_server();
        let items = items_at_mark_in(&mut s, "file:///w/m.sysml", &text);
        assert_eq!(
            completion_labels(&items),
            ["mass", "fuelIn", "wheels", "metadata"]
        );
        assert_eq!(items[0]["detail"], "P::vehicle1::mass");
    }

    /// A unit that does not parse still contributes the declarations
    /// around its error: a receiver typed by a definition declared there
    /// lists that definition's features.
    #[test]
    fn member_access_reaches_types_declared_in_a_unit_that_does_not_parse() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/other.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package O {\n    part def Tank { attribute level; }\n    attribute broken = ;\n}\n"}}}),
        );
        assert_eq!(
            labels_at_mark_in(
                &mut s,
                "file:///w/m.sysml",
                "package M {\n    private import O::*;\n    part t : Tank;\n    attribute x = t.|\n}\n",
            ),
            ["level", "metadata"]
        );
    }

    /// A declaration whose `;` is still missing counts as declared, the
    /// way the parser reads it: a receiver it declares lists members.
    #[test]
    fn member_access_reaches_a_declaration_missing_its_terminator() {
        let text = VEHICLES
            .replace("port fp : ~FuelPort;", "port fp : ~FuelPort")
            .replace('§', "ref x = fp.|");
        let mut s = two_package_server();
        assert_eq!(
            labels_at_mark_in(&mut s, "file:///w/m.sysml", &text),
            ["fuel", "metadata"]
        );
    }

    /// A quantity's unit bracket offers units and nothing else: no
    /// keywords, no other names. The fixture library's one unit is
    /// offered by its short symbol first.
    #[test]
    fn unit_brackets_offer_only_units() {
        for marked in [
            "package P {\n    attribute g = 9.8 [|\n}\n",
            "package P {\n    attribute g = 9.8 [|];\n}\n",
            "package P {\n    part def V { attribute m; assert constraint { m <= 2 [| } }\n}\n",
        ] {
            let mut s = two_package_server();
            assert_eq!(
                labels_at_mark_in(&mut s, "file:///w/m.sysml", marked),
                ["m/s²", "metre per second squared"],
                "{marked:?}"
            );
        }
        // A qualifier there lists its namespace's units alone.
        let mut s = two_package_server();
        let labels = labels_at_mark_in(
            &mut s,
            "file:///w/m.sysml",
            "package P {\n    attribute g = 9.8 [MiniLib::|\n}\n",
        );
        assert!(labels.contains(&"m/s²".to_string()), "{labels:?}");
        assert!(!labels.contains(&"Widget".to_string()), "{labels:?}");
    }

    /// A `[` that opens a multiplicity or an import's filter, or none at
    /// all (in a comment or a string), offers nothing: an editor that
    /// opens a list on `[` shows none there.
    #[test]
    fn brackets_without_a_unit_offer_nothing() {
        for marked in [
            "package P {\n    part w : Widget [|\n}\n",
            "package P {\n    part w : Widget[|]\n}\n",
            "package P {\n    part w : Widget [0..|\n}\n",
            "package P {\n    part w : Widget [1|\n}\n",
            "package P {\n    part w : Widget [0..5|\n}\n",
            "package P {\n    part w [|\n}\n",
            "package P {\n    attribute a : Widget [1] = 5; part w : Widget [|\n}\n",
            "package P {\n    private import MiniLib::*[|\n}\n",
            "package P {\n    doc /* see [| */\n}\n",
            "package P {\n    attribute s = \"a [|\";\n}\n",
        ] {
            let mut s = two_package_server();
            let labels = labels_at_mark_in(&mut s, "file:///w/m.sysml", marked);
            assert!(labels.is_empty(), "{marked:?}: {labels:?}");
        }
    }

    /// A multiplicity's bound may name a feature (`[1..numberOfBolts]`),
    /// and a filter a metadata definition: once a name is typed there,
    /// names are offered again — but no unit's long name, which only a
    /// unit bracket takes.
    #[test]
    fn a_name_typed_in_a_bound_or_a_filter_is_completed() {
        let mut s = two_package_server();
        let labels = labels_at_mark_in(
            &mut s,
            "file:///w/m.sysml",
            "package P {\n    attribute count;\n    part w : Widget [1..co|\n}\n",
        );
        assert!(labels.contains(&"count".to_string()), "{labels:?}");
        assert!(
            !labels.contains(&"metre per second squared".to_string()),
            "{labels:?}"
        );
        let mut s = two_package_server();
        let labels = labels_at_mark_in(
            &mut s,
            "file:///w/m.sysml",
            "package P {\n    view def V { expose MiniLib::**[@Wid| }\n}\n",
        );
        assert!(labels.contains(&"Widget".to_string()), "{labels:?}");
    }

    /// `[` opens completion like `:` and `.` do.
    #[test]
    fn a_bracket_triggers_completion() {
        let mut s = PushServer::new();
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        let triggers = &out[0]["result"]["capabilities"]["completionProvider"]["triggerCharacters"];
        assert_eq!(triggers, &serde_json::json!([":", ".", "["]));
    }

    /// An unresolved-reference diagnostic offers exact-name import
    /// quick fixes — for quoted restricted references included.
    #[test]
    fn code_action_offers_import_for_unresolved_reference() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    part w : Widget;\n}\n"}}}),
        );
        let range = serde_json::json!({"start": {"line": 1, "character": 13},
                                       "end": {"line": 1, "character": 19}});
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range, "message": "unresolved reference `Widget`"}]}}}),
        );
        let actions = out[0]["result"].as_array().expect("actions");
        let fix = actions
            .iter()
            .find(|a| a["title"] == "Add import MiniLib::Widget")
            .expect("import quick fix offered");
        assert_eq!(fix["isPreferred"], true);
        let edit = &fix["edit"]["changes"]["file:///w/m.sysml"][0];
        assert_eq!(edit["newText"], "private import MiniLib::Widget;\n    ");
        assert_eq!(
            edit["range"]["start"],
            serde_json::json!({"line": 1, "character": 4})
        );

        // Quoted reference: the diagnostic starts at the quote.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                "contentChanges": [
                    {"text": "package P {\n    attribute g = 9.8 ['m/s²'];\n}\n"}]}}),
        );
        let range = serde_json::json!({"start": {"line": 1, "character": 23},
                                       "end": {"line": 1, "character": 29}});
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range, "message": "unresolved reference `m/s²`"}]}}}),
        );
        let actions = out[0]["result"].as_array().expect("actions");
        let fix = actions
            .iter()
            .find(|a| a["title"] == "Add import MiniLib::'m/s²'")
            .expect("quoted import quick fix offered");
        let edit = &fix["edit"]["changes"]["file:///w/m.sysml"][0];
        assert_eq!(edit["newText"], "private import MiniLib::'m/s²';\n    ");
    }

    /// The import quick fix sees the SEEDED workspace, not just open
    /// documents — the declaring unit is usually not open in a tab.
    #[test]
    fn code_action_offers_import_from_seeded_workspace_unit() {
        let mut s = two_package_server();
        s.set_workspace_sources(vec![
            (
                "file:///w/vehicle.sysml".to_string(),
                "package Vehicle { part def Engine; }".to_string(),
            ),
            (
                "file:///w/m.sysml".to_string(),
                "package P {\n    part e : Engine;\n}\n".to_string(),
            ),
        ]);
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    part e : Engine;\n}\n"}}}),
        );
        let range = serde_json::json!({"start": {"line": 1, "character": 13},
                                       "end": {"line": 1, "character": 19}});
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range, "message": "unresolved reference `Engine`"}]}}}),
        );
        let actions = out[0]["result"].as_array().expect("actions");
        assert!(
            actions
                .iter()
                .any(|a| a["title"] == "Add import Vehicle::Engine"),
            "seeded-unit import fix offered: {actions:?}"
        );
    }

    /// No import quick fix when the unresolved reference IS an import
    /// path — the import's target is missing from the model, and
    /// inserting another import statement cannot make it resolve.
    #[test]
    fn code_action_no_import_fix_inside_import_statement() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    private import Widget;\n}\n"}}}),
        );
        let range = serde_json::json!({"start": {"line": 1, "character": 19},
                                       "end": {"line": 1, "character": 25}});
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range, "message": "unresolved reference `Widget`"}]}}}),
        );
        let actions = out[0]["result"].as_array().expect("actions");
        assert!(
            !actions.iter().any(|a| a["title"]
                .as_str()
                .is_some_and(|t| t.starts_with("Add import"))),
            "no import fix on an import path: {actions:?}"
        );
    }

    /// A `;` where none belongs — after a body's result expression, or
    /// standing where a member would start (`;;`, `{ … };`) — is
    /// removed by a preferred quick fix riding the error the server
    /// published on it. A `;` an error sits on that the statement still
    /// needs (`part p : ;`) gets none.
    #[test]
    fn code_action_removes_a_stray_terminator() {
        let fixes = |text: &str| -> Vec<(String, serde_json::Value)> {
            let mut s = two_package_server();
            let opened = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let published = opened
                .iter()
                .find(|m| m["method"] == "textDocument/publishDiagnostics")
                .expect("diagnostics published");
            let diagnostics = published["params"]["diagnostics"].clone();
            let mut out = Vec::new();
            for d in diagnostics.as_array().expect("diagnostics") {
                let answer = responses(
                    &mut s,
                    &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/codeAction",
                        "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                                   "range": d["range"],
                                   "context": {"diagnostics": [d]}}}),
                );
                for a in answer[0]["result"].as_array().expect("actions") {
                    if a["title"] == "Remove `;`" {
                        assert_eq!(a["isPreferred"], true, "{a}");
                        let edit = &a["edit"]["changes"]["file:///w/m.sysml"][0];
                        out.push((d["message"].as_str().unwrap().to_string(), edit.clone()));
                    }
                }
            }
            out
        };
        let removal = |line: u32, character: u32| {
            serde_json::json!({"range": {"start": {"line": line, "character": character},
                                         "end": {"line": line, "character": character + 1}},
                               "newText": ""})
        };

        let found = fixes(
            "part def P {\n    attribute mass;\n    assert constraint {\n        mass <= 2;\n    }\n}\n",
        );
        assert_eq!(
            found,
            vec![(
                sysmlv2_parser::parser::RESULT_EXPRESSION_TERMINATOR.to_string(),
                removal(3, 17)
            )]
        );
        for (text, line, character) in [
            (
                "package P {\n    part def A;;\n    part def B;\n}\n",
                1u32,
                15u32,
            ),
            ("package P {\n    part def A {\n    };\n}\n", 2, 5),
            ("package P {\n    part def A; /* note */ ;\n}\n", 1, 27),
        ] {
            let found = fixes(text);
            assert_eq!(found.len(), 1, "{text:?}: {found:?}");
            assert_eq!(found[0].1, removal(line, character), "{text:?}");
        }
        // An error expecting something else at the `;` leaves it: the
        // statement ends there, and what is missing comes before it.
        for text in [
            "package P {\n    part p : ;\n}\n",
            "package P {\n    calc def f { in g; g }\n    attribute a = f({ in x; x };\n}\n",
            "package P {\n    attribute xs : ScalarValues::Real[*];\n    attribute a = (xs->select { in x; x > 0 };\n}\n",
        ] {
            let found = fixes(text);
            assert!(found.is_empty(), "{text:?}: {found:?}");
        }
    }

    /// Completion and signature help cut the same statement out of the
    /// model they read, so alternating between them at one position
    /// builds one session — an expression's body passed as an argument
    /// ahead of the cursor included (`Twice({ in z; z }, v.|`), which
    /// leaves the statement around it whole for completion too.
    #[test]
    fn completion_and_signature_help_share_one_session() {
        let text = "package P {\n    calc def Twice { in f; in x; }\n    \
                    part def V { attribute w; }\n    part def U {\n        part v : V;\n        \
                    attribute a = Twice({ in z; z }, v.\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/p.sysml";
        put(&mut s, uri, 1, text);
        // After `v.`.
        let at = serde_json::json!({"line": 5, "character": 43});
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        for id in 0..2 {
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 10 + id, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": uri}, "position": at}}),
            );
            let items = out[0]["result"].as_array().cloned().unwrap_or_default();
            assert!(items.iter().any(|i| i["label"] == "w"), "{}", out[0]);
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 20 + id, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": uri}, "position": at}}),
            );
            let help = &out[0]["result"];
            assert_eq!(help["signatures"][0]["label"], "Twice(f, x)", "{help}");
            assert_eq!(help["activeParameter"], 1, "{help}");
        }
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 1);
    }

    /// In an invocation's argument list the server answers with the
    /// invoked callable's signature — the hover card's line — and the
    /// parameter the argument being typed binds, by position or by
    /// name; parameters are label offsets for a client that takes them.
    /// Outside an argument list, or for a name that calls nothing,
    /// there is no answer.
    #[test]
    fn signature_help_names_the_parameter_being_typed() {
        const MODEL: &str = "package P {\n\
                             \x20   attribute def Mass;\n\
                             \x20   attribute def Speed;\n\
                             \x20   attribute def Energy;\n\
                             \x20   calc def KineticEnergy {\n\
                             \x20       doc /* The energy of a moving mass. */\n\
                             \x20       in m : Mass;\n\
                             \x20       in v : Speed;\n\
                             \x20       return : Energy;\n\
                             \x20   }\n\
                             \x20   constraint def Positive { in x : Mass; }\n\
                             \x20   part def V {\n\
                             \x20       LINE\n\
                             \x20   }\n\
                             }\n";
        let help = |caps: &serde_json::Value, line: &str| -> serde_json::Value {
            let mut s = two_package_server_with_caps(caps);
            let character = u32::try_from(line.find('|').expect("cursor") + 8).unwrap();
            let text = MODEL.replace("LINE", &line.replace('|', ""));
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 12, "character": character}}}),
            );
            out[0]["result"].clone()
        };
        let plain = serde_json::json!({"general": {"positionEncodings": ["utf-8"]}});
        let offsets = serde_json::json!({
            "general": {"positionEncodings": ["utf-8"]},
            "textDocument": {"signatureHelp": {"signatureInformation": {
                "parameterInformation": {"labelOffsetSupport": true}}}}});

        let h = help(&plain, "attribute e = KineticEnergy(m, |");
        let sig = &h["signatures"][0];
        assert_eq!(sig["label"], "KineticEnergy(m: Mass, v: Speed) → Energy");
        assert_eq!(
            sig["parameters"],
            serde_json::json!([{"label": "m: Mass"}, {"label": "v: Speed"}])
        );
        assert_eq!(
            sig["documentation"]["value"],
            "The energy of a moving mass."
        );
        assert_eq!(h["activeParameter"], 1);
        let h = help(&offsets, "attribute e = KineticEnergy(|");
        assert_eq!(
            h["signatures"][0]["parameters"],
            serde_json::json!([{"label": [14, 21]}, {"label": [23, 31]}])
        );
        assert_eq!(h["activeParameter"], 0);
        let h = help(&plain, "attribute e = KineticEnergy(v = 2, m = |");
        assert_eq!(h["activeParameter"], 0, "{h}");
        // A body closing on the cursor's line stays in the model.
        let h = help(&plain, "assert constraint { Positive(|) }");
        assert_eq!(h["signatures"][0]["label"], "Positive(x: Mass)", "{h}");
        // A usage declaring no parameters of its own calls with its
        // definition's, under its own name.
        let h = help(&plain, "calc ke : KineticEnergy; attribute e = ke(m, |");
        assert_eq!(
            h["signatures"][0]["label"], "ke(m: Mass, v: Speed) → Energy",
            "{h}"
        );
        assert_eq!(h["activeParameter"], 1);
        // Documented nowhere itself, it reads its definition's.
        assert_eq!(
            h["signatures"][0]["documentation"]["value"],
            "The energy of a moving mass."
        );
        // A declared multiplicity other than one follows the type, as a
        // library callable's does.
        let h = help(
            &plain,
            "calc def Many { in xs : Mass[0..*]; in one : Mass[1]; } attribute e = Many(|",
        );
        assert_eq!(
            h["signatures"][0]["label"], "Many(xs: Mass[0..*], one: Mass)",
            "{h}"
        );
        // Parameters inherited follow the callable's own — a definition
        // specializing another, a usage typed by one — each redefined
        // one replaced by what redefines it, by name, explicitly, or by
        // position; the result is the closest declaration's.
        for (line, label) in [
            (
                "calc def KE2 :> KineticEnergy; attribute e = KE2(m, |",
                "KE2(m: Mass, v: Speed) → Energy",
            ),
            (
                "calc def KE2 :> KineticEnergy; calc ke2 : KE2; attribute e = ke2(m, |",
                "ke2(m: Mass, v: Speed) → Energy",
            ),
            (
                "attribute def Heavy :> Mass; \
                 calc def KE3 :> KineticEnergy { in m : Heavy; } attribute e = KE3(m, |",
                "KE3(m: Heavy, v: Speed) → Energy",
            ),
            (
                "attribute def Heavy :> Mass; \
                 calc def KE4 :> KineticEnergy { in :>> m : Heavy; } attribute e = KE4(m, |",
                "KE4(m: Heavy, v: Speed) → Energy",
            ),
            (
                "attribute def Heavy :> Mass; \
                 calc def KE5 :> KineticEnergy { in mass : Heavy; } attribute e = KE5(m, |",
                "KE5(mass: Heavy, v: Speed) → Energy",
            ),
            (
                "attribute def Joules :> Energy; \
                 calc def KE7 :> KineticEnergy { return : Joules; } attribute e = KE7(m, |",
                "KE7(m: Mass, v: Speed) → Joules",
            ),
            // Redefining only, it reads with the type it redefines; unnamed
            // in an inherited parameter's place, with that one's name.
            (
                "calc def KE8 :> KineticEnergy { in :>> m; } attribute e = KE8(m, |",
                "KE8(m: Mass, v: Speed) → Energy",
            ),
            (
                "attribute def Heavy :> Mass; \
                 calc def KE9 :> KineticEnergy { in : Heavy; } attribute e = KE9(m, |",
                "KE9(m: Heavy, v: Speed) → Energy",
            ),
        ] {
            let h = help(&plain, line);
            assert_eq!(h["signatures"][0]["label"], label, "{line:?}: {h}");
            assert_eq!(h["activeParameter"], 1, "{line:?}");
        }
        // The parameters an evaluation binds. An own parameter takes over
        // the general's at its place even when it redefines another one
        // explicitly, so `KE6` has one parameter that both of
        // `KineticEnergy`'s stand for; and a place pairs with the general's
        // parameters, its own then the inherited ones after them, so `b`
        // takes over the `v` that `KE3` inherits.
        for (line, label) in [
            (
                "calc def KE6 :> KineticEnergy { in :>> v; } attribute e = KE6(|",
                "KE6(v: Speed) → Energy",
            ),
            (
                "attribute def Heavy :> Mass; \
                 calc def KE3 :> KineticEnergy { in m : Heavy; } \
                 calc def KE10 :> KE3 { in a : Heavy; in b : Speed; } attribute e = KE10(|",
                "KE10(a: Heavy, b: Speed) → Energy",
            ),
        ] {
            let h = help(&plain, line);
            assert_eq!(h["signatures"][0]["label"], label, "{line:?}: {h}");
            assert_eq!(h["activeParameter"], 0, "{line:?}");
        }
        // Arguments bind the inputs, in order: an output declared among
        // them holds no argument's place.
        let h = help(
            &plain,
            "calc def Mixed { out o : Energy; in m : Mass; in v : Speed; } attribute e = Mixed(m, |",
        );
        assert_eq!(
            h["signatures"][0]["label"], "Mixed(out o: Energy, m: Mass, v: Speed)",
            "{h}"
        );
        assert_eq!(h["activeParameter"], 2, "{h}");
        let h = help(
            &plain,
            "calc def Mixed { out o : Energy; in m : Mass; in v : Speed; } attribute e = Mixed(o = |",
        );
        assert_eq!(h["activeParameter"], 3, "{h}");
        // An inherited parameter named.
        let h = help(
            &plain,
            "calc def KE2 :> KineticEnergy; attribute e = KE2(v = |",
        );
        assert_eq!(h["activeParameter"], 1, "{h}");
        // Documented nowhere itself, a definition reads the one it
        // specializes.
        assert_eq!(
            h["signatures"][0]["documentation"]["value"],
            "The energy of a moving mass."
        );
        // An unnamed usage redefining one, reached on a chain, is called
        // by the name it redefines.
        let h = help(
            &plain,
            "part def Holder { calc ke : KineticEnergy; } part h2 : Holder { calc :>> ke; } \
             attribute e = h2.ke(m, |",
        );
        assert_eq!(
            h["signatures"][0]["label"], "ke(m: Mass, v: Speed) → Energy",
            "{h}"
        );
        // A feature chain's step: a member of what its receiver reaches.
        let h = help(
            &plain,
            "part w { calc ke : KineticEnergy; } attribute e = w.ke(m, |",
        );
        assert_eq!(
            h["signatures"][0]["label"], "ke(m: Mass, v: Speed) → Energy",
            "{h}"
        );
        assert_eq!(h["activeParameter"], 1);
        // After a body expression passed as an argument, and past a
        // string holding a statement's punctuation.
        for line in [
            "attribute e = KineticEnergy({ in z; z }, |",
            "attribute e = KineticEnergy(\"a;b}\", |",
        ] {
            let h = help(&plain, line);
            assert_eq!(
                h["signatures"][0]["label"], "KineticEnergy(m: Mass, v: Speed) → Energy",
                "{line:?}: {h}"
            );
            assert_eq!(h["activeParameter"], 1, "{line:?}");
        }

        for line in [
            "attribute e = KineticEnergy(m, v)|",
            "attribute e = Mass(|",
            "attribute e = Unknown(|",
        ] {
            assert!(help(&plain, line).is_null(), "{line:?}");
        }

        // KerML: a function invoked in a feature value.
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/k.kerml", "languageId": "kerml", "version": 1,
                                 "text": "package K {\n    classifier Num;\n    function Twice { in x : Num; return : Num; }\n    feature y = Twice(\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/signatureHelp",
                "params": {"textDocument": {"uri": "file:///w/k.kerml"},
                           "position": {"line": 3, "character": 22}}}),
        );
        assert_eq!(
            out[0]["result"]["signatures"][0]["label"],
            "Twice(x: Num) → Num"
        );
        // A function specializing another: its general's parameters,
        // one of its own taking the place of the general's at its
        // position.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/s.kerml", "languageId": "kerml", "version": 1,
                                 "text": "package S {\n    classifier Num;\n    function Twice { in x : Num; return : Num; }\n    function Again specializes Twice;\n    function Other specializes Twice { in y : Num; }\n    feature a = Again(\n    feature b = Other(\n}\n"}}}),
        );
        for (line, label) in [(5, "Again(x: Num) → Num"), (6, "Other(y: Num) → Num")] {
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": "file:///w/s.kerml"},
                               "position": {"line": line, "character": 22}}}),
            );
            assert_eq!(out[0]["result"]["signatures"][0]["label"], label);
        }
        // A feature typed by a function, reached on a chain.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/c.kerml", "languageId": "kerml", "version": 1,
                                 "text": "package C {\n    classifier Num;\n    function Twice { in x : Num; return : Num; }\n    classifier Holder { feature double : Twice; }\n    feature h : Holder;\n    feature y = h.double(\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/signatureHelp",
                "params": {"textDocument": {"uri": "file:///w/c.kerml"},
                           "position": {"line": 5, "character": 25}}}),
        );
        assert_eq!(
            out[0]["result"]["signatures"][0]["label"],
            "double(x: Num) → Num"
        );

        let caps = crate::capabilities(crate::Encoding::Utf8);
        let triggers = caps
            .signature_help_provider
            .and_then(|o| o.trigger_characters)
            .unwrap_or_default();
        assert_eq!(triggers, ["(", ","]);
    }

    fn two_package_server() -> PushServer {
        two_package_server_with_caps(&serde_json::json!(
            {"general": {"positionEncodings": ["utf-8"]}}))
    }

    fn two_package_server_with_caps(capabilities: &serde_json::Value) -> PushServer {
        let mut s = PushServer::with_library_sources(
            vec![(
                "MiniLib.kerml".to_string(),
                "standard library package MiniLib { class Widget; class Gadget; \
                 feature <'m/s²'> 'metre per second squared' \
                 : MeasurementReferences::TensorMeasurementReference; } \
                 standard library package OtherLib { class Bolt; } \
                 standard library package MeasurementReferences { \
                 datatype TensorMeasurementReference; }"
                    .to_string(),
            )],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": capabilities}}),
        );
        s
    }

    fn completion_labels(items: &[serde_json::Value]) -> Vec<&str> {
        items.iter().filter_map(|i| i["label"].as_str()).collect()
    }

    /// The items of a completion response: an array, or the items of a
    /// list sent incomplete for the client to ask again as the user
    /// types.
    fn completion_items(result: &serde_json::Value) -> Vec<serde_json::Value> {
        result
            .as_array()
            .or_else(|| result["items"].as_array())
            .expect("completion items")
            .clone()
    }

    /// After `Foo::`, only the members of `Foo` are offered — no
    /// keywords, no other packages, no workspace names (import and
    /// non-import sites alike).
    #[test]
    fn qualifier_filters_completions_to_members() {
        for (text, character) in [
            // import path: cursor right after `MiniLib::`
            ("package P { part def X; private import MiniLib:: }", 48u32),
            // typed reference: same qualifier handling
            ("package P { part def X; part w : MiniLib:: }", 42u32),
        ] {
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1, "text": text}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 0, "character": character}}}),
            );
            let items = out[0]["result"].as_array().expect("completion items");
            let labels = completion_labels(items);
            assert!(labels.contains(&"Widget"), "member offered: {labels:?}");
            assert!(labels.contains(&"Gadget"), "member offered: {labels:?}");
            assert!(
                !labels.contains(&"Bolt"),
                "other package's member filtered: {labels:?}"
            );
            assert!(
                !labels.contains(&"X"),
                "workspace name filtered: {labels:?}"
            );
            assert!(!labels.contains(&"part"), "keywords filtered: {labels:?}");
        }
    }

    /// Completing a bare name inside an import inserts the full
    /// qualified path over the typed partial word, so the import
    /// resolves as accepted.
    #[test]
    fn import_completion_inserts_full_path() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P { private import Widg }"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 0, "character": 31}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget offered in import context");
        let edit = &widget["textEdit"];
        assert_eq!(edit["newText"], "MiniLib::Widget");
        assert_eq!(edit["range"]["start"]["character"], 27);
        assert_eq!(edit["range"]["end"]["character"], 31);
    }

    /// After a qualifier in an import or expose path the wildcards come
    /// with the members: `*` for the members, `**` for everything below
    /// them, inserted as typed rather than quoted as names. A qualifier
    /// in a reference offers none.
    #[test]
    fn import_paths_offer_wildcards() {
        for (text, character, offered) in [
            (
                "package P {\n    private import MiniLib::\n}\n",
                28u32,
                true,
            ),
            ("package P {\n    view v { expose MiniLib::\n}\n", 29, true),
            ("package P {\n    part w : MiniLib::\n}\n", 22, false),
        ] {
            let mut s = two_package_server();
            let items = completion_in_m(&mut s, text, 1, character);
            assert!(completion_labels(&items).contains(&"Widget"), "{text:?}");
            for wildcard in ["*", "**"] {
                let item = items.iter().find(|i| i["label"] == wildcard);
                assert_eq!(item.is_some(), offered, "{text:?}: `{wildcard}`");
                if let Some(item) = item {
                    assert_eq!(item["textEdit"]["newText"], wildcard, "{item}");
                    assert_eq!(item["textEdit"]["range"]["start"]["character"], character);
                    assert_ne!(
                        item["kind"],
                        serde_json::json!(lsp_types::CompletionItemKind::KEYWORD)
                    );
                }
            }
        }
    }

    /// An import path usually names a package: packages sort ahead of
    /// the members the same word matches, so `Vehi` focuses
    /// `VehicleModel`, not its `Vehicle`. A workspace package is not
    /// annotated as standard library.
    #[test]
    fn import_paths_rank_packages_first() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package VehicleModel {\n    part def Vehicle;\n    \
                                          package VehicleStates;\n    part vehicle1 : Vehicle;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    private import Vehi\n}\n", 1, 23);
        let item = |label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"))
        };
        let sort = |label: &str| item(label)["sortText"].as_str().map(str::to_lowercase);
        for package in ["VehicleModel", "VehicleStates"] {
            for member in ["Vehicle", "vehicle1"] {
                assert!(
                    sort(package).is_some() && sort(package) < sort(member),
                    "{package} before {member}: {:?} {:?}",
                    sort(package),
                    sort(member)
                );
            }
        }
        assert_ne!(item("VehicleModel")["detail"], "standard library");
        assert_eq!(item("MiniLib")["detail"], "standard library");
    }

    /// The wildcards come with an import or expose statement's keyword,
    /// not with the word in a comment or string of another statement.
    #[test]
    fn wildcards_need_an_import_or_expose_keyword() {
        for (text, character) in [
            (
                "package P {\n    part w : /* expose */ MiniLib::\n}\n",
                36u32,
            ),
            ("package P {\n    part w : /* import */ MiniLib::\n}\n", 36),
            (
                "package P {\n    part w : // import\n        MiniLib::\n}\n",
                17,
            ),
        ] {
            let line = u32::try_from(
                text.lines()
                    .position(|l| l.contains("MiniLib::"))
                    .expect("line"),
            )
            .expect("line");
            let mut s = two_package_server();
            let items = completion_in_m(&mut s, text, line, character);
            let labels = completion_labels(&items);
            assert!(labels.contains(&"Widget"), "{text:?}: {labels:?}");
            assert!(!labels.contains(&"*"), "{text:?}: {labels:?}");
        }
    }

    /// An import path offers what a package owns — packages and their
    /// members — never a feature of a definition, such as a
    /// requirement's subject: importing it by path is no way to reach
    /// it.
    #[test]
    fn import_completion_offers_only_package_members() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Model {\n    part def Vehicle { part engine; }\n    \
                                          requirement def MassReq { subject vehicle : Vehicle; }\n    \
                                          part vehicle1 : Vehicle;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    private import veh\n}\n", 1, 22);
        let inserted: Vec<&str> = items
            .iter()
            .filter_map(|i| i["textEdit"]["newText"].as_str())
            .filter(|t| t.starts_with("Model::"))
            .collect();
        assert!(
            inserted.contains(&"Model::Vehicle") && inserted.contains(&"Model::vehicle1"),
            "{inserted:?}"
        );
        for feature in ["Model::MassReq::vehicle", "Model::Vehicle::engine"] {
            assert!(
                !inserted.contains(&feature),
                "`{feature}` offered: {inserted:?}"
            );
        }
    }

    /// Host-seeded workspace sources feed navigation: definition on an
    /// import-introduced name jumps into a unit that was seeded but
    /// never opened (the filesystem-less host's cross-file shape), and
    /// re-seeding replaces the set.
    #[test]
    fn workspace_sources_feed_navigation() {
        let mut s = PushServer::new();
        s.set_workspace_sources(vec![(
            "file:///w/defs.sysml".to_string(),
            "package Defs {\n    part def Wheel;\n}\n".to_string(),
        )]);
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/uses.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Uses {\n    private import Defs::*;\n    part w : Wheel;\n}\n"}}}),
        );
        let definition = |s: &mut PushServer, id: i32| -> serde_json::Value {
            let out = responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": id, "method": "textDocument/definition",
                    "params": {"textDocument": {"uri": "file:///w/uses.sysml"},
                               "position": {"line": 2, "character": 14}}}),
            );
            out[0]["result"].clone()
        };
        let loc = definition(&mut s, 2);
        assert_eq!(loc["uri"], "file:///w/defs.sysml", "{loc:?}");
        assert_eq!(loc["range"]["start"]["line"], 1, "{loc:?}");
        assert_eq!(loc["range"]["start"]["character"], 13, "{loc:?}");

        // Re-seeding replaces the workspace: without Defs the imported
        // name no longer resolves, so definition has nothing to answer.
        s.set_workspace_sources(Vec::new());
        assert_eq!(definition(&mut s, 3), serde_json::Value::Null);
    }

    /// A prepared library answers exactly as the sources it was prepared
    /// from: completions, hover and a definition inside a library unit.
    #[test]
    fn prepared_library_answers_like_its_sources() {
        let units = || {
            vec![(
                "Mini Lib/MiniLib.sysml".to_string(),
                "package MiniLib {\n    part def Widget;\n    part def Gadget;\n}\n".to_string(),
            )]
        };
        let answers = |mut s: PushServer| {
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                    "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
            );
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                     "version": 1,
                                     "text": "package P {\n    private import MiniLib::*;\n    part w : Widget;\n    part def X;\n}\n"}}}),
            );
            // Completion in the typing's position, where the library's
            // definitions are offered.
            [
                ("textDocument/completion", 2, 13),
                ("textDocument/hover", 2, 14),
                ("textDocument/definition", 2, 14),
            ]
            .into_iter()
            .map(|(method, line, character)| {
                responses(
                    &mut s,
                    &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": method,
                        "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                                   "position": {"line": line, "character": character}}}),
                )
            })
            .collect::<Vec<_>>()
        };
        let prepared = sysmlv2_transform::Library::prepared_sources(units(), None).unwrap();
        let expected = answers(PushServer::with_library_sources(units(), None));
        assert_eq!(answers(PushServer::with_library(prepared)), expected);
        assert_eq!(
            expected[2][0]["result"]["uri"], "sysmlv2-lib:/Mini%20Lib/MiniLib.sysml",
            "{expected:?}"
        );
        let items = expected[0][0]["result"]
            .as_array()
            .expect("completion items");
        assert!(items.iter().any(|i| i["label"] == "Gadget"), "{items:?}");
    }

    /// Hover, go-to-definition and document highlights answer while a
    /// unit does not parse — a member the parser cannot read elsewhere
    /// in the document, another document ending mid-declaration — off a
    /// session the broken units join salvaged, at the positions the
    /// documents hold (a `;` written over a line break shifts none).
    /// References, which a blanked member would leave short, answer
    /// nothing until everything parses. The session is built once for
    /// the documents as they stand.
    #[test]
    fn read_only_navigation_survives_syntax_errors() {
        let text = "package P {\n    private import B::*;\n    part def Vehicle { attribute mass; }\n    \
                    part z { attribute = ; }\n    part vehicle1 : Vehicle;\n    part y : Y;\n}\n";
        let other = "package B {\npart def X\npart def Y;\npart def W :> ;\n}\n";
        let mut s = two_package_server();
        for (uri, body) in [("file:///w/m.sysml", text), ("file:///w/b.sysml", other)] {
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": uri, "languageId": "sysml", "version": 1,
                                     "text": body}}}),
            );
        }
        let at = |line: u32, character: u32| {
            serde_json::json!({"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": line, "character": character}})
        };
        let ask = |s: &mut PushServer, id: i32, method: &str, params: serde_json::Value| {
            let mut params = params;
            if method == "textDocument/references" {
                params["context"] = serde_json::json!({"includeDeclaration": true});
            }
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}),
            )[0]["result"]
                .clone()
        };
        let hover = ask(&mut s, 2, "textDocument/hover", at(4, 22));
        assert!(
            hover["contents"]["value"]
                .as_str()
                .is_some_and(|v| v.contains("P::Vehicle")),
            "{hover}"
        );
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        let definition = ask(&mut s, 3, "textDocument/definition", at(4, 22));
        assert_eq!(definition["uri"], "file:///w/m.sysml", "{definition}");
        assert_eq!(definition["range"]["start"]["line"], 2, "{definition}");
        assert_eq!(
            definition["range"]["start"]["character"], 13,
            "{definition}"
        );
        // Into the other document, below a declaration missing its `;`.
        let definition = ask(&mut s, 4, "textDocument/definition", at(5, 13));
        assert_eq!(definition["uri"], "file:///w/b.sysml", "{definition}");
        assert_eq!(definition["range"]["start"]["line"], 2, "{definition}");
        assert_eq!(definition["range"]["start"]["character"], 9, "{definition}");
        let highlights = ask(&mut s, 5, "textDocument/documentHighlight", at(2, 15));
        let lines: Vec<u64> = highlights
            .as_array()
            .map(|h| {
                h.iter()
                    .filter_map(|h| h["range"]["start"]["line"].as_u64())
                    .collect()
            })
            .unwrap_or_default();
        assert_eq!(lines, [2, 4], "{highlights}");
        assert_eq!(
            ask(&mut s, 6, "textDocument/references", at(2, 15)),
            serde_json::Value::Null
        );
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
    }

    /// A document that stops parsing leaves the strict session stale,
    /// answering nothing for the new versions: building the tolerant one
    /// lets it go, so no more than two models are held at once.
    #[test]
    fn a_stale_strict_session_is_let_go_for_the_tolerant_one() {
        let valid = "package P {\n    part def Vehicle;\n    part v : Vehicle;\n}\n";
        let broken = "package P {\n    part def Vehicle;\n    part v : Vehicle;\n    part z { attribute = ; }\n}\n";
        let mut s = two_package_server();
        let hover = |s: &mut PushServer, id: i32| {
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": id, "method": "textDocument/hover",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 2, "character": 14}}}),
            )[0]["result"]
                .clone()
        };
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": valid}}}),
        );
        assert!(!hover(&mut s, 2).is_null());
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                "contentChanges": [{"text": broken}]}}),
        );
        assert!(!hover(&mut s, 3).is_null());
        let held = s.server.as_ref().expect("initialized").nav.sessions_held();
        assert_eq!(held, 1, "the tolerant session alone");
    }

    /// Definition on a library-typed reference lands inside the library
    /// unit, addressed by the `sysmlv2-lib:/` scheme (the host serves
    /// that text as a read-only virtual document). Unit names keep their
    /// library-relative path, space-encoded.
    #[test]
    fn definition_reaches_library_units() {
        let mut s = PushServer::with_library_sources(
            vec![(
                "Mini Lib/MiniLib.sysml".to_string(),
                "package MiniLib {\n    part def Widget;\n}\n".to_string(),
            )],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    private import MiniLib::*;\n    part w : Widget;\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/definition",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 2, "character": 14}}}),
        );
        let loc = &out[0]["result"];
        assert_eq!(
            loc["uri"], "sysmlv2-lib:/Mini%20Lib/MiniLib.sysml",
            "{loc:?}"
        );
        assert_eq!(loc["range"]["start"]["line"], 1, "{loc:?}");
        assert_eq!(loc["range"]["start"]["character"], 13, "{loc:?}");
    }

    /// The half-typed import is an outline node named by the typed word
    /// itself; it must not be offered back (it would outrank the real
    /// target with a self-referential path).
    #[test]
    fn import_completion_omits_the_phantom_self_symbol() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P { private import Widg }"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 0, "character": 31}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let phantom: Vec<&serde_json::Value> = items
            .iter()
            .filter(|i| i["textEdit"]["newText"].as_str() == Some("P::Widg"))
            .collect();
        assert!(
            phantom.is_empty(),
            "phantom self-symbol offered: {phantom:?}"
        );
    }

    /// An import missing its `;` runs into the next statement, which
    /// makes that statement an import context. When the statement
    /// declares the word being typed — a keyword whose next word may be
    /// a new name keeps completion on (`flow Widg`) — that declaration
    /// must not be offered back as an import (`P::Widg`), and a
    /// declared name after a declaring keyword gets no names at all.
    #[test]
    fn import_context_omits_the_declaration_being_typed() {
        for marked in [
            "package P {\n    private import MiniLib::*\n    flow Widg|\n}\n",
            "package P {\n    private import MiniLib::*\n    succession flow Widg|\n}\n",
            "package P {\n    private import MiniLib::*\n    message Widg|\n}\n",
        ] {
            let items = complete_in("file:///w/m.sysml", marked);
            assert!(
                items
                    .iter()
                    .any(|i| i["textEdit"]["newText"] == "MiniLib::Widget"),
                "import context: {items:?}"
            );
            let phantom: Vec<&serde_json::Value> = items
                .iter()
                .filter(|i| i["textEdit"]["newText"].as_str() == Some("P::Widg"))
                .collect();
            assert!(phantom.is_empty(), "phantom offered: {phantom:?}");
        }
        let items = complete_in(
            "file:///w/m.sysml",
            "package P {\n    private import MiniLib::*\n    part def Widg|;\n}\n",
        );
        assert!(items.is_empty(), "a declared name: {items:?}");
    }

    /// An import missing its `;` runs into a bare word on the next line,
    /// which the parse declares: the import path list must not offer
    /// that word back as `P::Widg`.
    #[test]
    fn import_context_omits_a_bare_word_the_parse_declares() {
        let items = complete_at("package P {\n    private import MiniLib::*\n    Widg|;\n}\n");
        assert!(
            items
                .iter()
                .any(|i| i["textEdit"]["newText"] == "MiniLib::Widget"),
            "import context: {items:?}"
        );
        assert!(
            items
                .iter()
                .all(|i| i["textEdit"]["newText"].as_str() != Some("P::Widg")),
            "phantom offered: {items:?}"
        );
    }

    /// A server over one in-memory library unit, initialized for
    /// utf-8 positions.
    fn library_server(library: &str) -> PushServer {
        let mut s = PushServer::with_library_sources(
            vec![("Lib.kerml".to_string(), library.to_string())],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        s
    }

    /// Open (or replace) `file:///w/m.sysml` with `text` and complete
    /// at `line`/`character`.
    fn completion_in_m(
        s: &mut PushServer,
        text: &str,
        line: u32,
        character: u32,
    ) -> Vec<serde_json::Value> {
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1, "text": text}}}),
        );
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": line, "character": character}}}),
        );
        out[0]["result"]
            .as_array()
            .expect("completion items")
            .clone()
    }

    /// `import` and `expose` members declare nothing: neither the
    /// library's nor the workspace's own become completion symbols —
    /// not by simple name, not as members of their owner, not in an
    /// import path — while an alias stays a member and the outline
    /// still lists every import.
    #[test]
    fn import_members_are_not_completion_symbols() {
        let mut s = library_server(
            "standard library package Parts { class Bolt; } \
             standard library package Kit { private import Parts::Bolt; \
             public import Parts::*; alias Fastener for Parts::Bolt; class Crate; }",
        );

        // Unqualified: the library's `Parts::Bolt` import is no name,
        // and the workspace's own `import Kit::*` and `expose Parts::*`
        // do not shadow the library packages they name.
        let text = "package P {\n    private import Kit::*;\n    view v { expose Parts::*; }\n    ref b : \n}\n";
        let items = completion_in_m(&mut s, text, 3, 12);
        let labels = completion_labels(&items);
        let paths: Vec<&str> = labels
            .iter()
            .copied()
            .filter(|l| l.contains("::"))
            .collect();
        assert!(paths.is_empty(), "import paths offered as names: {paths:?}");
        for package in ["Kit", "Parts"] {
            let item = items
                .iter()
                .find(|i| i["label"] == package)
                .unwrap_or_else(|| panic!("{package} offered"));
            assert_eq!(item["detail"], "standard library", "{item}");
            assert!(item.get("additionalTextEdits").is_none(), "{item}");
        }
        let alias = items
            .iter()
            .find(|i| i["label"] == "Fastener")
            .expect("alias offered");
        assert_eq!(alias["detail"], "Kit::Fastener");

        // Qualified: an import is not a member of its owner.
        let text = "package P {\n    private import Kit::*;\n    part b : Kit::\n}\n";
        let items = completion_in_m(&mut s, text, 2, 18);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Crate") && labels.contains(&"Fastener"),
            "{labels:?}"
        );
        assert!(
            !labels.iter().any(|l| l.starts_with("Parts")),
            "imports listed as members: {labels:?}"
        );

        // Import path: one `Kit`, the package itself.
        let text = "package P {\n    private import Kit::*;\n    private import Ki\n}\n";
        let items = completion_in_m(&mut s, text, 2, 21);
        let inserted: Vec<&str> = items
            .iter()
            .filter(|i| i["label"] == "Kit")
            .filter_map(|i| i["textEdit"]["newText"].as_str())
            .collect();
        assert_eq!(inserted, ["Kit"]);
        assert!(
            !items.iter().any(|i| i["textEdit"]["newText"]
                .as_str()
                .is_some_and(|t| t.starts_with("Kit::Parts"))),
            "an import's target offered under its owner"
        );

        // The outline is unchanged: it lists the imports.
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"}}}),
        );
        let children = out[0]["result"][0]["children"]
            .as_array()
            .expect("package members");
        assert!(
            children.iter().any(|c| c["name"] == "Kit"
                && c["kind"] == serde_json::json!(lsp_types::SymbolKind::MODULE)),
            "{children:?}"
        );
    }

    /// After a qualifier, a namespace offers what it makes visible: its
    /// own members, then what its public imports bring in — a whole
    /// namespace (`::*`), one member, a namespace recursively (`::**`),
    /// and, transitively, what the imported namespaces re-export —
    /// once per name, an owned member hiding an imported one. Private
    /// imports re-export nothing; no visibility keyword is public.
    #[test]
    fn qualifier_offers_what_public_imports_bring_in() {
        let mut s = library_server(
            "standard library package Base { class Widget; class Gadget; } \
             standard library package More { class Bolt; } \
             standard library package Hidden { class Secret; } \
             standard library package Solo { class Nut; class Washer; } \
             standard library package Deep { package Inner { class Pin; } } \
             standard library package Facade { public import Base::*; import More::*; \
             private import Hidden::*; public import Solo::Nut; public import Deep::**; \
             class Own; class Gadget; } \
             standard library package Outer { public import Facade::*; }",
        );
        // The members offered (an import path also offers wildcards).
        let offered = |items: &[serde_json::Value]| -> Vec<(String, String)> {
            items
                .iter()
                .filter(|i| i["label"] != "*" && i["label"] != "**")
                .map(|i| {
                    let text = |v: &serde_json::Value| v.as_str().unwrap_or_default().to_string();
                    (text(&i["label"]), text(&i["detail"]))
                })
                .collect()
        };
        let expected = [
            ("Own", "Facade::Own"),
            ("Gadget", "Facade::Gadget"),
            ("Widget", "Base::Widget"),
            ("Bolt", "More::Bolt"),
            ("Nut", "Solo::Nut"),
            ("Deep", "Deep"),
            ("Inner", "Deep::Inner"),
            ("Pin", "Deep::Inner::Pin"),
        ]
        .map(|(l, d)| (l.to_string(), d.to_string()));
        // Right after each qualifier, on line 1.
        for (text, character) in [
            ("package P {\n    part w : Facade::\n}\n", 21u32),
            ("package P {\n    private import Facade::\n}\n", 27),
        ] {
            let items = completion_in_m(&mut s, text, 1, character);
            assert_eq!(offered(&items), expected, "{text:?}");
        }
        // Transitively: `Outer` re-exports what `Facade` makes visible.
        let items = completion_in_m(&mut s, "package P {\n    part w : Outer::\n}\n", 1, 20);
        let labels = completion_labels(&items);
        for name in ["Own", "Widget", "Bolt", "Nut", "Pin"] {
            assert!(labels.contains(&name), "`{name}` missing: {labels:?}");
        }
        assert!(!labels.contains(&"Secret") && !labels.contains(&"Washer"));
    }

    /// An existing namespace import admits what the imported namespace
    /// re-exports: after `import Facade::*;` a member `Facade`
    /// re-exports from `Base` needs no import of its own — transitively
    /// too, and through a workspace package an import names relative
    /// to its own — while a private import re-exports nothing. The
    /// "Add import" fix holds to the same check.
    #[test]
    fn import_admission_follows_reexports() {
        let library = "standard library package Base { class Widget; } \
                       standard library package Facade { public import Base::*; } \
                       standard library package Outer { public import Facade::*; } \
                       standard library package Sealed { private import Base::*; }";
        for (text, line, character, admitted) in [
            (
                "package P {\n    private import Facade::*;\n    ref w : \n}\n",
                2u32,
                12u32,
                true,
            ),
            (
                "package P {\n    private import Outer::*;\n    ref w : \n}\n",
                2,
                12,
                true,
            ),
            (
                "package P {\n    private import Sealed::*;\n    ref w : \n}\n",
                2,
                12,
                false,
            ),
            (
                "package P {\n    package Kit { public import Base::*; }\n    package Use {\n        \
                 private import Kit::*;\n        ref w : \n    }\n}\n",
                4,
                16,
                true,
            ),
        ] {
            let mut s = library_server(library);
            let items = completion_in_m(&mut s, text, line, character);
            let widget = items
                .iter()
                .find(|i| i["label"] == "Widget")
                .expect("Widget offered");
            assert_eq!(
                widget.get("additionalTextEdits").is_none(),
                admitted,
                "{text:?}: {widget}"
            );

            // The quick fix on an unresolved `Widget` at the same spot.
            let fixed = text.replacen("ref w : \n", "ref w : Widget;\n", 1);
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "version": 2},
                    "contentChanges": [{"text": fixed}]}}),
            );
            let range = serde_json::json!({"start": {"line": line, "character": character},
                                           "end": {"line": line, "character": character + 6}});
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/codeAction",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "range": range,
                               "context": {"diagnostics": [
                                   {"range": range, "message": "unresolved reference `Widget`"}]}}}),
            );
            let fixes = out[0]["result"]
                .as_array()
                .expect("actions")
                .iter()
                .filter(|a| {
                    a["title"]
                        .as_str()
                        .is_some_and(|t| t.starts_with("Add import"))
                })
                .count();
            assert_eq!(fixes == 0, admitted, "{fixed:?}");
        }
    }

    /// An inserted import names the conventional path: through the
    /// package of the symbol's family when that package re-exports it
    /// (`Kit::Crate` for `KitParts::Crate`), through a top-level
    /// package when that is shorter (`Top::Deep` for `Top::Inner::Deep`),
    /// and the symbol's own path otherwise — also when the family's
    /// package declares a member of the same name, or the name only
    /// begins like the package's (`Car` is no family of `Cargo`).
    /// Completion's auto-import, the "Add import" fix, and import-path
    /// completion agree.
    #[test]
    fn imports_name_the_conventional_path() {
        let library = "standard library package KitParts { class Crate; } \
                       standard library package Kit { public import KitParts::*; } \
                       standard library package Other { public import KitParts::*; } \
                       standard library package Base { class Widget; } \
                       standard library package Facade { public import Base::*; } \
                       standard library package Top { package Inner { class Deep; } \
                       public import Inner::*; } \
                       standard library package LotParts { class Box; } \
                       standard library package Lot { public import LotParts::*; class Box; } \
                       standard library package Cargo { class Pallet; } \
                       standard library package Car { public import Cargo::*; }";
        let mut s = library_server(library);

        // Completion: the auto-import and its `import …` annotation.
        let items = completion_in_m(&mut s, "package P {\n    ref w : \n}\n", 1, 12);
        for (label, path) in [
            ("Crate", "Kit::Crate"),
            ("Widget", "Base::Widget"),
            ("Pallet", "Cargo::Pallet"),
        ] {
            let item = items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"));
            assert_eq!(
                item["additionalTextEdits"][0]["newText"],
                format!("private import {path};\n    "),
                "{item}"
            );
            let package = path.rsplit_once("::").map(|(p, _)| p).unwrap_or_default();
            assert_eq!(
                item["labelDetails"]["description"],
                format!("import {package}")
            );
        }
        let boxes: Vec<&serde_json::Value> = items.iter().filter(|i| i["label"] == "Box").collect();
        assert!(
            boxes
                .iter()
                .any(|i| i["additionalTextEdits"][0]["newText"]
                    == "private import LotParts::Box;\n    "),
            "{boxes:?}"
        );

        // The quick fix on an unresolved name.
        for (name, path) in [("Crate", "Kit::Crate"), ("Deep", "Top::Deep")] {
            let text = format!("package P {{\n    part w : {name};\n}}\n");
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": "file:///w/m.sysml", "version": 3},
                    "contentChanges": [{"text": text}]}}),
            );
            let range = serde_json::json!({"start": {"line": 1, "character": 13},
                                           "end": {"line": 1, "character": 13 + name.len()}});
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/codeAction",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "range": range,
                               "context": {"diagnostics": [
                                   {"range": range,
                                    "message": format!("unresolved reference `{name}`")}]}}}),
            );
            let titles: Vec<&str> = out[0]["result"]
                .as_array()
                .expect("actions")
                .iter()
                .filter_map(|a| a["title"].as_str())
                .collect();
            assert!(
                titles.contains(&format!("Add import {path}").as_str()),
                "{titles:?}"
            );
        }

        // Import-path completion inserts the same path.
        for (typed, label, path) in [("Cra", "Crate", "Kit::Crate"), ("Dee", "Deep", "Top::Deep")] {
            let text = format!("package P {{\n    private import {typed}\n}}\n");
            // Right after the typed word.
            let items = completion_in_m(&mut s, &text, 1, 22);
            let item = items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"));
            assert_eq!(item["textEdit"]["newText"], path);
            assert_eq!(item["detail"], path);
        }
    }

    /// An inserted import's annotation names its package as the
    /// statement spells it: a restricted name quoted.
    #[test]
    fn an_import_annotation_quotes_restricted_names() {
        let mut s = library_server("standard library package 'Model Lib' { class Gear; }");
        let items = completion_in_m(&mut s, "package P {\n    ref w : \n}\n", 1, 12);
        let gear = items
            .iter()
            .find(|i| i["label"] == "Gear")
            .expect("Gear offered");
        assert_eq!(
            gear["additionalTextEdits"][0]["newText"],
            "private import 'Model Lib'::Gear;\n    "
        );
        assert_eq!(gear["labelDetails"]["description"], "import 'Model Lib'");
    }

    /// The statement being typed declares its names ahead of the cursor:
    /// none is offered in its own value or specialization.
    #[test]
    fn a_statement_does_not_offer_its_own_name() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        for (text, character, own) in [
            ("package P {\n    attribute zz = \n}\n", 19, "zz"),
            ("package P {\n    attribute <z> zz = \n}\n", 23, "z"),
            ("package P {\n    part def Gear :> \n}\n", 21, "Gear"),
        ] {
            let items = completion_in_m(&mut s, text, 1, character);
            let labels = completion_labels(&items);
            assert!(!labels.contains(&own), "{text:?}: {labels:?}");
        }
    }

    /// The "Add import" titles offered for an unresolved bare `name`
    /// written as `part w : <name>;` inside `package P` after `imports`.
    fn import_fix_titles(s: &mut PushServer, imports: &str, name: &str) -> Vec<String> {
        let text = format!("package P {{\n{imports}    part w : {name};\n}}\n");
        let line = text
            .lines()
            .position(|l| l.contains("part w : "))
            .expect("line");
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 9, "text": text}}}),
        );
        let range = serde_json::json!({"start": {"line": line, "character": 13},
                                       "end": {"line": line, "character": 13 + name.len()}});
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 5, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range,
                                "message": format!("unresolved reference `{name}`")}]}}}),
        );
        out[0]["result"]
            .as_array()
            .expect("actions")
            .iter()
            .filter_map(|a| a["title"].as_str())
            .filter(|t| t.starts_with("Add import"))
            .map(str::to_string)
            .collect()
    }

    /// "Add import" titles for `part w : <name>;` in `package P`, with
    /// `prefix` at the root of the document ahead of it.
    fn root_fix_titles(s: &mut PushServer, prefix: &str, name: &str) -> Vec<String> {
        let text = format!("{prefix}package P {{\n    part w : {name};\n}}\n");
        let line = text
            .lines()
            .position(|l| l.contains("part w : "))
            .expect("line");
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 9, "text": text}}}),
        );
        let range = serde_json::json!({"start": {"line": line, "character": 13},
                                       "end": {"line": line, "character": 13 + name.len()}});
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 5, "method": "textDocument/codeAction",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "range": range,
                           "context": {"diagnostics": [
                               {"range": range,
                                "message": format!("unresolved reference `{name}`")}]}}}),
        );
        out[0]["result"]
            .as_array()
            .expect("actions")
            .iter()
            .filter_map(|a| a["title"].as_str())
            .filter(|t| t.starts_with("Add import"))
            .map(str::to_string)
            .collect()
    }

    /// The path an inserted import names does not depend on the
    /// questions asked before: a layer's routes are shared with the
    /// layers above it, and one of those can declare a package of the
    /// route's name itself (here the document's own `Kit`, whose
    /// `Crate` takes the name, so `Kit::Crate` would name it).
    #[test]
    fn import_routes_do_not_depend_on_earlier_requests() {
        let library = "standard library package KitParts { class Crate; } \
                       standard library package Kit { public import KitParts::*; }";
        let own_kit = "package Kit {\n    part def Crate;\n}\n";
        let fresh = |prefix: &str| root_fix_titles(&mut library_server(library), prefix, "Crate");
        let (with_own_kit, without) = (fresh(own_kit), fresh(""));
        assert_eq!(
            with_own_kit,
            ["Add import Kit::Crate", "Add import KitParts::Crate"]
        );
        assert_eq!(without, ["Add import Kit::Crate"]);
        let mut s = library_server(library);
        assert_eq!(root_fix_titles(&mut s, "", "Crate"), without);
        assert_eq!(root_fix_titles(&mut s, own_kit, "Crate"), with_own_kit);
        assert_eq!(root_fix_titles(&mut s, "", "Crate"), without);
    }

    /// A private import elsewhere of a package the document declares
    /// changes nothing any namespace makes visible, so a keystroke
    /// still reworks only its own document.
    #[test]
    fn a_private_import_of_the_document_keeps_the_rest_cached() {
        let mut s = library_server("standard library package Lib { class Unused; }");
        let open = |s: &mut PushServer, uri: &str, text: &str| {
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {"uri": uri, "languageId": "sysml",
                                                "version": 1, "text": text}}}),
            );
        };
        open(
            &mut s,
            "file:///w/uses.sysml",
            "package Uses {\n    private import P::*;\n    part def Wheel;\n}\n",
        );
        let complete = |s: &mut PushServer, typed: &str| {
            let text = format!("package P {{\n    part w : {typed}\n}}\n");
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                                "version": 1, "text": text}}}),
            );
            let out = responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 1, "character": 13 + typed.len()}}}),
            );
            out[0]["result"].as_array().expect("items").len()
        };
        assert!(complete(&mut s, "") > 0);
        crate::nav::WORK.with(|w| w.set([0; 3]));
        assert!(complete(&mut s, "W") > 0);
        assert_eq!(
            crate::nav::WORK.with(std::cell::Cell::get),
            [2, 0, 0],
            "symbols indexed, names, route walks"
        );
    }

    /// Taking an alias as what it names reads one name in each namespace
    /// on the way, not everything the namespace makes visible: a request
    /// whose list needs no namespace's names works none out, though the
    /// document's alias `C` reads `Crate` through the import of `Kit`'s
    /// members and the table holding it is built anew.
    #[test]
    fn aliases_resolve_without_working_out_whole_namespaces() {
        let mut s = library_server("standard library package Kit { class Crate; class Pallet; }");
        let text = "package P {\n    private import Kit::*;\n    alias C for Crate;\n    \
                    package Q {\n        part def Leaf;\n    }\n    ref w : Q::\n}\n";
        crate::nav::WORK.with(|w| w.set([0; 3]));
        let items = completion_in_m(&mut s, text, 6, 15);
        assert_eq!(completion_labels(&items), ["Leaf"]);
        assert_eq!(
            crate::nav::WORK.with(std::cell::Cell::get)[1],
            0,
            "namespaces whose names were worked out"
        );
    }

    /// An import's filter condition is an expression, not the path:
    /// a qualifier there (`[@MiniLib::`) offers no wildcards.
    #[test]
    fn an_import_filter_offers_no_wildcards() {
        let mut s = two_package_server();
        let text = "package P {\n    private import OtherLib::*[@MiniLib::\n}\n";
        let items = completion_in_m(&mut s, text, 1, 41);
        let labels = completion_labels(&items);
        assert!(labels.contains(&"Widget"), "{labels:?}");
        assert!(
            !labels.contains(&"*") && !labels.contains(&"**"),
            "{labels:?}"
        );
    }

    /// A private member is visible only inside its namespace or through
    /// an `import all`, where it needs no import, and no inserted import
    /// makes it visible anywhere else: it is offered bare there, and
    /// elsewhere neither with an import, nor in an import path, nor by
    /// the "Add import" fix, nor after its namespace's qualifier.
    #[test]
    fn private_members_are_offered_only_where_visible() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/hidden.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Hidden {\n    private part def Secret;\n    \
                                          part def Open;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : \n}\n", 1, 13);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && !labels.contains(&"Secret"),
            "{labels:?}"
        );
        // An import of the namespace brings in its public members; only
        // an `import all` brings in the others.
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Hidden::*;\n    part w : \n}\n",
            2,
            13,
        );
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && !labels.contains(&"Secret"),
            "{labels:?}"
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import all Hidden::*;\n    part w : \n}\n",
            2,
            13,
        );
        let secret = items
            .iter()
            .find(|i| i["label"] == "Secret")
            .expect("offered through an `import all`");
        assert!(secret.get("additionalTextEdits").is_none(), "{secret}");
        let items = completion_in_m(&mut s, "package P {\n    private import Sec\n}\n", 1, 22);
        assert!(!completion_labels(&items).contains(&"Secret"));
        assert!(import_fix_titles(&mut s, "", "Secret").is_empty());
        // Inside its namespace: offered as is.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/hidden.sysml", "version": 2},
                "contentChanges": [{"text": "package Hidden {\n    private part def Secret;\n    \
                                              part w : \n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/hidden.sysml"},
                           "position": {"line": 2, "character": 13}}}),
        );
        let items = out[0]["result"].as_array().expect("items");
        let secret = items
            .iter()
            .find(|i| i["label"] == "Secret")
            .expect("offered inside its namespace");
        assert!(secret.get("additionalTextEdits").is_none(), "{secret}");
        // After its namespace's qualifier: inside the namespace, not
        // outside it.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": "file:///w/hidden.sysml", "version": 3},
                "contentChanges": [{"text": "package Hidden {\n    private part def Secret;\n    \
                                              part w : Hidden::\n}\n"}]}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/hidden.sysml"},
                           "position": {"line": 2, "character": 21}}}),
        );
        let labels = completion_labels(out[0]["result"].as_array().expect("items"));
        assert!(labels.contains(&"Secret"), "{labels:?}");
        let items = completion_in_m(&mut s, "package P {\n    part w : Hidden::\n}\n", 1, 21);
        let labels = completion_labels(&items);
        assert!(!labels.contains(&"Secret"), "{labels:?}");
    }

    /// The import edits of the items labeled `label`.
    fn import_edits_of(items: &[serde_json::Value], label: &str) -> Vec<String> {
        items
            .iter()
            .filter(|i| i["label"] == label)
            .map(|i| {
                i["additionalTextEdits"][0]["newText"]
                    .as_str()
                    .unwrap_or_default()
                    .to_string()
            })
            .collect()
    }

    /// A name that two of a namespace's public imports bring in denotes
    /// no one element there: `Kit::Crate` is an ambiguous reference
    /// when `Kit` re-exports both `KitA::Crate` and `KitB::Crate` (the
    /// standard library's `ISQ` does so for eleven names). No inserted
    /// import runs through such a namespace, an existing import of it
    /// does not count as providing the name, and a qualifier does not
    /// offer it; its unambiguous neighbours are unaffected.
    #[test]
    fn ambiguous_reexports_are_not_imported_through() {
        let mut s = library_server(
            "standard library package KitA { class Crate; class Only; } \
             standard library package KitB { class Crate; } \
             standard library package Kit { public import KitA::*; public import KitB::*; }",
        );
        // Auto-import: the declaring package, not the facade.
        let items = completion_in_m(&mut s, "package P {\n    ref w : \n}\n", 1, 12);
        assert_eq!(
            import_edits_of(&items, "Crate"),
            ["private import KitA::Crate;\n    "]
        );
        assert_eq!(
            import_edits_of(&items, "Only"),
            ["private import Kit::Only;\n    "]
        );
        // An existing `import Kit::*;` provides `Only`, not `Crate`.
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Kit::*;\n    ref w : \n}\n",
            2,
            12,
        );
        let crate_item = items.iter().find(|i| i["label"] == "Crate").expect("Crate");
        assert!(
            crate_item.get("additionalTextEdits").is_some(),
            "{crate_item}"
        );
        let only = items.iter().find(|i| i["label"] == "Only").expect("Only");
        assert!(only.get("additionalTextEdits").is_none(), "{only}");
        // After `Kit::`: `Only`, not the ambiguous `Crate`.
        let items = completion_in_m(&mut s, "package P {\n    part w : Kit::\n}\n", 1, 18);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Only") && !labels.contains(&"Crate"),
            "{labels:?}"
        );
        // Import-path completion: each `Crate` by its own path, once.
        let items = completion_in_m(&mut s, "package P {\n    private import Cra\n}\n", 1, 22);
        let mut paths: Vec<&str> = items
            .iter()
            .filter(|i| i["label"] == "Crate")
            .filter_map(|i| i["textEdit"]["newText"].as_str())
            .collect();
        paths.sort_unstable();
        assert_eq!(paths, ["KitA::Crate", "KitB::Crate"]);
        // The quick fix agrees.
        let mut titles = import_fix_titles(&mut s, "", "Crate");
        titles.sort();
        assert_eq!(titles, ["Add import KitA::Crate", "Add import KitB::Crate"]);
    }

    /// An owned member hides an imported one of the same name at every
    /// step of a re-export chain: `Outer` re-exports `Facade`'s own
    /// `Gadget`, not the `BaseP::Inner::Gadget` that `Facade` imports,
    /// so `Outer::Gadget` would silently name the other element.
    #[test]
    fn hidden_reexports_are_not_imported_through() {
        let mut s = library_server(
            "standard library package BaseP { package Inner { class Gadget; } } \
             standard library package Facade { public import BaseP::Inner::*; class Gadget; } \
             standard library package Outer { public import Facade::*; }",
        );
        let items = completion_in_m(&mut s, "package P {\n    private import Gadg\n}\n", 1, 23);
        let mut paths: Vec<&str> = items
            .iter()
            .filter(|i| i["label"] == "Gadget")
            .filter_map(|i| i["textEdit"]["newText"].as_str())
            .collect();
        paths.sort_unstable();
        assert_eq!(paths, ["BaseP::Inner::Gadget", "Facade::Gadget"]);
        let mut titles = import_fix_titles(&mut s, "", "Gadget");
        titles.sort();
        assert_eq!(
            titles,
            [
                "Add import BaseP::Inner::Gadget",
                "Add import Facade::Gadget"
            ]
        );
        // The hidden name is no ambiguity: `Outer::Gadget` is `Facade`'s
        // own, listed after the qualifier and provided by an import of
        // `Outer`, which does not provide the one it hides.
        let items = completion_in_m(&mut s, "package P {\n    part w : Outer::\n}\n", 1, 20);
        let gadget = items
            .iter()
            .find(|i| i["label"] == "Gadget")
            .expect("Gadget listed");
        assert_eq!(gadget["detail"], "Facade::Gadget");
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Outer::*;\n    ref w : \n}\n",
            2,
            12,
        );
        for (detail, provided) in [("Facade::Gadget", true), ("BaseP::Inner::Gadget", false)] {
            let edits: Vec<bool> = items
                .iter()
                .filter(|i| i["detail"] == detail)
                .map(|i| i.get("additionalTextEdits").is_none())
                .collect();
            assert!(
                edits.is_empty() || edits == [provided],
                "{detail}: {edits:?}"
            );
        }
        let gadget = items
            .iter()
            .find(|i| i["label"] == "Gadget")
            .expect("Gadget offered");
        assert_eq!(gadget["detail"], "Facade::Gadget");
        assert!(gadget.get("additionalTextEdits").is_none(), "{gadget}");
    }

    /// A filtered import brings in only the members its condition
    /// admits (`[@Safety]`, or a `filter` member of the importing
    /// package), which a syntax tier cannot evaluate: such a package
    /// counts as re-exporting nothing — no inserted import runs through
    /// it (`SafeParts::Bolt` does not resolve), an existing import of
    /// it provides nothing, and its qualifier offers nothing imported.
    #[test]
    fn filtered_reexports_are_not_imported_through() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/lib.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Lib {\n    metadata def Safety;\n    \
                                          package Parts {\n        part def Bolt;\n        \
                                          part def Nut { @Safety; }\n    }\n}\n\
                                          package SafeParts {\n    \
                                          public import Lib::Parts::*[@Lib::Safety];\n}\n\
                                          package SafeParts2 {\n    \
                                          public import Lib::Parts::*;\n    \
                                          filter @Lib::Safety;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : \n}\n", 1, 13);
        for (label, path) in [("Bolt", "Lib::Parts::Bolt"), ("Nut", "Lib::Parts::Nut")] {
            assert_eq!(
                import_edits_of(&items, label),
                [format!("private import {path};\n    ")],
                "{label}"
            );
        }
        for facade in ["SafeParts", "SafeParts2"] {
            let text =
                format!("package P {{\n    private import {facade}::*;\n    part w : \n}}\n");
            let items = completion_in_m(&mut s, &text, 2, 13);
            let bolt = items.iter().find(|i| i["label"] == "Bolt").expect("Bolt");
            assert!(
                bolt.get("additionalTextEdits").is_some(),
                "{facade}: {bolt}"
            );
            let text = format!("package P {{\n    part w : {facade}::\n}}\n");
            let items = completion_in_m(
                &mut s,
                &text,
                1,
                u32::try_from(15 + facade.len()).expect("column"),
            );
            let labels = completion_labels(&items);
            assert!(!labels.contains(&"Bolt"), "{facade}: {labels:?}");
        }
        let titles = import_fix_titles(&mut s, "", "Bolt");
        assert!(
            titles.contains(&"Add import Lib::Parts::Bolt".to_string())
                && !titles.iter().any(|t| t.contains("SafeParts")),
            "{titles:?}"
        );
    }

    /// The document's own filtered import provides only what its
    /// condition admits, which completion cannot tell, so it counts as
    /// providing none of the names the imported package re-exports —
    /// whether the condition is the import's own `[…]` or a `filter`
    /// member beside it — and accepting one still inserts its import.
    #[test]
    fn own_filtered_imports_admit_no_reexports() {
        let mut s = library_server(
            "standard library package Base { class Widget; metadata def Safety; } \
             standard library package Facade { public import Base::*; }",
        );
        for (imports, provided) in [
            ("    private import Facade::*;\n", true),
            ("    private import Facade::*[@Base::Safety];\n", false),
            (
                "    private import Facade::*;\n    filter @Base::Safety;\n",
                false,
            ),
        ] {
            let text = format!("package P {{\n{imports}    ref w : \n}}\n");
            let line = u32::try_from(text.lines().count() - 2).expect("line");
            let items = completion_in_m(&mut s, &text, line, 12);
            let widget = items
                .iter()
                .find(|i| i["label"] == "Widget")
                .expect("Widget offered");
            assert_eq!(
                widget.get("additionalTextEdits").is_none(),
                provided,
                "{imports:?}: {widget}"
            );
        }
    }

    /// A private member is no member of its package for anyone outside
    /// it, so a package that imports it does not re-export it either:
    /// `Facade::Hidden` does not resolve.
    #[test]
    fn private_members_are_not_reexported() {
        let mut s = library_server(
            "standard library package Base { class Open; private class Hidden; } \
             standard library package Facade { public import Base::*; }",
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : Facade::\n}\n", 1, 21);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && !labels.contains(&"Hidden"),
            "{labels:?}"
        );
    }

    /// Two imports of a scope bringing in different elements under one
    /// name make it ambiguous there, so neither is named bare: the name
    /// comes with an import of its one member, which is found ahead of
    /// what the namespace imports bring in — and with that import in
    /// place, it comes bare.
    #[test]
    fn a_name_two_imports_bring_in_comes_with_an_import_of_it() {
        let mut s = library_server(
            "standard library package KitA { class Crate; class Pallet; } \
             standard library package KitB { class Crate; }",
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import KitA::*;\n    private import KitB::*;\n    \
             ref w : \n}\n",
            3,
            12,
        );
        assert_eq!(
            import_edits_of(&items, "Crate"),
            ["\n    private import KitA::Crate;"]
        );
        assert_eq!(import_edits_of(&items, "Pallet"), [""]);
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import KitA::*;\n    private import KitB::*;\n    \
             private import KitA::Crate;\n    ref w : \n}\n",
            4,
            12,
        );
        assert_eq!(import_edits_of(&items, "Crate"), [""]);
    }

    /// A name an import of one member brings in finds that member ahead
    /// of anything an inserted import beside it could bring in, so no
    /// other element of that name is offered with an import: here the
    /// library's `Crate` comes bare, not the workspace's with one.
    #[test]
    fn an_import_of_one_member_keeps_its_name() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/q.sysml", "languageId": "sysml",
                                 "version": 1, "text": "package Q {\n    part def Crate;\n}\n"}}}),
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Kit::Crate;\n    ref w : \n}\n",
            2,
            12,
        );
        let crates: Vec<&serde_json::Value> =
            items.iter().filter(|i| i["label"] == "Crate").collect();
        assert_eq!(crates.len(), 1, "{crates:?}");
        assert_eq!(crates[0]["detail"], "Kit::Crate", "{:?}", crates[0]);
        assert!(
            crates[0].get("additionalTextEdits").is_none(),
            "{:?}",
            crates[0]
        );
    }

    /// A name an enclosing package declares finds that element inside
    /// the packages it holds too, so no other element of that name
    /// comes with an import: one in the nearest package would take the
    /// name from every reference there (`Inner::Deep` would stop
    /// resolving). The element the name finds is offered, bare.
    #[test]
    fn a_name_an_enclosing_package_declares_keeps_it() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let items = completion_in_m(
            &mut s,
            "package BaseP {\n    package Inner {\n        part def Gadget;\n    }\n}\n\
             package Hidden {\n    package Inner {\n        part def Deep;\n    }\n    \
             package Vault {\n        part existing : Inner::Deep;\n        ref w : \n    }\n}\n",
            11,
            16,
        );
        let inners: Vec<&serde_json::Value> =
            items.iter().filter(|i| i["label"] == "Inner").collect();
        assert_eq!(inners.len(), 1, "{inners:?}");
        assert_eq!(inners[0]["detail"], "Hidden::Inner", "{:?}", inners[0]);
        assert!(
            inners[0].get("additionalTextEdits").is_none(),
            "{:?}",
            inners[0]
        );
    }

    /// The same for a name one namespace import of the package brings
    /// in: an import of another `Mass` beside it would be found ahead
    /// of it, and `existing` would name that one, silently.
    #[test]
    fn a_name_a_namespace_import_brings_in_keeps_it() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let items = completion_in_m(
            &mut s,
            "package Other {\n    part def Mass;\n}\npackage Lib {\n    part def Mass;\n}\n\
             package P {\n    private import Lib::*;\n    part existing : Mass;\n    ref w : \n}\n",
            9,
            12,
        );
        let masses: Vec<&serde_json::Value> =
            items.iter().filter(|i| i["label"] == "Mass").collect();
        assert_eq!(masses.len(), 1, "{masses:?}");
        assert_eq!(masses[0]["detail"], "Lib::Mass", "{:?}", masses[0]);
        assert!(
            masses[0].get("additionalTextEdits").is_none(),
            "{:?}",
            masses[0]
        );
    }

    /// A private member is no member of its package for a client, so it
    /// hides nothing from one either: what a public import brings in
    /// under its name is what the client finds (`Facade::Part` is
    /// `Base::Part`).
    #[test]
    fn private_members_hide_nothing_from_clients() {
        let mut s = library_server(
            "standard library package Base { class Part; } \
             standard library package Facade { private class Part; public import Base::*; }",
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : Facade::\n}\n", 1, 21);
        let part = items
            .iter()
            .find(|i| i["label"] == "Part")
            .expect("offered after the qualifier");
        assert_eq!(part["detail"], "Base::Part");
    }

    /// A usage without a name of its own is found by the name of the
    /// feature it redefines (`attribute redefines mass = 5;`, `part :>>
    /// engine`): listed under it after its owner's qualifier, which
    /// lists what paths through it reach too, and counted when names
    /// are compared — a recursive import of `Config` brings in two
    /// `mass`es, so `Analysis::` lists neither, and nothing inside the
    /// unnamed `engine`, which a recursive import does not reach into.
    #[test]
    fn unnamed_usages_are_found_by_the_name_they_redefine() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Defs {\n    part def Vehicle {\n        \
                                          attribute mass;\n        part engine;\n    }\n}\n\
                                          package Config {\n    part vehicle_b : Defs::Vehicle {\n        \
                                          attribute redefines mass = 5;\n        \
                                          part :>> engine {\n            part piston;\n        }\n    \
                                          }\n    part other {\n        attribute mass;\n    }\n}\n\
                                          package Analysis {\n    public import Config::**;\n}\n"}}}),
        );
        let labels = |s: &mut PushServer, qualifier: &str| -> Vec<String> {
            let text = format!("package P {{\n    ref w : {qualifier}::\n}}\n");
            let character = u32::try_from(14 + qualifier.len()).expect("column");
            completion_labels(&completion_in_m(s, &text, 1, character))
                .into_iter()
                .map(str::to_string)
                .collect()
        };
        assert_eq!(labels(&mut s, "Config::vehicle_b"), ["mass", "engine"]);
        assert_eq!(labels(&mut s, "Config::vehicle_b::engine"), ["piston"]);
        let analysis = labels(&mut s, "Analysis");
        assert!(analysis.contains(&"engine".to_string()), "{analysis:?}");
        assert!(
            !analysis.contains(&"mass".to_string()) && !analysis.contains(&"piston".to_string()),
            "{analysis:?}"
        );
    }

    /// A `perform` or a `satisfy` without a name of its own is found by
    /// the name of what it references — for a `perform`, the last step
    /// of a feature chain: `C::p::` lists `act`, `step`, and `req`.
    #[test]
    fn unnamed_usages_are_found_by_what_they_reference() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Acts {\n    action def Act;\n    \
                                          action act : Act {\n        action step;\n    }\n    \
                                          requirement req;\n}\npackage C {\n    part p {\n        \
                                          perform Acts::act;\n        perform Acts::act.step;\n        \
                                          satisfy Acts::req by p;\n    }\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    ref w : C::p::\n}\n", 1, 19);
        assert_eq!(completion_labels(&items), ["act", "step", "req"]);
    }

    /// A usage without a name of its own is offered by the name it is
    /// found by only after its owner's qualifier: in the list a name
    /// brings up anywhere, `spec` is the requirement a package declares,
    /// with its import, not the `satisfy` that references it.
    #[test]
    fn unnamed_usages_leave_their_names_to_what_declares_them() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Model {\n    part def V;\n    package Parts {\n        \
                                          part v : V {\n            satisfy Reqs::spec by v;\n        \
                                          }\n    }\n    package Reqs {\n        requirement spec;\n    \
                                          }\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    alias a for \n}\n", 1, 16);
        let specs: Vec<&serde_json::Value> =
            items.iter().filter(|i| i["label"] == "spec").collect();
        assert_eq!(specs.len(), 1, "{specs:?}");
        assert_eq!(specs[0]["detail"], "Model::Reqs::spec", "{:?}", specs[0]);
        assert_eq!(
            import_edits_of(&items, "spec"),
            ["    private import Model::Reqs::spec;\n"]
        );
    }

    /// An import resolves its path from where it sits: where a name
    /// there takes the path's first segment from the top-level package
    /// — here the `Reqs` that `Facade` re-exports — the inserted import
    /// writes the path from the global scope.
    #[test]
    fn an_inserted_import_whose_first_segment_is_taken_starts_at_the_root() {
        let mut s = library_server("standard library package Reqs { class check; }");
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/conf.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Conf {\n    package Reqs {\n        \
                                          part def Other;\n    }\n}\n\
                                          package Facade {\n    public import Conf::*;\n}\n"}}}),
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Facade::*;\n    ref w : \n}\n",
            2,
            12,
        );
        assert_eq!(
            import_edits_of(&items, "check"),
            ["\n    private import $::Reqs::check;"]
        );
        assert_eq!(
            import_fix_titles(&mut s, "    private import Facade::*;\n", "check"),
            ["Add import $::Reqs::check"]
        );
        // Without the import, the path is written as it is.
        let items = completion_in_m(&mut s, "package P {\n    ref w : \n}\n", 1, 12);
        assert_eq!(
            import_edits_of(&items, "check"),
            ["private import Reqs::check;\n    "]
        );
    }

    /// Inside the element holding it, a redefinition without a name of
    /// its own is what the name it redefines finds: at an operand in
    /// `SportCar`, `engine` is `SportCar`'s, named so, not `Car`'s.
    #[test]
    fn a_redefinition_is_offered_as_itself_inside_its_owner() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let text = "package P {\n    part def Car {\n        part engine;\n    }\n    \
                    part def SportCar :> Car {\n        part :>> engine {\n            \
                    attribute hp;\n        }\n        attribute y = \n    }\n}\n";
        let items = completion_in_m(&mut s, text, 8, 22);
        let engines: Vec<&serde_json::Value> =
            items.iter().filter(|i| i["label"] == "engine").collect();
        assert_eq!(engines.len(), 1, "{engines:?}");
        assert_eq!(
            engines[0]["detail"], "P::SportCar::engine",
            "{:?}",
            engines[0]
        );
    }

    /// A member of a type is offered by simple name wherever that name
    /// finds it, bare: inherited into a specialization or into a usage
    /// the type types — at an operand, a `perform`, or a level deeper —
    /// and brought in by an import of the type's members, of the one
    /// member, or of everything below the type.
    #[test]
    fn members_of_types_are_offered_wherever_their_names_find_them() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let lib = "package Lib {\n    action def Go;\n    part def Car {\n        \
                   attribute wheelbase;\n        part chassis {\n            \
                   attribute stiffness;\n        }\n        action drive : Go;\n    }\n}\n";
        for (body, want) in [
            (
                "    part def SportCar :> Lib::Car {\n        attribute x = ",
                "Lib::Car::wheelbase",
            ),
            (
                "    part car : Lib::Car {\n        attribute x = ",
                "Lib::Car::wheelbase",
            ),
            (
                "    part car : Lib::Car {\n        part inner {\n            attribute x = ",
                "Lib::Car::chassis",
            ),
            (
                "    part car : Lib::Car {\n        perform ",
                "Lib::Car::drive",
            ),
            (
                "    private import Lib::Car::*;\n    attribute x = ",
                "Lib::Car::wheelbase",
            ),
            (
                "    private import Lib::Car::wheelbase;\n    attribute x = ",
                "Lib::Car::wheelbase",
            ),
            (
                "    private import Lib::Car::**;\n    attribute x = ",
                "Lib::Car::chassis::stiffness",
            ),
        ] {
            let before = format!("{lib}package P {{\n{body}");
            let line = u32::try_from(before.matches('\n').count()).expect("short text");
            let character = u32::try_from(before.rsplit('\n').next().unwrap_or_default().len())
                .expect("short line");
            let open = body.matches('{').count();
            let text = format!("{before}\n{}}}\n", "    }\n".repeat(open));
            let items = completion_in_m(&mut s, &text, line, character);
            let label = want.rsplit("::").next().unwrap_or(want);
            let item = items.iter().find(|i| i["label"] == label);
            assert_eq!(
                item.map(|i| i["detail"].clone()),
                Some(serde_json::json!(want)),
                "{body:?}: {label} offered as {item:?}"
            );
            assert!(
                item.is_some_and(|i| i.get("additionalTextEdits").is_none()),
                "{body:?}: {item:?}"
            );
        }
    }

    /// An alias comes bare by its own name beside an import of a package
    /// that re-exports it, as beside an import of the package declaring
    /// it: the name finds the alias, which names the element it is an
    /// alias for — the one element, not another.
    #[test]
    fn an_alias_is_offered_through_a_package_re_exporting_it() {
        let mut s = library_server(
            "standard library package ISQBase { attribute def DurationValue; } \
             standard library package ISQSpaceTime { private import ISQBase::*; \
             alias TimeValue for DurationValue; } \
             standard library package ISQ { public import ISQBase::*; \
             public import ISQSpaceTime::*; }",
        );
        for import in ["ISQ::*", "Defs::*", "Outer::*"] {
            let text = format!(
                "package Outer {{\n    public import Defs::*;\n}}\n\
                 package Defs {{\n    public import ISQ::*;\n}}\n\
                 package P {{\n    private import {import};\n    attribute x : \n}}\n"
            );
            let cursor = text.find("attribute x : ").expect("cursor") + "attribute x : ".len();
            let line = u32::try_from(text[..cursor].matches('\n').count()).expect("short text");
            let character =
                u32::try_from(text[..cursor].rsplit('\n').next().unwrap_or_default().len())
                    .expect("short line");
            let items = completion_in_m(&mut s, &text, line, character);
            let found: Vec<_> = items.iter().filter(|i| i["label"] == "TimeValue").collect();
            assert_eq!(found.len(), 1, "{import}: {found:?}");
            assert_eq!(
                found[0]["detail"], "ISQSpaceTime::TimeValue",
                "{import}: {found:?}"
            );
            assert!(
                found[0].get("additionalTextEdits").is_none(),
                "{import}: {found:?}"
            );
        }
    }

    /// A member of a type comes bare through a package re-exporting it —
    /// one importing the type's members publicly, the one member, or
    /// everything below the type — beside an import of that package's
    /// members.
    #[test]
    fn members_of_types_are_offered_through_a_re_exporting_package() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let lib = "package Lib {\n    part def Car {\n        attribute wheelbaseQq;\n        \
                   part chassisQq {\n            attribute stiffnessQq;\n        }\n    }\n}\n";
        for (export, want) in [
            ("public import Lib::Car::*;", "Lib::Car::wheelbaseQq"),
            (
                "public import Lib::Car::wheelbaseQq;",
                "Lib::Car::wheelbaseQq",
            ),
            (
                "public import Lib::Car::**;",
                "Lib::Car::chassisQq::stiffnessQq",
            ),
        ] {
            let text = format!(
                "{lib}package Pub {{\n    {export}\n}}\n\
                 package P {{\n    private import Pub::*;\n    attribute x = \n}}\n"
            );
            let cursor = text.find("attribute x = ").expect("cursor") + "attribute x = ".len();
            let line = u32::try_from(text[..cursor].matches('\n').count()).expect("short text");
            let character =
                u32::try_from(text[..cursor].rsplit('\n').next().unwrap_or_default().len())
                    .expect("short line");
            let items = completion_in_m(&mut s, &text, line, character);
            let label = want.rsplit("::").next().unwrap_or(want);
            let item = items.iter().find(|i| i["label"] == label);
            assert_eq!(
                item.map(|i| i["detail"].clone()),
                Some(serde_json::json!(want)),
                "{export}: {label} offered as {item:?}"
            );
            assert!(
                item.is_some_and(|i| i.get("additionalTextEdits").is_none()),
                "{export}: {item:?}"
            );
        }
    }

    /// Inside elements nested in one another, a name finds the innermost
    /// one's own or inherited member first: in `vehicle_b`'s `engine`,
    /// `mass` and `fuelCmdPort` are the engine's, `range` the vehicle's,
    /// and in `vehicle_b`, a member redefining `range` hides the one it
    /// inherits.
    #[test]
    fn inherited_members_are_found_innermost_first() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let lib = "package Lib {\n    part def Engine {\n        attribute mass;\n        \
                   port fuelCmdPort;\n    }\n    part def Vehicle {\n        attribute mass;\n        \
                   port fuelCmdPort;\n        attribute range;\n        part engine : Engine;\n    \
                   }\n}\n";
        let engine = "    part vehicle_b : Lib::Vehicle {\n        part :>> engine {\n            \
                      attribute x = ";
        let vehicle = "    part vehicle_b : Lib::Vehicle {\n        attribute x = ";
        let redefined = "    part vehicle_b : Lib::Vehicle {\n        attribute :>> range = 5;\n        \
             attribute x = ";
        for (body, label, want) in [
            (engine, "mass", "Lib::Engine::mass"),
            (engine, "fuelCmdPort", "Lib::Engine::fuelCmdPort"),
            (engine, "range", "Lib::Vehicle::range"),
            (vehicle, "mass", "Lib::Vehicle::mass"),
            (redefined, "range", "P::vehicle_b::range"),
        ] {
            let before = format!("{lib}package P {{\n{body}");
            let line = u32::try_from(before.matches('\n').count()).expect("short text");
            let character = u32::try_from(before.rsplit('\n').next().unwrap_or_default().len())
                .expect("short line");
            let open = body.matches('{').count();
            let text = format!("{before}\n{}}}\n", "    }\n".repeat(open));
            let items = completion_in_m(&mut s, &text, line, character);
            let found: Vec<_> = items.iter().filter(|i| i["label"] == label).collect();
            assert_eq!(found.len(), 1, "{body:?}: {label} offered as {found:?}");
            assert_eq!(found[0]["detail"], want, "{body:?}: {found:?}");
            assert!(found[0].get("additionalTextEdits").is_none(), "{found:?}");
        }
    }

    /// The ends a connection names as it connects them are its own
    /// features: inside it, such an end hides the member of its type it
    /// redefines, which is not offered for its name there.
    #[test]
    fn a_connections_named_ends_hide_what_its_type_declares() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let text = "package Lib {\n    port def P;\n    interface def I {\n        end a : P;\n        \
                    end b : P;\n    }\n}\n\
                    package M {\n    part x {\n        port pa : Lib::P;\n    }\n    part y {\n        \
                    port pb : Lib::P;\n    }\n    \
                    interface i : Lib::I connect a ::> x.pa to b ::> y.pb {\n        attribute z = \n    \
                    }\n}\n";
        let items = completion_in_m(&mut s, text, 15, 22);
        let ends: Vec<_> = items
            .iter()
            .filter(|i| i["detail"] == "Lib::I::a" || i["detail"] == "Lib::I::b")
            .collect();
        assert!(ends.is_empty(), "{ends:?}");
    }

    /// Definitions specializing each other in a cycle pass on what each
    /// declares, the cycle cut where it closes.
    #[test]
    fn inherited_members_come_through_a_specialization_cycle() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let text = "package Lib {\n    part def A :> B {\n        attribute fromA;\n    }\n    \
                    part def B :> A {\n        attribute fromB;\n    }\n}\n\
                    package P {\n    part x : Lib::A {\n        attribute y = \n    }\n}\n";
        let items = completion_in_m(&mut s, text, 10, 22);
        for (label, want) in [("fromA", "Lib::A::fromA"), ("fromB", "Lib::B::fromB")] {
            let found: Vec<_> = items.iter().filter(|i| i["label"] == label).collect();
            assert_eq!(found.len(), 1, "{label}: {found:?}");
            assert_eq!(found[0]["detail"], want);
        }
    }

    /// A name an inherited member takes at the cursor is offered as that
    /// member, bare — not as a library element of the same name with an
    /// import the member would shadow.
    #[test]
    fn an_inherited_member_keeps_its_name_from_the_library() {
        let mut s = library_server(
            "standard library package ISQSpaceTime { attribute speed; } \
             standard library package ISQ { public import ISQSpaceTime::*; }",
        );
        let text = "package Lib {\n    part def Car {\n        attribute speed;\n    }\n}\n\
                    package P {\n    part def SportCar :> Lib::Car {\n        attribute x = \n    \
                    }\n}\n";
        let items = completion_in_m(&mut s, text, 7, 22);
        let speeds: Vec<_> = items.iter().filter(|i| i["label"] == "speed").collect();
        assert_eq!(speeds.len(), 1, "{speeds:?}");
        assert_eq!(speeds[0]["detail"], "Lib::Car::speed");
        assert!(speeds[0].get("additionalTextEdits").is_none(), "{speeds:?}");
    }

    /// Where the enclosing element's features are named (`:>>`), each
    /// label comes once, an inherited member's too: the feature the
    /// position names, or the member as the symbol tables hold it.
    #[test]
    fn an_inherited_member_is_offered_once_where_features_are_named() {
        let mut s = library_server("standard library package Kit { class Crate; }");
        let text = "package Lib {\n    part def Car {\n        attribute speed;\n        \
                    part wheel;\n    }\n}\n\
                    package P {\n    part def SportCar :> Lib::Car {\n        part :>> \n    \
                    }\n}\n";
        let items = completion_in_m(&mut s, text, 8, 17);
        let labels = completion_labels(&items);
        for label in ["speed", "wheel"] {
            assert_eq!(
                labels.iter().filter(|l| **l == label).count(),
                1,
                "{label}: {labels:?}"
            );
        }
        let unique: std::collections::HashSet<&&str> = labels.iter().collect();
        assert_eq!(unique.len(), labels.len(), "{labels:?}");
    }

    /// A recursive import brings in what the elements below its
    /// namespace inherit from the workspace's types — `own`, through
    /// `c : Defs::M` — but not what a library type passes on, which
    /// also comes to elements no declaration shows inheriting it, so
    /// that the name may denote several.
    #[test]
    fn a_recursive_import_brings_in_what_the_elements_below_inherit() {
        let mut s =
            library_server("standard library package L { part def T { attribute shared; } }");
        let text = "package Defs {\n    part def M {\n        attribute own;\n    }\n}\n\
                    package Config {\n    part a : L::T;\n    part c : Defs::M;\n}\n\
                    package Analysis {\n    public import Config::**;\n}\n\
                    package Q {\n    attribute y : Analysis::\n}\n";
        let items = completion_in_m(&mut s, text, 13, 28);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"own") && !labels.contains(&"shared"),
            "{labels:?}"
        );
    }

    /// A member of a type has no path an import could name: where its
    /// simple name does not find it — beside `Cars`, outside `Car` and
    /// what inherits from it — it is not offered; inside its owner it
    /// is.
    #[test]
    fn members_of_types_are_offered_by_name_only_where_their_names_find_them() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/cars.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Cars {\n    part def Car {\n        \
                                          part wheel;\n    }\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    alias a for \n}\n", 1, 16);
        assert!(!completion_labels(&items).contains(&"wheel"));
        let items = completion_in_m(
            &mut s,
            "package Trucks {\n    part def Truck {\n        part axle;\n        \
             alias a for \n    }\n}\n",
            3,
            20,
        );
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"axle") && !labels.contains(&"wheel"),
            "{labels:?}"
        );
    }

    /// A member of a private package has no path outside the namespace
    /// owning that package: it is offered there (inside `Outer`, with an
    /// import), and elsewhere only through a package re-exporting it —
    /// `Deep2` with an import of `Outer2::Deep2` — never `Deep`: not by
    /// simple name, through an import of its package's members, in an
    /// import path, by the "Add import" fix, after its package's
    /// qualifier, nor through a recursive import of `Outer3`, which
    /// shows its clients nothing of a private package.
    #[test]
    fn members_of_a_private_package_are_offered_only_where_they_resolve() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/nested.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Outer {\n    private package Inner {\n        \
                                          part def Deep;\n    }\n}\n\
                                          package Outer2 {\n    private package Inner2 {\n        \
                                          part def Deep2;\n    }\n    public import Inner2::*;\n}\n\
                                          package Outer3 {\n    private package Inner3 {\n        \
                                          part def Deep3;\n    }\n}\n\
                                          package Facade3 {\n    public import Outer3::**;\n}\n"}}}),
        );
        for (imports, edit) in [
            ("", "private import Outer2::Deep2;\n    "),
            (
                "    private import Outer::Inner::*;\n",
                "\n    private import Outer2::Deep2;",
            ),
        ] {
            let text = format!("package P {{\n{imports}    ref w : \n}}\n");
            let line = text
                .lines()
                .position(|l| l.contains("ref w"))
                .expect("line");
            let line = u32::try_from(line).expect("line");
            let items = completion_in_m(&mut s, &text, line, 12);
            assert!(import_edits_of(&items, "Deep").is_empty(), "{imports:?}");
            assert_eq!(import_edits_of(&items, "Deep2"), [edit], "{imports:?}");
        }
        let items = completion_in_m(&mut s, "package P {\n    private import \n}\n", 1, 19);
        let labels = completion_labels(&items);
        assert!(
            !labels.contains(&"Deep") && labels.contains(&"Deep2"),
            "{labels:?}"
        );
        assert!(import_fix_titles(&mut s, "", "Deep").is_empty());
        assert_eq!(
            import_fix_titles(&mut s, "", "Deep2"),
            ["Add import Outer2::Deep2"]
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    ref w : Outer::Inner::\n}\n",
            1,
            26,
        );
        assert!(!completion_labels(&items).contains(&"Deep"));
        let items = completion_in_m(&mut s, "package P {\n    ref w : Facade3::\n}\n", 1, 21);
        assert!(!completion_labels(&items).contains(&"Deep3"));
        // Inside `Outer`, its path resolves.
        let items = completion_in_m(
            &mut s,
            "package Outer {\n    private package Inner {\n        part def Deep;\n    }\n    \
             ref w : \n}\n",
            4,
            12,
        );
        assert_eq!(
            import_edits_of(&items, "Deep"),
            ["private import Outer::Inner::Deep;\n    "]
        );
    }

    /// An `import all` brings in a namespace's members whatever their
    /// visibility, so a public one re-exports them all: `AllFacade::`
    /// lists `Secret`, which `PlainFacade::` does not, and an import of
    /// `AllFacade`'s members lets `Secret` be named bare.
    #[test]
    fn a_public_import_all_reexports_every_member() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/hidden.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Hidden {\n    private part def Secret;\n    \
                                          part def Open;\n}\npackage AllFacade {\n    \
                                          public import all Hidden::*;\n}\n\
                                          package PlainFacade {\n    \
                                          public import Hidden::*;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : AllFacade::\n}\n", 1, 24);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && labels.contains(&"Secret"),
            "{labels:?}"
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    part w : PlainFacade::\n}\n",
            1,
            26,
        );
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && !labels.contains(&"Secret"),
            "{labels:?}"
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import AllFacade::*;\n    part w : \n}\n",
            2,
            13,
        );
        let secret = items
            .iter()
            .find(|i| i["label"] == "Secret")
            .expect("offered through the facade's `import all`");
        assert!(secret.get("additionalTextEdits").is_none(), "{secret}");
    }

    /// An `import all` path names a namespace's members whatever their
    /// visibility: after `import all Hidden::` its private members are
    /// listed, after `import Hidden::` they are not.
    #[test]
    fn an_import_all_path_lists_every_member() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/hidden.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Hidden {\n    private part def Secret;\n    \
                                          protected part def Guarded;\n    \
                                          part def Open;\n}\n"}}}),
        );
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import all Hidden::\n}\n",
            1,
            31,
        );
        let labels = completion_labels(&items);
        for label in ["Secret", "Guarded", "Open"] {
            assert!(labels.contains(&label), "{label}: {labels:?}");
        }
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import Hidden::\n}\n",
            1,
            27,
        );
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"Open") && !labels.contains(&"Secret") && !labels.contains(&"Guarded"),
            "{labels:?}"
        );
    }

    /// A library package's private member is a name for a model only
    /// through an `import all`: named bare where one is in scope, and
    /// listed after `import all Base::`.
    #[test]
    fn private_library_members_come_in_through_import_all() {
        let mut s =
            library_server("standard library package Base { class Open; private class Hidden; }");
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import all Base::*;\n    ref w : \n}\n",
            2,
            12,
        );
        let hidden = items
            .iter()
            .find(|i| i["label"] == "Hidden")
            .expect("offered through the `import all`");
        assert!(hidden.get("additionalTextEdits").is_none(), "{hidden}");
        let items = completion_in_m(
            &mut s,
            "package P {\n    private import all Base::\n}\n",
            1,
            29,
        );
        assert!(completion_labels(&items).contains(&"Hidden"));
    }

    /// A library package's private member is no name for a model: not
    /// offered by simple name, in an import path, after its package's
    /// qualifier, or by the "Add import" fix.
    #[test]
    fn private_library_members_are_not_offered() {
        let mut s = library_server(
            "standard library package Base { class Open; private class Hidden; \
             protected class Kept; }",
        );
        let items = completion_in_m(
            &mut s,
            "package P {
    ref w : 
}
",
            1,
            12,
        );
        let labels = completion_labels(&items);
        assert!(labels.contains(&"Open"), "{labels:?}");
        assert!(
            !labels.contains(&"Hidden") && !labels.contains(&"Kept"),
            "{labels:?}"
        );
        let items = completion_in_m(
            &mut s,
            "package P {
    private import 
}
",
            1,
            19,
        );
        let labels = completion_labels(&items);
        assert!(labels.contains(&"Open"), "{labels:?}");
        assert!(
            !labels.contains(&"Hidden") && !labels.contains(&"Kept"),
            "{labels:?}"
        );
        let items = completion_in_m(
            &mut s,
            "package P {
    part w : Base::
}
",
            1,
            19,
        );
        assert_eq!(completion_labels(&items), ["Open"]);
        assert!(import_fix_titles(&mut s, "", "Hidden").is_empty());
    }

    /// A single-member re-export routes an import of that member alone:
    /// `Top` re-exports `Deep::Inner::Pin`, so an inserted import names
    /// `Top::Pin`, while `Inner`'s other members keep their own paths.
    #[test]
    fn single_member_reexports_route_that_member() {
        let mut s = library_server(
            "standard library package Deep { package Inner { class Pin; class Peg; } } \
             standard library package Top { public import Deep::Inner::Pin; }",
        );
        let titles = import_fix_titles(&mut s, "", "Pin");
        assert_eq!(titles, ["Add import Top::Pin"]);
        let titles = import_fix_titles(&mut s, "", "Peg");
        assert_eq!(titles, ["Add import Deep::Inner::Peg"]);
        let items = completion_in_m(&mut s, "package P {\n    private import P\n}\n", 1, 20);
        let path = |label: &str| -> Vec<&str> {
            items
                .iter()
                .filter(|i| i["label"] == label)
                .filter_map(|i| i["textEdit"]["newText"].as_str())
                .collect()
        };
        assert_eq!(path("Pin"), ["Top::Pin"]);
        assert_eq!(path("Peg"), ["Deep::Inner::Peg"]);
    }

    /// Typing in one document costs a completion request that
    /// document's symbols alone: the rest of the workspace is not
    /// re-read, and what its namespaces and the library's make visible,
    /// and which packages route their members, is not worked out again
    /// — until another document changes.
    #[test]
    fn a_keystroke_reworks_only_its_own_document() {
        let mut s = library_server(
            "standard library package Base { class Widget; class Gadget; } \
             standard library package Facade { public import Base::*; }",
        );
        let open = |s: &mut PushServer, uri: &str, version: i32, text: &str| {
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {"uri": uri, "languageId": "sysml",
                                                "version": version, "text": text}}}),
            );
        };
        let model = "package Model {\n    public import Facade::*;\n    package Parts {\n        \
                     part def Wheel;\n    }\n    public import Parts::*;\n}\n";
        open(&mut s, "file:///w/model.sysml", 1, model);
        let doc = |typed: &str| format!("package P {{\n    part w : {typed}\n}}\n");
        let complete = |s: &mut PushServer, typed: &str| {
            let out = responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                               "position": {"line": 1,
                                            "character": 13 + typed.len()}}}),
            );
            out[0]["result"].as_array().expect("items").len()
        };
        let change = |s: &mut PushServer, uri: &str, version: i32, text: &str| {
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange",
                    "params": {"textDocument": {"uri": uri, "version": version},
                               "contentChanges": [{"text": text}]}}),
            );
        };
        open(&mut s, "file:///w/m.sysml", 1, &doc(""));
        assert!(complete(&mut s, "") > 0);
        let reset = || crate::nav::WORK.with(|w| w.set([0; 3]));
        let work = || crate::nav::WORK.with(std::cell::Cell::get);

        // A keystroke: the document's own symbols, nothing else.
        reset();
        change(&mut s, "file:///w/m.sysml", 2, &doc("W"));
        assert!(complete(&mut s, "W") > 0);
        assert_eq!(work(), [2, 0, 0], "symbols indexed, names, route walks");

        // Another document changed: the rest of the workspace is read
        // anew, and what depends on it worked out again.
        change(
            &mut s,
            "file:///w/model.sysml",
            2,
            &model.replace("Wheel", "Tire"),
        );
        reset();
        assert!(complete(&mut s, "W") > 0);
        let [symbols, names, walks] = work();
        assert!(symbols > 2 && names > 0 && walks > 0, "{:?}", work());
    }

    /// An import target reached through other packages' re-exports
    /// resolves however long the chain: `Z` imports `A::Deep`, which `A`
    /// re-exports from `B::X`, which `B` re-exports from `C`.
    #[test]
    fn import_targets_resolve_through_any_chain() {
        let mut s = library_server(
            "standard library package C { package X { class Deep; } } \
             standard library package B { public import C::*; } \
             standard library package A { public import B::X::*; } \
             standard library package Z { public import A::Deep; }",
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : Z::\n}\n", 1, 16);
        assert_eq!(completion_labels(&items), ["Deep"]);
    }

    /// A document reopened with new text at the version it had counts as
    /// changed: completion offers what the new text declares.
    #[test]
    fn a_document_reopened_at_its_old_version_is_read_again() {
        let mut s = library_server("standard library package Lib { class Unused; }");
        let open = |s: &mut PushServer, text: &str| {
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {"uri": "file:///w/model.sysml", "languageId": "sysml",
                                                "version": 1, "text": text}}}),
            );
        };
        open(&mut s, "package Model { part def Wheel; }");
        let labels = |s: &mut PushServer| -> Vec<String> {
            let items = completion_in_m(s, "package P {\n    part w : \n}\n", 1, 13);
            completion_labels(&items)
                .into_iter()
                .map(str::to_string)
                .collect()
        };
        assert!(labels(&mut s).contains(&"Wheel".to_string()));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didClose",
                "params": {"textDocument": {"uri": "file:///w/model.sysml"}}}),
        );
        open(&mut s, "package Model { part def Tire; }");
        let offered = labels(&mut s);
        assert!(
            offered.contains(&"Tire".to_string()) && !offered.contains(&"Wheel".to_string()),
            "{offered:?}"
        );
    }

    /// Another document's import can name a namespace the document being
    /// completed declares: what it re-exports is still offered, and an
    /// import through it still admits and routes.
    #[test]
    fn imports_into_the_document_being_completed_still_count() {
        let mut s = library_server("standard library package Lib { class Unused; }");
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                "params": {"textDocument": {"uri": "file:///w/uses.sysml", "languageId": "sysml",
                                            "version": 1,
                                            "text": "package Uses {\n    public import Defs::*;\n}\n"}}}),
        );
        let items = completion_in_m(
            &mut s,
            "package Defs {\n    part def Engine;\n}\npackage P {\n    part e : Uses::\n}\n",
            4,
            19,
        );
        let labels = completion_labels(&items);
        assert!(labels.contains(&"Engine"), "{labels:?}");
    }

    /// An alias completes as what it names: with its target's kind (and
    /// icon) when the target is a sibling — by name or by short name,
    /// through further aliases — and with the module kind when a
    /// syntax-tier lookup cannot follow it. The outline still shows an
    /// alias as one.
    #[test]
    fn aliases_complete_as_what_they_name() {
        use lsp_types::CompletionItemKind as K;
        let mut s = library_server(
            "standard library package Kit { class Bolt; feature <m> metre; function twice; \
             package Parts; alias Fastener for Bolt; alias Meter for m; alias Double for twice; \
             alias Stock for Parts; alias Screw for Fastener; alias Lost for Missing; \
             alias Far for Other::Thing; }",
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : Kit::\n}\n", 1, 18);
        for (label, kind) in [
            ("Fastener", K::CLASS),
            ("Meter", K::VARIABLE),
            ("Double", K::FUNCTION),
            ("Stock", K::MODULE),
            ("Screw", K::CLASS),
            ("Lost", K::MODULE),
            ("Far", K::MODULE),
        ] {
            let item = items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"));
            assert_eq!(item["kind"], serde_json::json!(kind), "{item}");
        }

        // A workspace alias, and the outline of its document.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/cars.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package Cars {\n    part def Car;\n    alias Auto for Car;\n}\n"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    part w : \n}\n", 1, 13);
        let auto = items
            .iter()
            .find(|i| i["label"] == "Auto")
            .expect("Auto offered");
        assert_eq!(auto["kind"], serde_json::json!(K::CLASS), "{auto}");
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": "file:///w/cars.sysml"}}}),
        );
        let outline = &out[0]["result"][0]["children"];
        assert_eq!(outline[1]["name"], "Auto");
        assert_eq!(
            outline[1]["kind"],
            serde_json::json!(lsp_types::SymbolKind::MODULE)
        );
    }

    /// A function named by an operator (`'+'`, `'['`) or a word
    /// operator (`'not'`), and an alias naming one (`alias '*' for
    /// times;`), is written as that operator, never by name:
    /// unqualified completion — the flat list and an import path's
    /// first segment — leaves it out, while a qualifier still lists
    /// it. The element decides, not the spelling: a unit spelled `%`
    /// stays, as a short name or as an alias, and so does a function
    /// whose quoted name holds a word (`'cartesian+'`).
    #[test]
    fn operator_functions_complete_only_through_a_qualifier() {
        // What an item offers from a package: its label, by the
        // qualified path in its detail.
        let from = |items: &[serde_json::Value], package: &str| -> Vec<String> {
            items
                .iter()
                .filter(|i| {
                    i["detail"]
                        .as_str()
                        .is_some_and(|d| d.starts_with(&format!("{package}::")))
                })
                .filter_map(|i| i["label"].as_str().map(str::to_string))
                .collect()
        };
        for units in [
            "feature <'%'> percent;",
            "feature percent; alias '%' for percent;",
        ] {
            let mut s = library_server(&format!(
                "standard library package Ops {{ function '%'; function '+'; function '['; \
                 function 'not'; predicate '<'; function 'cartesian+'; function sum; \
                 function times; alias '*' for times; }} \
                 standard library package Units {{ {units} }}"
            ));

            let items = completion_in_m(&mut s, "package P {\n    attribute a = \n}\n", 1, 18);
            assert_eq!(
                from(&items, "Ops"),
                ["cartesian+", "sum", "times"],
                "{units}"
            );
            assert_eq!(from(&items, "Units"), ["percent", "%"], "{units}");

            let items = completion_in_m(&mut s, "package P {\n    private import \n}\n", 1, 19);
            assert_eq!(
                from(&items, "Ops"),
                ["cartesian+", "sum", "times"],
                "{units}"
            );
            assert_eq!(from(&items, "Units"), ["percent", "%"], "{units}");
            assert!(completion_labels(&items).contains(&"Ops"));

            let items = completion_in_m(&mut s, "package P {\n    attribute a = Ops::\n}\n", 1, 23);
            assert_eq!(
                completion_labels(&items),
                ["%", "+", "[", "not", "<", "cartesian+", "sum", "times", "*"]
            );
        }
    }

    /// Workspace symbol search finds declarations: an `import` or
    /// `expose` member declares nothing and is not listed, while the
    /// declarations around it and an alias are.
    #[test]
    fn workspace_symbols_skip_import_members() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    private import MiniLib::*;\n    \
                                          alias Part for MiniLib::Widget;\n    \
                                          view v { expose OtherLib::*; }\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "workspace/symbol",
                "params": {"query": ""}}),
        );
        let names: Vec<&str> = out[0]["result"]
            .as_array()
            .expect("symbols")
            .iter()
            .filter_map(|s| s["name"].as_str())
            .collect();
        assert_eq!(names, ["P", "Part", "v"]);
    }

    /// Workspace symbol search finds names: an anonymous member (the
    /// outline's `«part»`) is not listed, while the named members
    /// inside it are.
    #[test]
    fn workspace_symbols_skip_anonymous_members() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    part def V {\n        part : V {\n            \
                                          attribute inner;\n        }\n    }\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "workspace/symbol",
                "params": {"query": ""}}),
        );
        let names: Vec<&str> = out[0]["result"]
            .as_array()
            .expect("symbols")
            .iter()
            .filter_map(|s| s["name"].as_str())
            .collect();
        assert_eq!(names, ["P", "V", "inner"]);
    }

    /// Keywords are the only keyword-kind items: metadata definitions
    /// and usages complete with a kind of their own.
    #[test]
    fn only_keywords_complete_as_keywords() {
        let mut s = two_package_server();
        let text = "package P {\n    metadata def Safety;\n    part w { metadata tag : Safety; }\n    \n}\n";
        // A type position offers the definition, an expression beside
        // the usage the usage and the literal keywords.
        let mut items = completion_in_m(&mut s, &text.replace("    \n}", "    ref x : \n}"), 3, 12);
        items.extend(completion_in_m(
            &mut s,
            &text.replace("Safety; }", "Safety;\n        attribute y = \n    }"),
            3,
            22,
        ));
        let keyword = serde_json::json!(lsp_types::CompletionItemKind::KEYWORD);
        let not_keywords: Vec<&str> = items
            .iter()
            .filter(|i| i["kind"] == keyword)
            .filter_map(|i| i["label"].as_str())
            .filter(|l| !crate::tokens::VOCABULARY.contains(l))
            .collect();
        assert!(
            not_keywords.is_empty(),
            "names with the keyword kind: {not_keywords:?}"
        );
        let reference = serde_json::json!(lsp_types::CompletionItemKind::REFERENCE);
        for name in ["Safety", "tag"] {
            let item = items
                .iter()
                .find(|i| i["label"] == name)
                .unwrap_or_else(|| panic!("{name} offered"));
            assert_eq!(item["kind"], reference, "{item}");
        }
    }

    /// The workspace's own operator functions are held to the same
    /// rule as the library's: out of the flat list, listed after a
    /// qualifier.
    #[test]
    fn workspace_operator_functions_complete_only_through_a_qualifier() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/ops.kerml", "languageId": "kerml",
                                 "version": 1,
                                 "text": "package WOps { function '+'; function plus; }"}}}),
        );
        let items = completion_in_m(&mut s, "package P {\n    attribute a = \n}\n", 1, 18);
        let labels = completion_labels(&items);
        assert!(
            labels.contains(&"plus") && !labels.contains(&"+"),
            "{labels:?}"
        );
        let items = completion_in_m(&mut s, "package P {\n    attribute a = WOps::\n}\n", 1, 24);
        assert_eq!(completion_labels(&items), ["+", "plus"]);
    }

    /// The completion items a fresh [`two_package_server`] answers at
    /// the `|` in `marked`, opened (marker removed) as a `.sysml`
    /// document.
    fn complete_at(marked: &str) -> Vec<serde_json::Value> {
        complete_in("file:///w/m.sysml", marked)
    }

    /// [`complete_at`] for a document opened under `uri`.
    fn complete_in(uri: &str, marked: &str) -> Vec<serde_json::Value> {
        let at = marked.find('|').expect("cursor marker");
        let text = marked.replacen('|', "", 1);
        let line = marked[..at].matches('\n').count();
        let character = at - marked[..at].rfind('\n').map_or(0, |i| i + 1);
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "sysml",
                                 "version": 1, "text": text}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": line, "character": character}}}),
        );
        out[0]["result"]
            .as_array()
            .expect("completion items")
            .clone()
    }

    /// Inside a comment, a note, a documentation body, or a string
    /// literal nothing is offered — not even when a trigger character
    /// (`.`, `:`) opened the request — while a quoted name being typed
    /// completes as any name does.
    #[test]
    fn no_completions_in_comments_or_strings() {
        for marked in [
            "package P {\n    part def V {\n        doc /* A vehicle part.| */\n    }\n}\n",
            "package P {\n    // TODO:|\n}\n",
            "package P {\n    //* see Widget.| */\n}\n",
            "package P {\n    comment about P /* see MiniLib::| */\n}\n",
            "package P {\n    attribute s = \"v1.|\";\n}\n",
        ] {
            assert_eq!(
                complete_at(marked),
                Vec::<serde_json::Value>::new(),
                "{marked:?}"
            );
        }
        for marked in [
            "package P {\n    ref w : 'Widg|';\n}\n",
            "package P {\n    /* done */ ref w : Widg|\n}\n",
        ] {
            let items = complete_at(marked);
            assert!(completion_labels(&items).contains(&"Widget"), "{marked:?}");
        }
    }

    /// A number's decimal point or exponent and a range bound are no
    /// place for a name: nothing is offered there.
    #[test]
    fn no_completions_in_numbers_or_range_bounds() {
        for marked in [
            "package P {\n    attribute x = 5.|\n}\n",
            "package P {\n    attribute x = 5.4|\n}\n",
            "package P {\n    attribute x = 1.5e|\n}\n",
            "package P {\n    attribute x = 12|\n}\n",
            "package P {\n    part ws : Widget [0.|\n}\n",
            "package P {\n    part ws : Widget [0..|\n}\n",
            "package P {\n    part ws : Widget [1..*|\n}\n",
        ] {
            assert_eq!(
                complete_at(marked),
                Vec::<serde_json::Value>::new(),
                "{marked:?}"
            );
        }
        // A bound may name a feature; a product takes any operand.
        for marked in [
            "package P {\n    attribute count;\n    part ws : Widget [0..cou|\n}\n",
            "package P {\n    attribute count;\n    attribute x = 2 * cou|\n}\n",
        ] {
            let items = complete_at(marked);
            assert!(completion_labels(&items).contains(&"count"), "{marked:?}");
        }
    }

    /// Where the word being typed is a name the statement declares, no
    /// element's name is offered — accepting one would replace the new
    /// name — only the keywords that may stand there instead. Positions
    /// that take references keep their names.
    #[test]
    fn declared_names_are_offered_no_element_names() {
        for (marked, keywords) in [
            ("package P {\n    abstract part def Widg|\n}\n", vec![]),
            ("package P {\n    part Widg|\n}\n", vec!["def", "redefines"]),
            ("package P {\n    part def <Widg|\n}\n", vec![]),
            (
                "package P {\n    action def A {\n        in item Widg|\n    }\n}\n",
                vec!["redefines"],
            ),
            (
                "package P {\n    enum def E {\n        Widg|\n    }\n}\n",
                vec![
                    "comment",
                    "doc",
                    "enum",
                    "language",
                    "locale",
                    "metadata",
                    "private",
                    "protected",
                    "public",
                    "rep",
                ],
            ),
        ] {
            let items = complete_at(marked);
            assert_eq!(completion_labels(&items), keywords, "{marked:?}");
            assert!(items.iter().all(|i| i["kind"] == 14), "keywords: {items:?}");
        }
        for (marked, name) in [
            (
                "package P {\n    action widgetAction;\n    perform widg|\n}\n",
                "widgetAction",
            ),
            ("package P {\n    alias A for Widg|\n}\n", "Widget"),
            (
                "package P {\n    state widgetState;\n    transition widg|\n}\n",
                "widgetState",
            ),
            ("package P {\n    ref w : Widg|\n}\n", "Widget"),
        ] {
            let items = complete_at(marked);
            assert!(completion_labels(&items).contains(&name), "{marked:?}");
        }

        // A KerML document reads its own grammar's declarations; a
        // SysML keyword there is a name like any other.
        let kerml = "file:///w/m.kerml";
        let items = complete_in(kerml, "package P {\n    class Widg|\n}\n");
        assert_eq!(completion_labels(&items), vec!["all"]);
        for marked in [
            "package P {\n    feature w : Widg|\n}\n",
            "package P {\n    part Widg|\n}\n",
        ] {
            let items = complete_in(kerml, marked);
            assert!(completion_labels(&items).contains(&"Widget"), "{marked:?}");
        }
    }

    /// A comment above the statement being completed is not part of
    /// it: a `[` in the comment asks for no `]` on accepting.
    #[test]
    fn a_bracket_in_a_comment_above_needs_no_repair() {
        let items = complete_at("package P {\n    /* note; [draft */\n    ref x : Widg|\n}\n");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        assert!(widget["textEdit"].is_null(), "no `]` repair: {widget}");
    }

    /// An `import` in a note above the statement being completed does
    /// not make it an import: the name inserts bare, with its import.
    #[test]
    fn an_import_in_a_note_above_is_no_import_statement() {
        let items =
            complete_at("package P {\n    // import the library below\n    ref w : Widg|\n}\n");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        assert!(widget["textEdit"].is_null(), "no import path: {widget}");
        assert_eq!(
            widget["additionalTextEdits"][0]["newText"],
            "private import MiniLib::Widget;\n    "
        );
    }

    /// A `;` in a comment above a feature chain does not start the
    /// statement inside the comment: the text cut out for the semantic
    /// session is the statement alone, so the chain still resolves.
    #[test]
    fn a_terminator_in_a_comment_above_keeps_chains_resolving() {
        let items = complete_at(
            "package P {\n    part def Tank { attribute level; }\n    part t : Tank;\n    \
             /* note; see below */\n    attribute x = t.|\n}\n",
        );
        assert_eq!(completion_labels(&items), vec!["level", "metadata"]);
    }

    /// A model with a definition of every kind the positions below
    /// take, opened beside the document under test.
    const VEHICLE_MODEL: &str = "package VehicleModel {\n\
        \x20   private import ScalarValues::*;\n\
        \x20   private import ISQ::*;\n\
        \x20   private import SI::*;\n\
        \x20   enum def Color { enum red; enum green; }\n\
        \x20   attribute def Speed :> ISQ::SpeedValue;\n\
        \x20   item def Fuel;\n\
        \x20   item def Signal;\n\
        \x20   port def FuelPort { out item fuel : Fuel; }\n\
        \x20   interface def FuelInterface { end a : FuelPort; end b : ~FuelPort; }\n\
        \x20   part def Vehicle { attribute mass : ISQ::MassValue; port fuelIn : ~FuelPort; }\n\
        \x20   part def Car :> Vehicle;\n\
        \x20   part def Driver;\n\
        \x20   action def Drive;\n\
        \x20   state def VehicleStates { state off; state on; }\n\
        \x20   calc def KineticEnergy { in m : ISQ::MassValue; }\n\
        \x20   requirement def MaxMassReq;\n\
        \x20   metadata def Safety;\n\
        }\n";

    /// A push server over the standard library with [`VEHICLE_MODEL`] open.
    fn standard_library_server() -> PushServer {
        let mut files = Vec::new();
        sysmlv2_testkit::collect_files(&sysmlv2_testkit::library_dir(), &mut files);
        let units = files
            .iter()
            .map(|f| {
                let text = std::fs::read_to_string(f).expect("library unit");
                (f.display().to_string(), text)
            })
            .collect();
        let mut s = PushServer::with_library_sources(units, None);
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/vehicles.sysml", "languageId": "sysml",
                                 "version": 1, "text": VEHICLE_MODEL}}}),
        );
        s
    }

    /// The labels an editor lists at the `|` in `body` — a member
    /// position of `part def P` in a package importing the vehicle
    /// model and the quantities — narrowed to those starting with the
    /// word typed before the cursor, in the order it lists them:
    /// `sortText`, then label.
    fn listed(s: &mut PushServer, uri: &str, body: &str) -> (Vec<String>, Vec<serde_json::Value>) {
        let header = "package Survey {\n    private import VehicleModel::*;\n    \
                      private import ISQ::*;\n    private import SI::*;\n    \
                      private import ScalarValues::*;\n    part def P {\n        ";
        let marked = format!("{header}{body}\n    }}\n}}\n");
        let at = marked.find('|').expect("cursor marker");
        let text = marked.replacen('|', "", 1);
        let line = marked[..at].matches('\n').count();
        let character = at - marked[..at].rfind('\n').map_or(0, |i| i + 1);
        let typed: String = marked[..at]
            .chars()
            .rev()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "sysml", "version": 1, "text": text}}}),
        );
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": line, "character": character}}}),
        );
        let items = out[0]["result"]
            .as_array()
            .expect("completion items")
            .clone();
        // Closed again: its unfinished statement must not keep the next
        // document's semantic session from building.
        responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {
                "textDocument": {"uri": uri}}}),
        );
        let mut shown: Vec<&serde_json::Value> = items
            .iter()
            .filter(|i| {
                let label = i["label"].as_str().unwrap_or_default().to_lowercase();
                label.starts_with(&typed.to_lowercase())
            })
            .collect();
        shown.sort_by_key(|i| {
            (
                i["sortText"].as_str().unwrap_or_default().to_string(),
                i["label"].as_str().unwrap_or_default().to_string(),
            )
        });
        let labels = shown
            .iter()
            .map(|i| i["label"].as_str().unwrap_or_default().to_string())
            .collect();
        (labels, items)
    }

    /// At a type position the list holds the definitions a usage of the
    /// statement's kind may be typed by, the best-fitting first — no
    /// keyword, no unit, no definition of another kind.
    #[test]
    fn typing_positions_offer_the_kinds_definitions() {
        let mut s = standard_library_server();
        let has =
            |items: &[serde_json::Value], label: &str| items.iter().any(|i| i["label"] == label);
        let keywordless = |items: &[serde_json::Value]| items.iter().all(|i| i["kind"] != 14);

        let (shown, items) = listed(&mut s, "file:///w/a.sysml", "attribute x : Rea|");
        assert!(shown[..3].contains(&"Real".to_string()), "{shown:?}");
        assert!(keywordless(&items));
        assert!(has(&items, "MassValue") && has(&items, "Color"));
        assert!(
            !has(&items, "kg") && !has(&items, "Vehicle"),
            "no units, no part definitions"
        );

        let (shown, items) = listed(&mut s, "file:///w/b.sysml", "part p : Veh|");
        assert_eq!(
            shown.first().map(String::as_str),
            Some("Vehicle"),
            "{shown:?}"
        );
        assert!(keywordless(&items));
        assert!(!has(&items, "Speed") && !has(&items, "MassValue") && !has(&items, "kg"));

        let (shown, items) = listed(&mut s, "file:///w/c.sysml", "port p : ~Fu|");
        assert_eq!(shown, vec!["FuelPort"], "port definitions only");
        assert!(!has(&items, "Fuel") && !has(&items, "FuelInterface"));

        let (shown, _) = listed(&mut s, "file:///w/d.sysml", "action d : Dr|");
        assert_eq!(
            shown.first().map(String::as_str),
            Some("Drive"),
            "{shown:?}"
        );
        assert!(
            !shown.contains(&"Driver".to_string()),
            "a part definition types no action"
        );
    }

    /// After `:>` on a definition: definitions of its kind first, those
    /// of the kinds it specializes after — no unit, no usage.
    #[test]
    fn specialization_offers_the_definitions_kind_first() {
        let mut s = standard_library_server();
        let (shown, items) = listed(&mut s, "file:///w/a.sysml", "part def Sedan :> C|");
        assert!(shown[..3].contains(&"Car".to_string()), "{shown:?}");
        assert!(
            items
                .iter()
                .all(|i| i["label"] != "kg" && i["label"] != "mass")
        );
        let car = shown.iter().position(|l| l == "Car").unwrap();
        let color = shown.iter().position(|l| l == "Color");
        assert!(color.is_none(), "an enumeration is no supertype of a part");
        assert!(car < 3);
    }

    /// Keywords come from the document's dialect and rank where the
    /// position needs them: the body's own keywords at a statement's
    /// start, the declaring keyword after `exhibit`, `true` for a
    /// Boolean's value.
    #[test]
    fn keywords_rank_where_the_position_needs_them() {
        let mut s = standard_library_server();
        let (shown, _) = listed(&mut s, "file:///w/a.sysml", "cons|");
        assert!(
            shown.contains(&"constant".to_string()) && shown.contains(&"constraint".to_string())
        );
        assert!(
            !shown.contains(&"const".to_string()),
            "a KerML word: {shown:?}"
        );

        let (shown, _) = listed(
            &mut s,
            "file:///w/b.sysml",
            "state def S {\n            ent|\n        }",
        );
        assert_eq!(
            shown.first().map(String::as_str),
            Some("entry"),
            "{shown:?}"
        );
        assert!(!shown.contains(&"enthalpy".to_string()), "{shown:?}");

        let (shown, _) = listed(&mut s, "file:///w/c.sysml", "exhibit st|");
        assert_eq!(
            shown.first().map(String::as_str),
            Some("state"),
            "{shown:?}"
        );

        let (shown, items) = listed(
            &mut s,
            "file:///w/d.sysml",
            "action def A {\n            fo|\n        }",
        );
        assert!(
            matches!(shown.first().map(String::as_str), Some("for" | "fork")),
            "{shown:?}"
        );
        assert!(
            items.iter().all(|i| i["label"] != "foot"),
            "no names at an action's statement"
        );

        let (shown, _) = listed(&mut s, "file:///w/e.sysml", "attribute b : Boolean = t|");
        assert_eq!(shown.first().map(String::as_str), Some("true"), "{shown:?}");

        let (shown, _) = listed(&mut s, "file:///w/f.sysml", "satisfy Max|");
        assert_eq!(
            shown.first().map(String::as_str),
            Some("MaxMassReq"),
            "{shown:?}"
        );
    }

    /// Measurement units write quantities' values and other units: in
    /// an expression they rank after every other name, and first where
    /// the statement's type is a unit type.
    #[test]
    fn units_rank_by_the_declared_type() {
        let mut s = standard_library_server();
        let before = |shown: &[String], a: &str, b: &str| {
            let at = |l: &str| shown.iter().position(|x| x == l);
            at(a).zip(at(b)).is_some_and(|(a, b)| a < b)
        };
        let (shown, _) = listed(&mut s, "file:///w/a.sysml", "attribute f : ForceUnit = m|");
        assert!(before(&shown, "metre", "mass"), "units first: {shown:?}");
        // A library quantity against a unit: the workspace's `mass`
        // would outrank every library name, units or not.
        let (shown, _) = listed(&mut s, "file:///w/b.sysml", "attribute f : MassValue = m|");
        assert!(
            before(&shown, "machNumber", "metre"),
            "units last: {shown:?}"
        );
        let (shown, _) = listed(&mut s, "file:///w/c.sysml", "attribute f = me|");
        let unit = shown
            .iter()
            .position(|l| l == "metre")
            .expect("metre offered");
        assert!(
            shown[unit..].iter().all(|l| !l.starts_with("mean")),
            "every quantity ahead of the units: {shown:?}"
        );
    }

    /// An alias whose target another unit declares ranks, and shows, as
    /// what it names, which the symbol tables find through the imports
    /// of the alias's namespace — private ones included — and outward:
    /// the library's `TimeValue` (an alias of `ISQBase::DurationValue`,
    /// which `ISQSpaceTime` imports privately) as that attribute
    /// definition at a type, typed in part too, a model's own `Torque`
    /// (for `ISQ::TorqueValue`) likewise, and `vmass` (for the vehicle
    /// model's `Vehicle::mass`) as a feature at a feature and an operand.
    #[test]
    fn aliases_of_other_units_elements_rank_as_what_they_name() {
        let mut s = standard_library_server();
        let aliases = "alias Torque for ISQ::TorqueValue;\n        \
                       alias vmass for VehicleModel::Vehicle::mass;\n        ";
        let item = |items: &[serde_json::Value], label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"))
                .clone()
        };
        let group = |item: &serde_json::Value| {
            item["sortText"]
                .as_str()
                .map(|k| k[..1].to_string())
                .unwrap_or_default()
        };
        let (_, items) = listed(
            &mut s,
            "file:///w/a0.sysml",
            &format!("{aliases}attribute t : |"),
        );
        for (alias, target) in [("TimeValue", "DurationValue"), ("Torque", "TorqueValue")] {
            let (alias, target) = (item(&items, alias), item(&items, target));
            assert_eq!(alias["kind"], target["kind"], "{alias}");
            assert_eq!(group(&alias), group(&target), "{alias}");
            assert_eq!(group(&alias), "1", "{alias}");
        }
        // Typed in part, it is listed as the word is typed, ranked so.
        let (shown, items) = listed(
            &mut s,
            "file:///w/a3.sysml",
            &format!("{aliases}attribute t : TimeV|"),
        );
        assert_eq!(
            shown.first().map(String::as_str),
            Some("TimeValue"),
            "{shown:?}"
        );
        assert_eq!(group(&item(&items, "TimeValue")), "1");
        for (i, body) in ["ref r ::> |", "attribute x = |"].into_iter().enumerate() {
            let uri = format!("file:///w/a{}.sysml", i + 1);
            let (_, items) = listed(&mut s, &uri, &format!("{aliases}{body}"));
            let vmass = item(&items, "vmass");
            assert_ne!(
                vmass["kind"],
                serde_json::json!(lsp_types::CompletionItemKind::MODULE),
                "{body:?}: {vmass}"
            );
            assert_eq!(group(&vmass), "1", "{body:?}: {vmass}");
        }
    }

    /// An alias ranks, and shows, as what the one lookup behind both
    /// finds it naming: a sibling (`Rim` for `Wheel`), an element of an
    /// enclosing namespace (`Tyre`, in a package of its own, for the
    /// same `Wheel`), or an element of another unit (`Chauffeur` for the
    /// vehicle model's `Driver`) — each ranked and shown as that part
    /// definition, here inside the package holding `Tyre`.
    #[test]
    fn aliases_rank_and_show_as_what_they_name() {
        let mut s = base_library_server();
        let (_, items) = listed(
            &mut s,
            "file:///w/r.sysml",
            "part def Wheel;\n        alias Rim for Wheel;\n        \
             alias Chauffeur for VehicleModel::Driver;\n        \
             package Spares {\n            alias Tyre for Wheel;\n            \
             part p : |\n        }",
        );
        let item = |label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .unwrap_or_else(|| panic!("{label} offered"))
                .clone()
        };
        let group = |item: &serde_json::Value| {
            item["sortText"]
                .as_str()
                .map(|k| k[..2].to_string())
                .unwrap_or_default()
        };
        let wheel = item("Wheel");
        for alias in ["Rim", "Tyre", "Chauffeur"] {
            let alias = item(alias);
            assert_eq!(alias["kind"], wheel["kind"], "{alias}");
            assert_eq!(group(&alias), group(&wheel), "{alias}");
        }
    }

    /// An alias's target is looked for as the notation resolves a name:
    /// a qualified target through its qualifier, not by its last
    /// segment (`Defs::Engine` names the part definition, not the usage
    /// beside the alias that shares its name), and a one-segment target
    /// outward from the alias (`Motor` in the enclosing package, not an
    /// attribute of that name declared earlier elsewhere in the unit).
    #[test]
    fn aliases_follow_their_target_as_written() {
        let mut s = base_library_server();
        for (i, (body, alias)) in [
            (
                "package Defs { part def Engine; }\n        package Uses {\n            \
                 part Engine : Defs::Engine;\n            alias E for Defs::Engine;\n            \
                 part p : |\n        }",
                "E",
            ),
            (
                "package A { attribute Motor; }\n        package B {\n            \
                 part def Motor;\n            package C {\n                \
                 alias M for Motor;\n                part p : |\n            }\n        }",
                "M",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/t{i}.sysml");
            let (_, items) = listed(&mut s, &uri, body);
            let item = items
                .iter()
                .find(|it| it["label"] == alias)
                .unwrap_or_else(|| panic!("{alias} offered: {items:?}"));
            assert_eq!(
                item["kind"],
                serde_json::json!(lsp_types::CompletionItemKind::CLASS),
                "{item}"
            );
            assert!(
                item["sortText"]
                    .as_str()
                    .is_some_and(|k| k.starts_with('1')),
                "{item}"
            );
        }
    }

    /// A definition qualifies the features it owns (`redefines
    /// Vehicle::mass`, `= WheelAssy::wheel`): the workspace's
    /// definitions stay offered where features are named and in
    /// expressions, after every other name. The library's do not — they
    /// would double those lists.
    #[test]
    fn definitions_qualify_the_features_they_own() {
        let mut s = base_library_server();
        for (i, body) in [
            "attribute m redefines Veh|",
            "attribute :>> Veh|",
            "attribute m = Veh|",
            "attribute ok = mass == Veh|",
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/q{i}.sysml");
            let (shown, _) = listed(
                &mut s,
                &uri,
                &format!("part def Car2 :> Vehicle {{\n            {body}\n        }}"),
            );
            assert!(
                shown.contains(&"Vehicle".to_string()),
                "{body:?}: {shown:?}"
            );
        }
        let (shown, _) = listed(&mut s, "file:///w/q9.sysml", "attribute m = Rend|");
        assert!(shown.is_empty(), "no library definition: {shown:?}");
    }

    /// A payload is typed by whatever it carries: after `accept` and a
    /// flow's or a message's `of`, the statement's own kind no longer
    /// decides the typing.
    #[test]
    fn payloads_take_any_definition() {
        let mut s = base_library_server();
        for (i, (body, name)) in [
            ("action trigger accept sig : Sig|", "Signal"),
            ("message of sig : Sig|", "Signal"),
            ("flow of fuel : Fu|", "Fuel"),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/p{i}.sysml");
            let (shown, _) = listed(&mut s, &uri, body);
            assert!(shown.contains(&name.to_string()), "{body:?}: {shown:?}");
        }
    }

    /// A succession steps between occurrences of any kind — parts and
    /// messages as well as actions and states, the behaviors first —
    /// and a transition may start from the entry action a state machine
    /// starts from.
    #[test]
    fn successions_name_occurrences_of_any_kind() {
        let mut s = base_library_server();
        for (i, (body, name)) in [
            (
                "part front;\n        part rear;\n        first fr|",
                "front",
            ),
            (
                "message m1;\n        message m2;\n        first m1 then m|",
                "m2",
            ),
            (
                "state def S {\n            entry action initial;\n            \
                 state off;\n            transition init|\n        }",
                "initial",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/s{i}.sysml");
            let (shown, _) = listed(&mut s, &uri, body);
            assert!(shown.contains(&name.to_string()), "{body:?}: {shown:?}");
        }
        let (shown, _) = listed(
            &mut s,
            "file:///w/s9.sysml",
            "part zone;\n        action zap;\n        first z|",
        );
        assert_eq!(shown, ["zap", "zone"], "the behavior first");
    }

    /// An individual definition specializes the occurrence definition it
    /// is an individual of, of whatever kind (`individual def Vehicle_1
    /// :> Vehicle`), and a definition of a user-defined kind (`#Service
    /// def`) may be of any kind, so every position taking definitions
    /// takes it.
    #[test]
    fn individuals_and_user_kinds_keep_their_supertypes() {
        let mut s = base_library_server();
        let service = "metadata def Service;\n        #Service def APIService;\n        ";
        for (i, (body, name)) in [
            ("individual def Vehicle_1 :> Veh|", "Vehicle"),
            ("port def ApiPort :> APIS|", "APIService"),
            ("attribute a : APIS|", "APIService"),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/i{i}.sysml");
            let (shown, _) = listed(&mut s, &uri, &format!("{service}{body}"));
            assert!(shown.contains(&name.to_string()), "{body:?}: {shown:?}");
        }
    }

    /// A connector end's multiplicity (`bind [1] a = [1] b`) is no
    /// operand: a feature follows it. Neither is the function an arrow
    /// invokes: a function reference may follow it (`->reduce max`).
    #[test]
    fn end_multiplicities_and_function_references_take_names() {
        let mut s = base_library_server();
        for (i, (body, name)) in [
            (
                "part front;\n        part rear;\n        bind [1] front = [1] re|",
                "rear",
            ),
            (
                "attribute es : Real[*];\n        attribute e = es->reduce Kin|",
                "KineticEnergy",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/m{i}.sysml");
            let (shown, _) = listed(&mut s, &uri, body);
            assert!(shown.contains(&name.to_string()), "{body:?}: {shown:?}");
        }
    }

    /// KerML's type operators take features, which are types too — a
    /// feature's operands are features first — and a binding's `of` its
    /// first end, a feature.
    #[test]
    fn type_operators_and_binding_ends_take_features() {
        let model = "package K {\n    feature links;\n    feature objects;\n    \
                     feature left;\n    LINE\n}\n";
        for (line, name) in [
            ("feature both intersects links, obj|", "objects"),
            ("feature f unions li|", "links"),
            ("feature f differences li|", "links"),
            ("feature f disjoint from li|", "links"),
            ("binding bnd of le|", "left"),
            ("classifier C unions li|", "links"),
        ] {
            let items = complete_in("file:///w/k.kerml", &model.replace("LINE", line));
            assert!(
                items.iter().any(|i| i["label"] == name),
                "{line:?}: {:?}",
                completion_labels(&items)
            );
        }
    }

    /// Within a group, shorter names rank first: the word typed is more
    /// of a short name, which the quantity library's long names sharing
    /// its first letters would bury alphabetically (`MassValue` after
    /// `MassAttenuationCoefficientValue` and thirty others).
    #[test]
    fn shorter_names_rank_first_within_a_group() {
        let mut s = standard_library_server();
        for (i, (body, name)) in [
            ("attribute x : Mas|", "MassValue"),
            ("attribute x : Spe|", "SpeedValue"),
        ]
        .into_iter()
        .enumerate()
        {
            let uri = format!("file:///w/r{i}.sysml");
            let (shown, _) = listed(&mut s, &uri, body);
            let at = shown.iter().position(|l| l == name);
            assert!(at.is_some_and(|at| at < 3), "{body:?}: {shown:?}");
        }
    }

    /// A push server over a small library holding the base every action
    /// implicitly specializes and two renderings, with
    /// [`VEHICLE_MODEL`] open.
    fn base_library_server() -> PushServer {
        let mut s = PushServer::with_library_sources(
            vec![(
                "Bases.sysml".to_string(),
                "standard library package Actions {\n\
                 \x20   abstract action def Action {\n\
                 \x20       action start;\n\
                 \x20       action done;\n\
                 \x20       abstract action subactions[0..*];\n\
                 \x20   }\n\
                 }\n\
                 standard library package Views {\n\
                 \x20   abstract rendering def Rendering;\n\
                 \x20   rendering asTreeDiagram : Rendering;\n\
                 \x20   rendering asElementTable : Rendering;\n\
                 }\n"
                .to_string(),
            )],
            None,
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/vehicles.sysml", "languageId": "sysml",
                                 "version": 1, "text": VEHICLE_MODEL}}}),
        );
        s
    }

    /// While a quoted name is being typed at an operand, the units only
    /// a quoted name writes are offered: a derived unit's definition
    /// names them so (`Btu_IT/'°F'`, `referenceUnit = 'm⋅s⁻²'`).
    #[test]
    fn a_quoted_operand_offers_the_units_spelled_apart() {
        let mut s = standard_library_server();
        let (_, items) = listed(
            &mut s,
            "file:///w/h.sysml",
            "attribute c : ThermalResistanceUnit = s/'°|",
        );
        for spelled in ["°F", "°C"] {
            assert!(items.iter().any(|i| i["label"] == spelled), "{spelled}");
        }
    }

    /// An expression's operand outside a unit bracket offers no unit only
    /// a quoted name writes (`m/s`, `m²/(V⋅s)`): a `)` typed after an
    /// argument (`KineticEnergy(m, v)`) would match its symbol and leave
    /// it the one item Enter accepts. Units spelled as plain names stay,
    /// and a unit bracket still offers every unit.
    #[test]
    fn operands_offer_no_unit_spelled_apart() {
        let mut s = standard_library_server();
        let has = |items: &[serde_json::Value], label: &str| {
            let quoted = format!("'{label}'");
            items
                .iter()
                .any(|i| i["label"] == label || i["label"] == quoted.as_str())
        };
        let (_, items) = listed(
            &mut s,
            "file:///w/f.sysml",
            "attribute ke = KineticEnergy(1, v|",
        );
        for spelled in ["m/s", "m²/(V⋅s)", "m²"] {
            assert!(!has(&items, spelled), "{spelled}");
        }
        for plain in ["kg", "N"] {
            assert!(has(&items, plain), "{plain}");
        }
        let (_, items) = listed(&mut s, "file:///w/g.sysml", "attribute a = 9.8 [m|");
        assert!(has(&items, "m/s"));
    }

    /// A qualified name's position is read off the text ahead of it, so
    /// the namespace's members rank as that position ranks names: a
    /// typing puts definitions first (`attribute x : ISQ::` puts
    /// `MassValue` among the first, the quantity features after every
    /// definition), a specialization its kinds, an import anything alike;
    /// in a unit bracket (`[SI::`) only units, the declared quantity's
    /// first — at `[SI::k` a mass takes `kg` ahead of kelvin's `K`, which
    /// gives up its whole match.
    #[test]
    fn a_qualified_position_takes_what_the_position_does() {
        let mut s = standard_library_server();
        let (shown, items) = listed(&mut s, "file:///w/a.sysml", "attribute x : ISQ::|");
        let has =
            |items: &[serde_json::Value], label: &str| items.iter().any(|i| i["label"] == label);
        assert!(
            shown.iter().take(10).any(|l| l == "MassValue"),
            "{:?}",
            &shown[..shown.len().min(10)]
        );
        let key = |items: &[serde_json::Value], label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .and_then(|i| i["sortText"].as_str().map(str::to_string))
                .unwrap_or_else(|| panic!("{label} offered"))
        };
        assert!(key(&items, "mass") > key(&items, "AbsoluteActivityValue"));
        let (_, items) = listed(
            &mut s,
            "file:///w/b.sysml",
            "part def Car3 :> VehicleModel::|",
        );
        assert!(key(&items, "Vehicle") < key(&items, "Speed"));
        let (_, items) = listed(&mut s, "file:///w/c.sysml", "private import ISQ::Mas|");
        assert!(has(&items, "MassValue") && has(&items, "mass"));
        let (_, items) = listed(
            &mut s,
            "file:///w/d.sysml",
            "attribute m : MassValue = 5 [SI::|",
        );
        assert!(has(&items, "kg") && has(&items, "g"));
        assert!(!has(&items, "MassValue") && !has(&items, "mass"));
        let (shown, items) = listed(
            &mut s,
            "file:///w/e.sysml",
            "attribute m : MassValue = 5 [SI::k|",
        );
        assert_eq!(shown.first().map(String::as_str), Some("kg"), "{shown:?}");
        let kelvin = items.iter().find(|i| i["label"] == "K").expect("K");
        assert_eq!(kelvin["filterText"], "K_kelvin");
    }

    /// After a qualifier the namespace's members rank as names do
    /// anywhere else, shorter labels first within a group: `ISQ::Mas`
    /// puts `MassValue` ahead of the longer `Mass…` names.
    #[test]
    fn qualified_members_rank_shorter_labels_first() {
        let mut s = standard_library_server();
        let (shown, _) = listed(&mut s, "file:///w/q.sysml", "attribute x : ISQ::Mas|");
        // As an editor matches the word typed, the case of its letters too.
        let shown: Vec<&String> = shown.iter().filter(|l| l.starts_with("Mas")).collect();
        let at = shown.iter().position(|l| *l == "MassValue");
        assert!(
            at.is_some_and(|i| i < 2),
            "{:?}",
            &shown[..shown.len().min(6)]
        );
    }

    /// Below the best group only a label of one or two characters, which
    /// a letter or two typed matches whole by chance, gives up that
    /// match: a longer name typed whole still comes first, ahead of the
    /// members it begins (`mass` at `attribute m :> mass`).
    #[test]
    fn a_longer_name_typed_whole_keeps_its_match() {
        let mut s = standard_library_server();
        let (_, items) = listed(
            &mut s,
            "file:///w/e.sysml",
            "part def Engine {\n            attribute m :> mas|\n        }",
        );
        let mass = items.iter().find(|i| i["label"] == "mass").expect("mass");
        assert!(mass["filterText"].is_null(), "{mass}");
    }

    /// An editor ranks a label the typed word matches whole ahead of
    /// every other, whatever the server's order: for a label of one or
    /// two characters only the best group a list holds keeps that. At a
    /// member position a name that is no member is filtered by its label
    /// and more (`m` by `m_m`), and in a quantity's unit bracket a unit of
    /// another quantity by its symbol and name (`K` by `K_kelvin` for a
    /// mass): `m` ranks `mass` first, `k` `kg`. Where no group comes
    /// first, nothing is held back.
    #[test]
    fn only_the_best_group_keeps_the_whole_match() {
        let mut s = standard_library_server();
        let filter = |items: &[serde_json::Value], label: &str| {
            items
                .iter()
                .find(|i| i["label"] == label)
                .map(|i| i["filterText"].clone())
        };
        let (_, items) = listed(
            &mut s,
            "file:///w/a.sysml",
            "part def Car2 :> Vehicle {\n            attribute :>> m|\n        }",
        );
        // The library's unit `m`, a name no member of `Car2` has.
        assert_eq!(filter(&items, "m"), Some(serde_json::json!("m_metre")));
        assert_eq!(filter(&items, "mass"), Some(serde_json::Value::Null));
        let (_, items) = listed(
            &mut s,
            "file:///w/b.sysml",
            "attribute m : MassValue = 5 [k|",
        );
        assert_eq!(filter(&items, "K"), Some(serde_json::json!("K_kelvin")));
        assert_eq!(filter(&items, "kg"), Some(serde_json::Value::Null));
        for (uri, body) in [
            ("file:///w/c.sysml", "attribute x = m|"),
            ("file:///w/d.sysml", "attribute y = 5 [K|"),
        ] {
            let (_, items) = listed(&mut s, uri, body);
            for label in ["m", "K"] {
                if let Some(f) = filter(&items, label) {
                    assert_eq!(f, serde_json::Value::Null, "{body}: {label}");
                }
            }
        }
    }

    /// A redefinition names the features the enclosing element
    /// inherits, and a succession the features in scope there — those
    /// the library base of its kind contributes too (`start` and `done`
    /// of every action) — ahead of every other name.
    #[test]
    fn inherited_features_come_first() {
        let mut s = base_library_server();
        // A workspace attribute that sorts ahead but is not inherited.
        let garage = "part def Garage { attribute maintenanceCost; }\n        ";
        let (shown, _) = listed(
            &mut s,
            "file:///w/a.sysml",
            &format!(
                "{garage}part def Car2 :> Vehicle {{\n            attribute :>> m|\n        }}"
            ),
        );
        assert_eq!(shown.first().map(String::as_str), Some("mass"), "{shown:?}");
        let (shown, _) = listed(
            &mut s,
            "file:///w/b.sysml",
            "part def Car2 :> Vehicle {\n            port :>> |\n        }",
        );
        assert_eq!(
            shown.first().map(String::as_str),
            Some("fuelIn"),
            "{shown:?}"
        );
        // Through a typing as well as a specialization.
        let (shown, _) = listed(
            &mut s,
            "file:///w/c.sysml",
            &format!(
                "{garage}part v2 : Vehicle {{\n            attribute redefines m|\n        }}"
            ),
        );
        assert_eq!(shown.first().map(String::as_str), Some("mass"), "{shown:?}");

        let (shown, _) = listed(
            &mut s,
            "file:///w/d.sysml",
            "action def A {\n            action a1 : Drive;\n            first st|\n        }",
        );
        assert_eq!(
            shown.first().map(String::as_str),
            Some("start"),
            "{shown:?}"
        );
        // The action's own succession targets first, then the ones it
        // inherits, then everything else.
        let (shown, items) = listed(
            &mut s,
            "file:///w/e.sysml",
            "action def A {\n            action a1 : Drive;\n            then |\n        }",
        );
        let names: Vec<&str> = shown.iter().map(String::as_str).take(4).collect();
        assert_eq!(names, ["a1", "done", "start", "subactions"], "{shown:?}");
        let start = items.iter().find(|i| i["label"] == "start").expect("start");
        assert!(
            start.get("additionalTextEdits").is_none(),
            "a name in scope needs no import: {start}"
        );
    }

    /// A syntax error in another document leaves the inherited members
    /// on: the completion session salvages around it.
    #[test]
    fn inherited_features_survive_a_syntax_error_elsewhere() {
        let mut s = base_library_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/broken.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package B {\n    part def Broken {\n        attribute x = ;\n"}}}),
        );
        let (shown, _) = listed(
            &mut s,
            "file:///w/a.sysml",
            "part def Car2 :> Vehicle {\n            attribute :>> m|\n        }",
        );
        assert_eq!(shown.first().map(String::as_str), Some("mass"), "{shown:?}");
    }

    /// An unreadable member elsewhere in the same document — a value
    /// left out before its `;`, a group left open at the end of a line —
    /// leaves the inherited members on too: salvage blanks that member
    /// alone, and the document stays in the model.
    #[test]
    fn inherited_features_survive_an_unreadable_member_in_the_document() {
        let mut s = base_library_server();
        for (i, broken) in ["part z { attribute = ; }", "attribute q = (1 + ;"]
            .into_iter()
            .enumerate()
        {
            for (j, (above, below)) in [(broken, ""), ("", broken)].into_iter().enumerate() {
                let (shown, _) = listed(
                    &mut s,
                    &format!("file:///w/r{i}{j}.sysml"),
                    &format!(
                        "{above}\n        part def Car2 :> Vehicle {{\n            \
                         attribute :>> m|\n        }}\n        {below}"
                    ),
                );
                assert_eq!(shown.first().map(String::as_str), Some("mass"), "{broken}");
                let (shown, _) = listed(
                    &mut s,
                    &format!("file:///w/s{i}{j}.sysml"),
                    &format!(
                        "{above}\n        action def A {{\n            action a1 : Drive;\n            \
                         first st|\n        }}\n        {below}"
                    ),
                );
                assert_eq!(shown.first().map(String::as_str), Some("start"), "{broken}");
            }
        }
    }

    /// Moving on to the next statement of the same body builds no
    /// session: what the enclosing element inherits was named for the
    /// last one, and the text outside its body has not changed. A
    /// statement in the body of an element new around it — an anonymous
    /// metadata usage, whose members are its metadata definition's —
    /// builds once, and the next statement there builds none.
    #[test]
    fn the_next_statement_builds_no_session() {
        let mut s = base_library_server();
        let uri = "file:///w/n.sysml";
        let text = |body: &str| {
            format!(
                "package N {{\n    private import VehicleModel::*;\n    \
                 metadata def Rating {{ attribute critical; attribute level; }}\n    \
                 part def Car2 :> Vehicle {{\n        {body}\n    }}\n}}\n"
            )
        };
        let builds = || crate::nav::SESSION_BUILDS.with(std::cell::Cell::get);
        put(&mut s, uri, 1, &text("attribute :>> m"));
        assert!(is_member(&mut s, uri, 4, 23, "mass"));
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        for (version, body, line, character, label, built) in [
            (
                2,
                "attribute :>> mass;\n        port :>> ",
                5,
                17,
                "fuelIn",
                0,
            ),
            (
                3,
                "attribute :>> mass;\n        @Rating { crit }",
                5,
                22,
                "critical",
                1,
            ),
            (
                4,
                "attribute :>> mass;\n        @Rating { critical; lev }",
                5,
                31,
                "level",
                1,
            ),
        ] {
            put(&mut s, uri, version, &text(body));
            assert!(is_member(&mut s, uri, line, character, label), "{body:?}");
            assert_eq!(builds(), built, "{body:?}");
        }
    }

    /// A metadata usage's body names the features of its metadata
    /// definition, ahead of every other name: the usage inherits none of
    /// its own.
    #[test]
    fn metadata_bodies_name_their_definitions_features() {
        for (i, statement) in ["@Rating { crit| }", "metadata Rating { ref crit| }"]
            .into_iter()
            .enumerate()
        {
            let mut s = base_library_server();
            let (_, items) = listed(
                &mut s,
                &format!("file:///w/m{i}.sysml"),
                &format!(
                    "metadata def Rating {{ attribute critical; attribute level; }}\n        \
                     part x {{\n            {statement}\n        }}"
                ),
            );
            let critical = items
                .iter()
                .find(|i| i["label"] == "critical")
                .unwrap_or_else(|| panic!("critical offered: {statement}"));
            assert!(
                critical["sortText"]
                    .as_str()
                    .is_some_and(|k| k.starts_with("00")),
                "{statement}: {critical}"
            );
        }
    }

    /// In a KerML behavior a succession names its steps — its own and
    /// those it inherits — ahead of every other name.
    #[test]
    fn kerml_successions_name_the_behaviors_steps() {
        for (marked, steps) in [
            (
                "package K {\n    behavior B {\n        step s1;\n        step s2;\n        \
                 succession first s|\n    }\n}\n",
                &["s1", "s2"][..],
            ),
            (
                "package K {\n    behavior A {\n        step a1;\n    }\n    \
                 behavior B specializes A {\n        succession first a|\n    }\n}\n",
                &["a1"],
            ),
        ] {
            let items = complete_in("file:///w/k.kerml", marked);
            for step in steps {
                let item = items
                    .iter()
                    .find(|i| i["label"] == *step)
                    .unwrap_or_else(|| panic!("{step} offered: {items:?}"));
                assert!(
                    item["sortText"]
                        .as_str()
                        .is_some_and(|k| k.starts_with("00")),
                    "{step}: {item}"
                );
            }
        }
    }

    /// A completion session that fails to build is not built again for
    /// the same sources: the next keystroke in the statement tries none.
    #[test]
    fn a_failed_completion_session_is_not_rebuilt() {
        // A library that cannot be read fails every build.
        let mut s = PushServer::new_with(Some(sysmlv2_transform::Library::dir(
            "/nonexistent/sysml.library",
        )));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
        );
        let uri = "file:///w/f.sysml";
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "sysml", "version": 1,
                                 "text": "package F {\n    part def V { attribute m; }\n    \
                                          part def W :> V {\n        attribute :>> \n    }\n}\n"}}}),
        );
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        for _ in 0..2 {
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": 3, "character": 22}}}),
            );
        }
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 1);
    }

    /// A member the symbol tables hold too carries their documentation
    /// and their kind, as the same name offered from them would: an
    /// attribute shows as the tables' property, not as the field its
    /// metaclass would make it.
    #[test]
    fn members_carry_their_documentation() {
        let mut s = base_library_server();
        let (_, items) = listed(
            &mut s,
            "file:///w/d.sysml",
            "part def Base {\n            attribute weight { doc /* How heavy it is. */ }\n        }\n        \
             part def Car3 :> Base {\n            attribute :>> w|\n        }",
        );
        let weight = items
            .iter()
            .find(|i| i["label"] == "weight")
            .expect("weight offered");
        assert!(
            weight["sortText"]
                .as_str()
                .is_some_and(|k| k.starts_with("00")),
            "{weight}"
        );
        assert!(
            weight["documentation"]["value"]
                .as_str()
                .is_some_and(|d| d.contains("How heavy it is.")),
            "{weight}"
        );
        assert_eq!(
            weight["kind"],
            serde_json::json!(lsp_types::CompletionItemKind::PROPERTY),
            "{weight}"
        );
    }

    /// Open or change `uri` to `text` on `s` at `version`.
    fn put(s: &mut PushServer, uri: &str, version: i32, text: &str) {
        let msg = if version == 1 {
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "sysml", "version": 1, "text": text}}})
        } else {
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri, "version": version},
                "contentChanges": [{"text": text}]}})
        };
        responses(s, &msg);
    }

    /// The sort text of the item labeled `label` a completion at
    /// `line`/`character` of `uri` offers, if any.
    fn sort_key(
        s: &mut PushServer,
        uri: &str,
        line: u32,
        character: u32,
        label: &str,
    ) -> Option<String> {
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": line, "character": character}}}),
        );
        out[0]["result"]
            .as_array()
            .expect("items")
            .iter()
            .find(|i| i["label"] == label)
            .and_then(|i| i["sortText"].as_str())
            .map(str::to_string)
    }

    /// Statements inside a redefinition without a name of its own
    /// (`part :>> engine { … }`) find it in the session built for the
    /// first of them by the name of the feature it redefines, as the
    /// model names it: the next builds none, and names the same members.
    #[test]
    fn unnamed_redefinitions_are_found_by_what_they_redefine() {
        let mut s = base_library_server();
        let uri = "file:///w/e.sysml";
        let text = |body: &str| {
            format!(
                "package E {{\n    part def Engine {{ attribute power; attribute displacement; }}\n    \
                 part def Car {{ part engine : Engine; }}\n    part def Car4 :> Car {{\n        \
                 part :>> engine {{\n            {body}\n        }}\n    }}\n}}\n"
            )
        };
        put(&mut s, uri, 1, &text("attribute :>> p"));
        let power = sort_key(&mut s, uri, 5, 27, "power");
        assert!(
            power.as_deref().is_some_and(|k| k.starts_with("00")),
            "{power:?}"
        );
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        put(
            &mut s,
            uri,
            2,
            &text("attribute :>> power;\n            attribute :>> d"),
        );
        let displacement = sort_key(&mut s, uri, 6, 27, "displacement");
        assert!(
            displacement.as_deref().is_some_and(|k| k.starts_with("00")),
            "{displacement:?}"
        );
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
    }

    /// A feature inherited through a redefinition without a name of its
    /// own (`attribute :>> mass = 1500;`) is named as the model names it,
    /// after the feature it redefines: still an inherited member.
    #[test]
    fn members_redefined_without_a_name_stay_members() {
        let mut s = base_library_server();
        for (i, body) in [
            "part def Car3 :> Heavy {\n            attribute :>> m|\n        }",
            "part c : Heavy {\n            attribute :>> m|\n        }",
        ]
        .into_iter()
        .enumerate()
        {
            let (_, items) = listed(
                &mut s,
                &format!("file:///w/h{i}.sysml"),
                &format!(
                    "part def Heavy :> Vehicle {{ attribute :>> mass = 1500; }}\n        {body}"
                ),
            );
            let mass = items
                .iter()
                .find(|i| i["label"] == "mass")
                .unwrap_or_else(|| panic!("mass offered: {body}"));
            assert!(
                mass["sortText"]
                    .as_str()
                    .is_some_and(|k| k.starts_with("00")),
                "{body}: {mass}"
            );
        }
    }

    /// A statement no type encloses — at a unit's top level — has no
    /// enclosing element's members to name: no session is built for it.
    #[test]
    fn top_level_statements_build_no_session() {
        let mut s = base_library_server();
        let uri = "file:///w/t.sysml";
        put(
            &mut s,
            uri,
            1,
            "part def V { attribute m; }\nattribute :>> ",
        );
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        sort_key(&mut s, uri, 1, 14, "m");
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
    }

    /// Is `label` offered at `line`/`character` of `uri` as an enclosing
    /// element's member, ahead of every other name?
    fn is_member(s: &mut PushServer, uri: &str, line: u32, character: u32, label: &str) -> bool {
        sort_key(s, uri, line, character, label).is_some_and(|k| k.starts_with("00"))
    }

    /// The members named for an enclosing element are what the text
    /// outside its body makes of it: a change there — a supertype
    /// gaining a feature in another document, the element's own
    /// specialization — names the new ones. Its body is read as the text
    /// has it: a feature an earlier statement redefines is no longer a
    /// member, and one declared since is.
    #[test]
    fn members_follow_the_text_around_the_body() {
        let mut s = base_library_server();
        let (a, b, c) = (
            "file:///w/a.sysml",
            "file:///w/b.sysml",
            "file:///w/c.sysml",
        );
        let bases = |extra: &str| {
            format!(
                "package A {{\n    part def Base {{ attribute a1; {extra}}}\n    \
                 part def Base2 {{ attribute b1; }}\n}}\n"
            )
        };
        let d = |header: &str, body: &str| {
            format!(
                "package B {{\n    private import A::*;\n    part def D :> {header} {{\n        \
                 {body}\n    }}\n}}\n"
            )
        };
        put(&mut s, a, 1, &bases(""));
        put(&mut s, b, 1, &d("Base", "attribute :>> "));
        assert!(is_member(&mut s, b, 3, 22, "a1"));
        // Another document: the supertype gains a feature.
        put(&mut s, a, 2, &bases("attribute a2; "));
        assert!(is_member(&mut s, b, 3, 22, "a2"));
        // The element's own specialization.
        put(&mut s, b, 2, &d("Base2", "attribute :>> "));
        assert!(is_member(&mut s, b, 3, 22, "b1"));
        assert!(!is_member(&mut s, b, 3, 22, "a1"));
        // Its body: a feature redefined in an earlier statement.
        put(
            &mut s,
            b,
            3,
            &d("Base2", "attribute :>> b1;\n        attribute :>> "),
        );
        assert!(!is_member(&mut s, b, 4, 22, "b1"));

        // A feature declared since, where a succession names its own.
        let act = |body: &str| {
            format!(
                "package C {{\n    action def Act {{\n        action a1;\n        {body}\n    }}\n}}\n"
            )
        };
        put(&mut s, c, 1, &act("then "));
        assert!(is_member(&mut s, c, 3, 13, "a1"));
        put(&mut s, c, 2, &act("action a3;\n        then "));
        assert!(is_member(&mut s, c, 4, 13, "a3"));
        assert!(is_member(&mut s, c, 4, 13, "a1"));
    }

    /// A feature the body redefined — explicitly, or by declaring its name
    /// — when the members were first read is a member again once no
    /// statement redefines it: what the element inherits is kept apart
    /// from its body.
    #[test]
    fn members_come_back_when_their_redefinition_goes() {
        let mut s = base_library_server();
        let uri = "file:///w/r.sysml";
        let d = |body: &str| {
            format!(
                "package R {{\n    part def Base {{ attribute a1; attribute a2; }}\n    \
                 part def D :> Base {{\n        {body}\n    }}\n}}\n"
            )
        };
        put(
            &mut s,
            uri,
            1,
            &d("attribute :>> a1 = 5;\n        attribute :>> "),
        );
        assert!(!is_member(&mut s, uri, 4, 22, "a1"));
        assert!(is_member(&mut s, uri, 4, 22, "a2"));
        put(&mut s, uri, 2, &d("attribute :>> "));
        assert!(is_member(&mut s, uri, 3, 22, "a1"));
        put(&mut s, uri, 3, &d("attribute a1;\n        attribute :>> "));
        assert!(!is_member(&mut s, uri, 4, 22, "a1"));
        put(&mut s, uri, 4, &d("attribute :>> "));
        assert!(is_member(&mut s, uri, 3, 22, "a1"));
    }

    /// A parameter a body redefines by name stays a member when the
    /// statement redefining it is the one typed, whichever of the body's
    /// statements was completed first: cutting that statement out moves
    /// the parameters after it, which then redefine the one before by
    /// position.
    #[test]
    fn a_parameter_stays_a_member_in_either_order() {
        let power = "package A {\n    action def ProvidePower { in item pwrCmd; out torque; }\n    \
                     action providePower : ProvidePower {\n        \
                     in item fuelCmd redefines pwrCmd;\n        \
                     out wheelTorque redefines torque;\n    }\n}\n";
        let mut answers = Vec::new();
        for torque_first in [false, true] {
            let mut s = base_library_server();
            let uri = "file:///w/a.sysml";
            put(&mut s, uri, 1, power);
            if torque_first {
                // Inside `torque`, after `redefines t`.
                let _ = sort_key(&mut s, uri, 4, 35, "torque");
            }
            // Inside `pwrCmd`, after `redefines p`.
            answers.push(is_member(&mut s, uri, 3, 35, "pwrCmd"));
        }
        assert_eq!(answers, [true, true], "pwrCmd first, torque first");
    }

    /// A `subject` redefines the library's `subj` every case and
    /// requirement has, and a `return` parameter the `result` every
    /// calculation has: once the body declares one, neither is a member,
    /// whichever of its statements was completed first.
    #[test]
    fn what_a_subject_or_return_redefines_is_no_member() {
        let rate = "package K {\n    calc def Rate {\n        in d :> ISQ::length;\n        \
                    return v :> ISQ::speed;\n    }\n}\n";
        let mut answers = Vec::new();
        for return_first in [false, true] {
            let mut s = standard_library_server();
            let uri = "file:///w/k.sysml";
            put(&mut s, uri, 1, rate);
            if return_first {
                // After `return v :> I`.
                let _ = sort_key(&mut s, uri, 3, 21, "ISQ");
            }
            // After `in d :> I`: the library's `result`.
            let key = sort_key(&mut s, uri, 2, 17, "result");
            answers.push(key.is_some_and(|k| k.starts_with('0')));
        }
        assert_eq!(answers, [false, false], "in first, return first");
        let checked = "package Q {\n    requirement def R {\n        subject v;\n        \
                       :>> s;\n    }\n}\n";
        let mut s = standard_library_server();
        let uri = "file:///w/q.sysml";
        put(&mut s, uri, 1, checked);
        // After `:>> s`: the library's `subj`.
        let key = sort_key(&mut s, uri, 3, 13, "subj");
        assert!(
            !key.as_deref().is_some_and(|k| k.starts_with('0')),
            "{key:?}"
        );
    }

    /// What comes back of what a body redefines is only what the
    /// heritage leaves: not a feature private to the definition, nor one
    /// the library redefines — an occurrence's `startShot`, which a part
    /// of no written type reaches through the library bases it
    /// specializes implicitly, and which none of them has.
    #[test]
    fn members_are_only_what_the_heritage_leaves() {
        let car = "package G {\n    part def V { private attribute secret; attribute mass; }\n    \
                   part def Car :> V {\n        attribute :>> mass = 1;\n        :>> s;\n    }\n    \
                   part def Bare {\n        attribute a = 1;\n        :>> s;\n    }\n}\n";
        let mut s = standard_library_server();
        let uri = "file:///w/g.sysml";
        put(&mut s, uri, 1, car);
        // After `:>> s`, in `Car` and in `Bare`.
        for (line, name) in [(4, "secret"), (8, "startShot")] {
            let key = sort_key(&mut s, uri, line, 13, name);
            assert!(
                !key.as_deref().is_some_and(|k| k.starts_with('0')),
                "{name}: {key:?}"
            );
            let key = sort_key(&mut s, uri, line, 13, "self");
            assert!(
                key.as_deref().is_some_and(|k| k.starts_with('0')),
                "self: {key:?}"
            );
        }
    }

    /// The members named in the body of an unnamed redefinition typed by
    /// a library type (`attribute :>> transformation :
    /// TranslationRotationSequence { … }`) do not depend on which of its
    /// statements was completed first: its second statement is offered
    /// the `elements` it inherits either way.
    #[test]
    fn members_of_an_unnamed_redefinition_do_not_depend_on_order() {
        let unnamed = "package G {\n    private import MeasurementReferences::*;\n    \
                       attribute cf : CoordinateFrame {\n        \
                       attribute :>> transformation : TranslationRotationSequence {\n            \
                       attribute :>> source = x;\n            attribute :>> elements = y;\n        \
                       }\n    }\n}\n";
        for source_first in [false, true] {
            let mut s = standard_library_server();
            let uri = "file:///w/g.sysml";
            put(&mut s, uri, 1, unnamed);
            if source_first {
                // Inside `source`, after `attribute :>> so`.
                let _ = sort_key(&mut s, uri, 4, 28, "source");
            }
            // Inside `elements`, after `attribute :>> el`.
            // A member the library declares: group 0, from the library.
            let key = sort_key(&mut s, uri, 5, 28, "elements");
            assert!(
                key.as_deref().is_some_and(|k| k.starts_with('0')),
                "source first: {source_first}: {key:?}"
            );
        }
    }

    /// A feature a body redefines without inheriting it (`part :>>
    /// part2;` in an untyped part) is no member of that body, whichever
    /// of its statements was completed first.
    #[test]
    fn redefined_but_not_inherited_is_no_member_in_either_order() {
        let variant = "package V {\n    part part2;\n    part part3;\n    part s2 {\n        \
                       part :>> part2;\n        part :>> part3;\n    }\n}\n";
        let mut answers = Vec::new();
        for part3_first in [false, true] {
            let mut s = base_library_server();
            let uri = "file:///w/v.sysml";
            put(&mut s, uri, 1, variant);
            if part3_first {
                // Inside `part3`, after `part :>> p`.
                let _ = sort_key(&mut s, uri, 5, 18, "part3");
            }
            // Inside `part2`, after `part :>> p`.
            answers.push(is_member(&mut s, uri, 4, 18, "part2"));
        }
        assert_eq!(answers, [false, false], "part2 first, part3 first");
    }

    /// A `ref` names no kind: redefining in an action's body, it is
    /// offered the members of every kind, whichever of the body's
    /// statements was completed first (`ref :>> st` takes the `start`
    /// action every action has).
    #[test]
    fn a_ref_redefines_members_of_any_kind() {
        let go = "package R {\n    action def Go {\n        ref :>> st;\n        \
                  ref :>> do;\n    }\n}\n";
        for done_first in [false, true] {
            let mut s = base_library_server();
            let uri = "file:///w/r.sysml";
            put(&mut s, uri, 1, go);
            if done_first {
                // Inside `done`, after `ref :>> do`.
                let _ = sort_key(&mut s, uri, 3, 18, "done");
            }
            // Inside `start`, after `ref :>> st`. A member the library
            // declares: group 0, from the library.
            let key = sort_key(&mut s, uri, 2, 18, "start");
            assert!(
                key.as_deref().is_some_and(|k| k.starts_with('0')),
                "done first: {done_first}: {key:?}"
            );
        }
    }

    /// A kind keyword names the members of its own kind and of every
    /// kind specializing it: a part usage is an item usage, so an
    /// individual item redefining in an individual definition is offered
    /// the part its definition inherits, after the item — and no
    /// attribute, which is no item.
    #[test]
    fn a_redefinition_names_members_of_the_kinds_under_its_own() {
        let text = "package N {\n    item def I {\n        part i : I;\n        \
                    item j;\n        attribute a;\n    }\n    \
                    individual item def II2 :> I {\n        individual item :>> ;\n    \
                    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/n.sysml";
        put(&mut s, uri, 1, text);
        // After `individual item :>> `: both members, the item first.
        let i = sort_key(&mut s, uri, 7, 28, "i").expect("i");
        let j = sort_key(&mut s, uri, 7, 28, "j").expect("j");
        assert!(
            j.starts_with("00") && i.starts_with('0') && j < i,
            "{j} {i}"
        );
        assert!(!is_member(&mut s, uri, 7, 28, "a"));
    }

    /// At a feature position the kind the statement declares comes
    /// first and the kinds specializing it after, among the enclosing
    /// element's members and among every other name alike — an item
    /// subsetting names the items in scope before the parts, then the
    /// workspace's other items before its other parts — and every
    /// occurrence alike after an individual, a snapshot or a time slice
    /// naming no kind of its own.
    #[test]
    fn a_feature_position_names_its_own_kind_first() {
        let text = "package T {\n    part hub;\n    item cap;\n    item def Box {\n        \
                    part rim;\n        item lid;\n        occurrence tic;\n    }\n    \
                    item def Crate :> Box {\n        item :> ;\n        snapshot s :> ;\n    \
                    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/t.sysml";
        put(&mut s, uri, 1, text);
        // After `item :> `.
        let keys: Vec<String> = ["lid", "rim", "cap", "hub"]
            .iter()
            .map(|label| sort_key(&mut s, uri, 9, 16, label).expect(label))
            .collect();
        assert!(keys.windows(2).all(|w| w[0] < w[1]), "{keys:?}");
        // After `snapshot s :> `.
        let tic = sort_key(&mut s, uri, 10, 22, "tic");
        let rim = sort_key(&mut s, uri, 10, 22, "rim");
        assert!(tic.is_some() && tic == rim, "{tic:?} {rim:?}");
    }

    /// A compound keyword declares the more specific kind it spells: a
    /// `perform action` redefining names the actions performed ahead of
    /// the plain ones, which it may still redefine.
    #[test]
    fn a_performed_action_redefines_the_performed_ones_first() {
        let text = "package F {\n    part def Base {\n        action pick;\n        \
                    perform action push;\n    }\n    part def Kid :> Base {\n        \
                    perform action :>> ;\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/f.sysml";
        put(&mut s, uri, 1, text);
        // After `perform action :>> `: both members, the performed first.
        let push = sort_key(&mut s, uri, 6, 27, "push").expect("push");
        let pick = sort_key(&mut s, uri, 6, 27, "pick").expect("pick");
        assert!(
            push.starts_with('0') && pick.starts_with('0') && push < pick,
            "{push} {pick}"
        );
    }

    /// A subsetting ranks its kind word's own kind first, more general
    /// than a compound keyword declares: an included use case subsets a
    /// plain one ahead of the included ones, which it redefines first.
    #[test]
    fn an_included_use_case_subsets_the_plain_ones_first() {
        let text = "package U {\n    use case def Ride {\n        use case board;\n        \
                    include use case alight_a;\n        include use case board_a :> ;\n        \
                    include use case :>> ;\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/u.sysml";
        put(&mut s, uri, 1, text);
        // After `include use case board_a :> `.
        let board = sort_key(&mut s, uri, 4, 36, "board").expect("board");
        let alight = sort_key(&mut s, uri, 4, 36, "alight_a").expect("alight_a");
        assert!(board < alight, "{board} {alight}");
        // After `include use case :>> `.
        let board = sort_key(&mut s, uri, 5, 29, "board").expect("board");
        let alight = sort_key(&mut s, uri, 5, 29, "alight_a").expect("alight_a");
        assert!(alight < board, "{alight} {board}");
    }

    /// A declaration inside an expression's body (`forAll { … attribute t
    /// : T { … } … }` in a constraint) encloses its own statements: they
    /// are offered its members, not those of the element holding the
    /// expression.
    #[test]
    fn a_declaration_in_an_expression_body_names_its_members() {
        let text = "package G {\n    part def T { attribute src; attribute dst; }\n    \
                    part def W {\n        attribute n = 2;\n        assert constraint {\n            \
                    (1..n)->forAll {\n                in i;\n                attribute t : T {\n                    \
                    :>> src = 1;\n                    :>> d;\n                }\n                \
                    true\n            }\n        }\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/g.sysml";
        put(&mut s, uri, 1, text);
        // After `:>> d`: `dst`, which `t` inherits from `T`.
        assert!(is_member(&mut s, uri, 9, 25, "dst"));
    }

    /// An element with no name of its own inherits through all it is
    /// declared with — the feature it subsets as well as the type it is
    /// typed by: `part :> slot : Q { … }` offers `slot`'s `p1` with `Q`'s
    /// `q1`.
    #[test]
    fn an_anonymous_element_inherits_through_its_subsetting_too() {
        let text = "package A {\n    part def P { attribute p1; }\n    part def Q { attribute q1; }\n    \
                    part def H { part slot : P; }\n    part h : H {\n        \
                    part :> slot : Q {\n            attribute :>> q1 = 1;\n            \
                    attribute :>> p;\n        }\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/a.sysml";
        put(&mut s, uri, 1, text);
        // After `attribute :>> p`.
        assert!(is_member(&mut s, uri, 7, 27, "p1"));
    }

    /// A transition's target after the `}` of its `do` action names the
    /// state's members first, though the statement its tokens end there
    /// leaves the transition short of one when cut out alone.
    #[test]
    fn a_transition_target_after_its_effect_names_the_members() {
        let text = "package T {\n    item def Sig;\n    state def SD { action go; }\n    \
                    state s : SD {\n        state idle;\n        accept Sig\n            \
                    do action { }\n            then idle;\n    }\n}\n";
        let mut s = base_library_server();
        let uri = "file:///w/t.sysml";
        put(&mut s, uri, 1, text);
        // Inside `idle`, after `then i`: `go`, which `s` inherits.
        assert!(is_member(&mut s, uri, 7, 18, "go"));
    }

    /// The members kept for an element are its own, whichever position
    /// read them first: a statement in an expression's body inside the
    /// element's value (`?{in p :> m; …}`) sits in the element as the
    /// live text reads it, so reading members there first must not keep
    /// those of the redefinition holding that expression for the
    /// element's other statements.
    #[test]
    fn members_read_inside_an_expression_body_are_the_elements() {
        let text = "package M {\n    attribute def Q { attribute num; attribute unit; }\n    \
                    part def T { attribute weight : Q; attribute total : Q; }\n    \
                    part f : T {\n        attribute cap :> weight;\n        \
                    attribute redefines total = total.?{in p :> weight; p};\n    }\n}\n";
        let mut answers = Vec::new();
        for select_first in [false, true] {
            let mut s = base_library_server();
            let uri = "file:///w/m.sysml";
            put(&mut s, uri, 1, text);
            if select_first {
                // Inside `weight`, after `in p :> w`.
                let _ = sort_key(&mut s, uri, 5, 53, "weight");
            }
            // Inside `weight`, after `attribute cap :> w`.
            answers.push((
                is_member(&mut s, uri, 4, 26, "weight"),
                is_member(&mut s, uri, 4, 26, "num"),
            ));
        }
        assert_eq!(
            answers,
            [(true, false), (true, false)],
            "(weight, num) as members: the select first or not"
        );
    }

    /// While the document stays out of the model either way — a
    /// transition's target after the `}` of its effect, a member
    /// elsewhere that does not parse — the sessions built for the
    /// statement are built once: the next keystrokes there build none.
    #[test]
    fn a_statement_left_out_of_the_model_builds_once() {
        let text = |target: &str| {
            format!(
                "package T {{\n    item def Sig;\n    part z {{ attribute = ; }}\n    \
                 state def SD {{ action go; }}\n    state s : SD {{\n        state idle;\n        \
                 accept Sig\n            do action {{ }}\n            then {target};\n    }}\n}}\n"
            )
        };
        let mut s = base_library_server();
        let uri = "file:///w/t.sysml";
        put(&mut s, uri, 1, &text("i"));
        // After `then i`.
        let _ = sort_key(&mut s, uri, 8, 18, "idle");
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        for (version, target) in [(2, "id"), (3, "idl")] {
            put(&mut s, uri, version, &text(target));
            let after = 17 + u32::try_from(target.len()).expect("short");
            let _ = sort_key(&mut s, uri, 8, after, "idle");
        }
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
    }

    /// Which statement of a body was completed first does not change
    /// the members named for it: a calculation usage whose body redefines
    /// its definition's `x` and `result` offers `result` in the return's
    /// redefinition whether `in :>> x` was completed before or not — the
    /// body the model was built from, which redefines `result` too, does
    /// not hide what the live body still offers.
    #[test]
    fn members_do_not_depend_on_the_statement_completed_first() {
        let text = "package Q {\n    calc def C { in x; return result; }\n    calc c : C {\n        \
                    in :>> x = 1;\n        return :>> result = 2;\n    }\n}\n";
        for x_first in [false, true] {
            let mut s = base_library_server();
            let uri = "file:///w/q.sysml";
            put(&mut s, uri, 1, text);
            if x_first {
                // Right after `in :>> x`.
                assert!(is_member(&mut s, uri, 3, 16, "x"));
            }
            // Inside `result`, after `return :>> res`.
            assert!(
                is_member(&mut s, uri, 4, 22, "result"),
                "x first: {x_first}"
            );
        }
    }

    /// A redefinition without a name of its own is one of the body's own
    /// features, under the name of the feature it redefines and ranked
    /// as that one: after `ref :>> start { … }` an action's succession
    /// still names `start` first.
    #[test]
    fn unnamed_redefinitions_are_own_features() {
        let mut s = base_library_server();
        let (_, items) = listed(
            &mut s,
            "file:///w/u.sysml",
            "action def Go {\n            ref :>> start { }\n            first st|\n        }",
        );
        let start = items
            .iter()
            .find(|i| i["label"] == "start")
            .expect("start offered");
        assert!(
            start["sortText"]
                .as_str()
                .is_some_and(|k| k.starts_with("00")),
            "{start}"
        );
    }

    /// After `all`, `new`, and `as` a type is named more often than a
    /// feature, but a feature stands there too (`all engineChoice`, `new
    /// testVehicle(…)`, `vehicles as vehicle`): usages stay offered, after
    /// the definitions.
    #[test]
    fn usages_follow_all_new_and_as() {
        let mut s = base_library_server();
        for (i, statement) in [
            "attribute a = all fu|",
            "attribute b = new fu|",
            "attribute c = (x as fu|",
        ]
        .into_iter()
        .enumerate()
        {
            let (shown, _) = listed(
                &mut s,
                &format!("file:///w/o{i}.sysml"),
                &format!("part fuelTank;\n        {statement}"),
            );
            assert!(
                shown.contains(&"fuelTank".to_string()),
                "{statement}: {shown:?}"
            );
            let (tank, fuel) = (
                shown.iter().position(|l| l == "fuelTank"),
                shown.iter().position(|l| l == "Fuel"),
            );
            assert!(tank > fuel, "the definition first: {statement}: {shown:?}");
        }
    }

    /// A position that takes keywords alone — an action body's
    /// statement start — builds no symbol table: nothing it offers is a
    /// name.
    #[test]
    fn keyword_positions_build_no_symbol_table() {
        let mut s = base_library_server();
        let uri = "file:///w/k.sysml";
        put(
            &mut s,
            uri,
            1,
            "package K {\n    action def A {\n        fo\n    }\n}\n",
        );
        crate::nav::WORK.with(|w| w.set([0; 3]));
        assert!(sort_key(&mut s, uri, 2, 10, "fork").is_some());
        assert_eq!(crate::nav::WORK.with(std::cell::Cell::get)[0], 0);
    }

    /// A re-seed that changes only the open documents' seeded copies —
    /// the host's analysis seeds every unit after each pause in typing —
    /// keeps the members named for an element; one that changes a unit
    /// not open names them again.
    #[test]
    fn members_survive_a_reseed_of_open_documents_only() {
        let mut s = base_library_server();
        let (uri, base) = ("file:///w/d.sysml", "file:///w/base.sysml");
        let d = |body: &str| {
            format!(
                "package D {{\n    private import A::*;\n    part def D :> Base {{\n        {body}\n    }}\n}}\n"
            )
        };
        let a = |extra: &str| {
            format!("package A {{\n    part def Base {{ attribute a1; {extra}}}\n}}\n")
        };
        s.set_workspace_sources(vec![(base.to_string(), a("")), (uri.to_string(), d(""))]);
        put(&mut s, uri, 1, &d("attribute :>> "));
        assert!(is_member(&mut s, uri, 3, 22, "a1"));
        // The host seeds the open document's new text.
        let typed = d("attribute :>> a1;\n        attribute :>> ");
        put(&mut s, uri, 2, &typed);
        s.set_workspace_sources(vec![
            (base.to_string(), a("")),
            (uri.to_string(), typed.clone()),
        ]);
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        crate::nav::MEMBER_READS.with(|n| n.set(0));
        assert!(!is_member(&mut s, uri, 4, 22, "a1"));
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        assert_eq!(crate::nav::MEMBER_READS.with(std::cell::Cell::get), 0);
        // A unit not open changes: the members are named again.
        s.set_workspace_sources(vec![
            (base.to_string(), a("attribute a2; ")),
            (uri.to_string(), typed),
        ]);
        assert!(is_member(&mut s, uri, 4, 22, "a2"));
    }

    /// The labels a completion at `line`/`character` of `uri` offers.
    fn labels_at(s: &mut PushServer, uri: &str, line: u32, character: u32) -> Vec<String> {
        let out = responses(
            s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": line, "character": character}}}),
        );
        completion_items(&out[0]["result"])
            .iter()
            .filter_map(|i| i["label"].as_str().map(str::to_string))
            .collect()
    }

    /// A re-seed that leaves every text as it was — the host seeds each
    /// open document after a pause in typing — keeps the completion
    /// session: the next request in the statement builds none. One that
    /// changes a unit not open builds again, and answers from the new
    /// text.
    #[test]
    fn a_reseed_of_unchanged_texts_keeps_the_completion_session() {
        let mut s = base_library_server();
        let (uri, base) = ("file:///w/r.sysml", "file:///w/base.sysml");
        let text =
            "package R {\n    private import B::*;\n    part v : V;\n    attribute a = v.\n}\n";
        let seed = |extra: &str| {
            vec![
                (
                    "file:///w/vehicles.sysml".to_string(),
                    VEHICLE_MODEL.to_string(),
                ),
                (
                    base.to_string(),
                    format!("package B {{ part def V {{ attribute m; {extra}}} }}\n"),
                ),
                (uri.to_string(), text.to_string()),
            ]
        };
        s.set_workspace_sources(seed(""));
        put(&mut s, uri, 1, text);
        assert!(labels_at(&mut s, uri, 3, 20).contains(&"m".to_string()));
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        s.set_workspace_sources(seed(""));
        assert!(labels_at(&mut s, uri, 3, 20).contains(&"m".to_string()));
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        s.set_workspace_sources(seed("attribute n; "));
        assert!(labels_at(&mut s, uri, 3, 20).contains(&"n".to_string()));
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 1);
    }

    /// The line and character right after the first `needle` in `text`.
    fn after(text: &str, needle: &str) -> (u32, u32) {
        let end = text.find(needle).expect("needle") + needle.len();
        let line = text[..end].matches('\n').count();
        let character = end - text[..end].rfind('\n').map_or(0, |i| i + 1);
        (
            u32::try_from(line).expect("short"),
            u32::try_from(character).expect("short"),
        )
    }

    /// The labels a completion right after the first `needle` in `text`,
    /// put as `uri`'s text at `version`, offers.
    fn labels_after(
        s: &mut PushServer,
        uri: &str,
        version: i32,
        text: &str,
        needle: &str,
    ) -> Vec<String> {
        put(s, uri, version, text);
        let (line, character) = after(text, needle);
        labels_at(s, uri, line, character)
    }

    /// The member access of the next statement of a body reads the
    /// session built for the last one where nothing it reads changed:
    /// the statement typed since, a re-seed of the open documents, and a
    /// document it does not read changing build nothing.
    #[test]
    fn the_next_member_access_builds_no_session() {
        let mut s = base_library_server();
        let (uri, other) = ("file:///w/w.sysml", "file:///w/o.sysml");
        let body = |statements: &str| {
            format!(
                "package W {{\n    private import VehicleModel::*;\n    part def Car2 :> Vehicle {{\n        \
                 part v : Vehicle;\n        {statements}\n    }}\n}}\n"
            )
        };
        // The host seeds every open document, in one order, before typing
        // and after each pause.
        let seed = |s: &mut PushServer, text: String, other_text: String| {
            s.set_workspace_sources(vec![
                (
                    "file:///w/vehicles.sysml".to_string(),
                    VEHICLE_MODEL.to_string(),
                ),
                (uri.to_string(), text),
                (other.to_string(), other_text),
            ]);
        };
        let first = "package O { part def P; }\n";
        seed(&mut s, body(""), first.to_string());
        put(&mut s, other, 1, first);
        let mut version = 1;
        let text = body("attribute a0 = v.");
        let labels = labels_after(&mut s, uri, version, &text, "a0 = v.");
        assert!(labels.contains(&"fuelIn".to_string()), "{labels:?}");
        let builds = || crate::nav::SESSION_BUILDS.with(std::cell::Cell::get);
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        let mut written = String::new();
        for k in 0..3 {
            written.push_str(&format!("attribute a{k} = v.mass;\n        "));
            version += 1;
            put(&mut s, uri, version, &body(written.trim_end()));
            seed(
                &mut s,
                body(written.trim_end()),
                format!("package O {{ part def P{k}; }}\n"),
            );
            put(
                &mut s,
                other,
                k + 2,
                &format!("package O {{ part def P{k}; }}\n"),
            );
            version += 1;
            let next = k + 1;
            let text = body(&format!("{written}attribute a{next} = v."));
            let labels = labels_after(&mut s, uri, version, &text, &format!("a{next} = v."));
            assert!(
                labels.contains(&"mass".to_string()) && labels.contains(&"fuelIn".to_string()),
                "{k}: {labels:?}"
            );
        }
        assert_eq!(builds(), 0);
    }

    /// A member access read off a session built for another statement
    /// answers as a new build would: a supertype gaining, renaming, or
    /// losing a feature in another document or statement, the receiver
    /// retyped or taken away, a declaration of the receiver's name
    /// nearer the statement, each is read from the text as it is.
    #[test]
    fn member_access_follows_what_it_reads() {
        let mut s = base_library_server();
        let (a, b) = ("file:///w/a.sysml", "file:///w/b.sysml");
        let base =
            |features: &str| format!("package A {{\n    part def Base {{ {features} }}\n}}\n");
        let d = |statements: &str| {
            format!(
                "package B {{\n    private import A::*;\n    part def Base2 {{ attribute b1; }}\n    \
                 part y : Base2;\n    part def D {{\n        part x : Base;\n        {statements}\n    }}\n}}\n"
            )
        };
        put(&mut s, a, 1, &base("attribute a1;"));
        let mut version = 0;
        let mut ask = |s: &mut PushServer, statements: &str, receiver: &str| {
            version += 1;
            let text = d(&format!("{statements}attribute q = {receiver}."));
            members(labels_after(
                s,
                b,
                version,
                &text,
                &format!("q = {receiver}."),
            ))
        };
        assert_eq!(ask(&mut s, "", "x"), ["a1"]);
        // The supertype, in another document: gains, renames, loses.
        put(&mut s, a, 2, &base("attribute a1; attribute a2;"));
        assert_eq!(ask(&mut s, "attribute p0;\n        ", "x"), ["a1", "a2"]);
        put(&mut s, a, 3, &base("attribute a1x; attribute a2;"));
        assert_eq!(ask(&mut s, "attribute p1;\n        ", "x"), ["a1x", "a2"]);
        put(&mut s, a, 4, &base("attribute a2;"));
        assert_eq!(ask(&mut s, "attribute p2;\n        ", "x"), ["a2"]);
        // The receiver retyped, then taken away.
        let retyped = "attribute p3;\n        ";
        let text =
            d(&format!("{retyped}attribute q = x.")).replace("part x : Base;", "part x : Base2;");
        version += 10;
        let listed = |s: &mut PushServer, version: i32, text: &str, needle: &str| {
            members(labels_after(s, b, version, text, needle))
        };
        assert_eq!(listed(&mut s, version, &text, "q = x."), ["b1"]);
        let text = d("attribute q = x.").replace("part x : Base;", "");
        version += 1;
        assert_eq!(
            listed(&mut s, version, &text, "q = x."),
            Vec::<String>::new()
        );
        // A declaration of the receiver's name nearer the statement: `y`
        // was the package's, typed `Base2`.
        version += 1;
        let text = d("attribute q = y.");
        assert_eq!(listed(&mut s, version, &text, "q = y."), ["b1"]);
        version += 1;
        let text = d("part y : Base;\n        attribute q = y.");
        assert_eq!(listed(&mut s, version, &text, "q = y."), ["a2"]);
        // The supertype's own body, in the document typed in.
        version += 1;
        let text = d("attribute q = y.").replace("attribute b1;", "attribute b1; attribute b2;");
        assert_eq!(listed(&mut s, version, &text, "q = y."), ["b1", "b2"]);
    }

    /// The members a member access lists, sorted, without the `metadata`
    /// keyword a receiver named by a reference also takes.
    fn members(mut labels: Vec<String>) -> Vec<String> {
        labels.retain(|l| l != "metadata");
        labels.sort();
        labels
    }

    /// The labels a member access at `needle` in `uri` offers once the
    /// documents `changed` take their new texts, on a server that read the
    /// same access for an earlier statement (`first`, with `documents` as
    /// they were) and on one built for the new texts alone: what the
    /// statement reads must agree.
    fn read_and_built(
        documents: &[(&str, &str)],
        first: (&str, &str, &str),
        changed: &[(&str, &str)],
        second: (&str, &str, &str),
    ) -> (Vec<String>, Vec<String>) {
        let mut s = base_library_server();
        for (uri, text) in documents {
            put(&mut s, uri, 1, text);
        }
        let (uri, text, needle) = first;
        labels_after(&mut s, uri, 1, text, needle);
        for (uri, text) in changed {
            put(&mut s, uri, 2, text);
        }
        let (uri, text, needle) = second;
        let read = labels_after(&mut s, uri, 2, text, needle);
        let mut fresh = base_library_server();
        for (doc, text) in documents {
            let text = changed
                .iter()
                .find(|(u, _)| u == doc)
                .map_or(*text, |(_, t)| *t);
            put(&mut fresh, doc, 1, text);
        }
        let (uri, text, needle) = second;
        let built = labels_after(&mut fresh, uri, 1, text, needle);
        (read, built)
    }

    /// A recursive import (`::**`) sees into the namespaces nested in its
    /// target, and into what the types there inherit: a declaration, an
    /// alias, or a re-export added there, a type added there that
    /// inherits the name looked up, or a general type of one there gaining
    /// such a base, has the next member access answer as a session built
    /// for its own text would — directly or through a package re-exporting
    /// the recursive import.
    #[test]
    fn member_access_after_what_a_recursive_import_sees() {
        let (lib, other, uri) = (
            "file:///w/lib.sysml",
            "file:///w/o.sysml",
            "file:///w/w.sysml",
        );
        let library = |extra: &str| {
            format!(
                "package Lib {{\n    package Inner {{\n        part def V1 {{ attribute a1; }}\n        \
                 part veh : V1;\n    }}\n    {extra}\n}}\n"
            )
        };
        let others = |general: &str| {
            format!(
                "package O {{\n    part def V9 {{ attribute z9; }}\n    part veh : V9;\n    \
                 part def Base9 {{ part veh : V9; }}\n    part def G{general};\n}}\n"
            )
        };
        let work = |import: &str, statements: &str| {
            format!(
                "package F {{ public import Lib::**; }}\npackage W {{\n    private import {import};\n    \
                 part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        for import in ["Lib::**", "F::*"] {
            for (added, general) in [
                (
                    "package Inner2 { part def V2 { attribute b2; } part veh : V2; }",
                    "",
                ),
                ("package Inner2 { alias veh for O::veh; }", ""),
                ("package Inner2 { public import O::*; }", ""),
                ("part def Holder :> O::Base9 { }", ""),
                ("part def Holder2 :> O::Base9;", ""),
                ("part def Holder :> O::G { }", " :> Base9"),
            ] {
                let first = work(import, "attribute q0 = veh.");
                let second = work(
                    import,
                    "attribute q0 = veh.a1;\n        attribute q1 = veh.",
                );
                let (lib_before, other_before) = (library(""), others(""));
                let (lib_after, other_after) = if general.is_empty() {
                    (library(added), others(""))
                } else {
                    // The general type of a type already there gains a base.
                    (library(added), others(general))
                };
                let documents = [
                    (other, other_before.as_str()),
                    (
                        lib,
                        if general.is_empty() {
                            lib_before.as_str()
                        } else {
                            lib_after.as_str()
                        },
                    ),
                ];
                let (read, built) = read_and_built(
                    &documents,
                    (uri, &first, "q0 = veh."),
                    &[(lib, &lib_after), (other, &other_after)],
                    (uri, &second, "q1 = veh."),
                );
                assert_eq!(read, built, "{import}: {added} {general}");
            }
        }
        // The type of a usage, and the callable invoked, found through it.
        let library = |extra: &str| {
            format!(
                "package Lib {{\n    package Inner {{\n        part def V1 {{ attribute a1; }}\n        \
                 calc def F {{ in a; in b; }}\n    }}\n    {extra}\n}}\n"
            )
        };
        let work = |statements: &str| {
            format!(
                "package W {{\n    private import Lib::**;\n    part veh : V1;\n    \
                 part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let (lib_before, lib_after) = (
            library(""),
            library("package Inner2 { part def V1 { attribute b1; } calc def F { in c; } }"),
        );
        let first = work("attribute q0 = veh.");
        let second = work("attribute q0 = veh.a1;\n        attribute q1 = veh.");
        let (read, built) = read_and_built(
            &[(lib, &lib_before)],
            (uri, &first, "q0 = veh."),
            &[(lib, &lib_after)],
            (uri, &second, "q1 = veh."),
        );
        assert_eq!(read, built, "a type found through the recursive import");
        let signature = |s: &mut PushServer, version: i32, text: &str, needle: &str| {
            put(s, uri, version, text);
            let (line, character) = after(text, needle);
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": line, "character": character}}}),
            )[0]["result"]
                .clone()
        };
        let mut s = base_library_server();
        put(&mut s, lib, 1, &lib_before);
        signature(&mut s, 1, &work("attribute s0 = F("), "s0 = F(");
        put(&mut s, lib, 2, &lib_after);
        let text = work("attribute s0 = F(1, 2);\n        attribute s1 = F(");
        let read = signature(&mut s, 2, &text, "s1 = F(");
        let mut fresh = base_library_server();
        put(&mut fresh, lib, 1, &lib_after);
        assert_eq!(
            read,
            signature(&mut fresh, 1, &text, "s1 = F("),
            "a callable found through the recursive import"
        );
    }

    /// What an import statement names resolves where the statement
    /// stands and in each namespace its path passes through: a namespace
    /// declared there under one of its names changes what the import
    /// brings in, and the next member access answers as a session built
    /// for its own text would.
    #[test]
    fn member_access_after_an_import_path_is_shadowed() {
        let (lib, uri) = ("file:///w/lib.sysml", "file:///w/w.sysml");
        let library = |extra: &str| {
            format!(
                "package Lib {{\n    package Inner {{\n        part def V1 {{ attribute a1; }}\n        \
                 part veh : V1;\n    }}\n    {extra}\n}}\n"
            )
        };
        let shadow = "package Inner { part def V5 { attribute z5; } part veh : V5; }";
        for (import, in_work) in [("Lib::Inner::*", true), ("Lib::Inner::*", false)] {
            let work = |extra: &str| {
                format!(
                    "package W {{\n    private import {import};\n    {extra}\n    part def D {{\n        \
                     attribute q0 = veh.\n    }}\n}}\n"
                )
            };
            let (work_before, lib_before) = (work(""), library(""));
            let (work_after, lib_after) = if in_work {
                (work(&shadow.replace("Inner", "Lib")), library(""))
            } else {
                (work(""), library(shadow))
            };
            let (read, built) = read_and_built(
                &[(lib, &lib_before), (uri, &work_before)],
                (uri, &work_before, "q0 = veh."),
                &[(lib, &lib_after), (uri, &work_after)],
                (uri, &work_after, "q0 = veh."),
            );
            assert_eq!(
                read,
                built,
                "{import}: shadowed in the {}",
                if in_work {
                    "importing package"
                } else {
                    "namespace looked into"
                }
            );
        }
        // The same for a name a declaration a recursive import sees into
        // names its type by: `holder : Defs::Defs::H0` looks into the type
        // `Defs`, where an `H0` of its own hides the one it inherits.
        let defs = "file:///w/d.sysml";
        let library = "package Lib {\n    part holder : Defs::Defs::H0;\n}\n";
        let definitions = |own: &str| {
            format!(
                "package Defs {{\n    part def V1 {{ attribute a1; }}\n    part def V9 {{ attribute z9; }}\n    \
                 part def DefsBase {{ part def H0 {{ part veh : V9; }} }}\n    \
                 part def Defs :> DefsBase {{ {own} }}\n}}\n"
            )
        };
        let work = |statements: &str| {
            format!(
                "package W {{\n    private import Lib::**;\n    part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let (defs_before, defs_after) = (
            definitions(""),
            definitions("part def H0 { part veh : V1; }"),
        );
        let first = work("attribute q0 = veh.");
        let second = work("attribute q0 = 1;\n        attribute q1 = veh.");
        let (read, built) = read_and_built(
            &[(lib, library), (defs, &defs_before)],
            (uri, &first, "q0 = veh."),
            &[(defs, &defs_after)],
            (uri, &second, "q1 = veh."),
        );
        assert_eq!(members(built.clone()), ["a1"], "the new type's");
        assert_eq!(
            read, built,
            "shadowed in a namespace a type's path looks into"
        );
    }

    /// A filtered import brings in what its condition admits, which reads
    /// the metadata of each member it is asked of: a member's annotation
    /// type losing the general type the condition names changes what the
    /// import brings in — a condition of the import, or a filter member
    /// of the namespace importing — and the next member access answers as
    /// a session built for its own text would.
    #[test]
    fn member_access_after_what_a_filter_reads_changes() {
        let (lib, uri) = ("file:///w/lib.sysml", "file:///w/w.sysml");
        let library = |general: &str| {
            format!(
                "package Lib {{\n    metadata def Safety;\n    metadata def Rated{general};\n    \
                 part def V1 {{ attribute a1; }}\n    part veh : V1 {{ @Rated; }}\n}}\n"
            )
        };
        for import in [
            "Lib::*[@Safety]",
            "Lib::**[@Safety]",
            "Lib::*;\n    filter @Safety",
        ] {
            let work = |statements: &str| {
                format!(
                    "package W {{\n    private import {import};\n    \
                     part def D {{\n        {statements}\n    }}\n}}\n"
                )
            };
            let (lib_before, lib_after) = (library(" :> Safety"), library(""));
            let first = work("attribute q0 = veh.");
            let second = work("attribute q0 = 1;\n        attribute q1 = veh.");
            let (read, built) = read_and_built(
                &[(lib, &lib_before)],
                (uri, &first, "q0 = veh."),
                &[(lib, &lib_after)],
                (uri, &second, "q1 = veh."),
            );
            assert_eq!(read, built, "{import}");
        }
    }

    /// A namespace import of a type (`import P::*`) brings in what the
    /// type inherits too: a general type of it gaining another base
    /// changes what the import brings in, and the next member access
    /// answers as a session built for its own text would.
    #[test]
    fn member_access_after_an_imported_type_changes() {
        let (a, uri) = ("file:///w/a.sysml", "file:///w/w.sysml");
        let types = |base: &str| {
            format!(
                "package A {{\n    part def X1 {{ attribute a1; }}\n    part def X3 {{ attribute a3; }}\n    \
                 part def H {{ part x : X1; }}\n    part def H3 {{ part x : X3; }}\n    \
                 part def G :> {base};\n    part def P :> G;\n}}\n"
            )
        };
        let work = |statements: &str| {
            format!(
                "package W {{\n    private import A::P::*;\n    part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let (before, after) = (types("H"), types("H3"));
        let first = work("attribute q0 = x.");
        let second = work("attribute q0 = 1;\n        attribute q1 = x.");
        let (read, built) = read_and_built(
            &[(a, &before)],
            (uri, &first, "q0 = x."),
            &[(a, &after)],
            (uri, &second, "q1 = x."),
        );
        assert_eq!(members(built.clone()), ["a3"]);
        assert_eq!(read, built);
    }

    /// A type a qualified name passes through (`P::x`, `: P::Q`) has its
    /// members from its general types: one of those gaining another base
    /// changes what the name finds, and the next member access answers as
    /// a session built for its own text would.
    #[test]
    fn member_access_after_a_type_a_name_passes_through_changes() {
        let (a, uri) = ("file:///w/a.sysml", "file:///w/w.sysml");
        let types = |base: &str| {
            format!(
                "package A {{\n    part def X1 {{ attribute a1; }}\n    part def X3 {{ attribute a3; }}\n    \
                 part def H {{ part x : X1; part def Q {{ attribute q1; }} }}\n    \
                 part def H3 {{ part x : X3; part def Q {{ attribute q3; }} }}\n    \
                 part def G :> {base};\n    part def P :> G;\n    part y : P::Q;\n}}\n"
            )
        };
        for (import, receiver) in [("A::*", "P::x"), ("A::*", "y")] {
            let work = |statements: &str| {
                format!(
                    "package W {{\n    private import {import};\n    part def D {{\n        {statements}\n    }}\n}}\n"
                )
            };
            let first = work(&format!("attribute q0 = {receiver}."));
            let second = work(&format!(
                "attribute q0 = 1;\n        attribute q1 = {receiver}."
            ));
            let (before, after) = (types("H"), types("H3"));
            let (read, built) = read_and_built(
                &[(a, before.as_str())],
                (uri, &first, &format!("q0 = {receiver}.")),
                &[(a, &after)],
                (uri, &second, &format!("q1 = {receiver}.")),
            );
            assert_eq!(read, built, "{import}: {receiver}");
        }
    }

    /// A general type re-exporting what it imports (`public import O::*`
    /// in its body) passes the imported namespace's members on: a member
    /// added there is listed by the next member access.
    #[test]
    fn member_access_after_a_re_exported_namespace_changes() {
        let (lib, other, uri) = (
            "file:///w/lib.sysml",
            "file:///w/o.sysml",
            "file:///w/w.sysml",
        );
        let library = "package Lib {\n    part def V1 { public import O::*; attribute a1; }\n    \
                       part veh : V1;\n}\n";
        let o = |extra: &str| format!("package O {{\n    attribute oo;\n    {extra}\n}}\n");
        let work = |statements: &str| {
            format!(
                "package W {{\n    private import Lib::*;\n    part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let (before, after) = (o(""), o("attribute oo2;"));
        let first = work("attribute q0 = veh.");
        let second = work("attribute q0 = veh.a1;\n        attribute q1 = veh.");
        let (read, built) = read_and_built(
            &[(lib, library), (other, &before)],
            (uri, &first, "q0 = veh."),
            &[(other, &after)],
            (uri, &second, "q1 = veh."),
        );
        assert_eq!(members(read.clone()), ["a1", "oo", "oo2"]);
        assert_eq!(read, built);
    }

    /// A usage typed by the type it is named as (`part T2 : T2;`) has the
    /// type found around it, not recorded among its targets: while that
    /// type has no members there is no inherited member to tell where they
    /// come from, and only the target the model did not report keeps the
    /// next member access from reading a session built before the type
    /// gained one.
    #[test]
    fn member_access_after_an_unreported_type_gains_a_member() {
        let (a, uri) = ("file:///w/a.sysml", "file:///w/w.sysml");
        let types = |members: &str| format!("package A {{\n    part def T2 {{ {members} }}\n}}\n");
        let work = |statements: &str| {
            format!(
                "package W {{\n    private import A::*;\n    part T2 : T2;\n    part x : T2;\n    \
                 part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let (before, after) = (types(""), types("attribute t2;"));
        let first = work("attribute q0 = x.");
        let second = work("attribute q0 = 1;\n        attribute q1 = x.");
        let (read, built) = read_and_built(
            &[(a, &before)],
            (uri, &first, "q0 = x."),
            &[(a, &after)],
            (uri, &second, "q1 = x."),
        );
        assert_eq!(read, built);
    }

    /// A statement that changes what a name finds without spelling the
    /// name — an import, a parameter or a result redefining the
    /// definition's by position, a subject — has the next member access
    /// answer as a session built for its own text would.
    #[test]
    fn member_access_after_what_changes_a_name_unspelled() {
        let head = "package A {\n    part def T1 { attribute t1; }\n    part x : T1;\n}\n\
                    package B {\n    part def T2 { attribute t2; }\n    part x : T2;\n}\n";
        let uri = "file:///w/c.sysml";
        for (open, before, receiver) in [
            (
                "package W {\n    private import A::*;\n    part def D {\n        ",
                "private import B::*;",
                "x",
            ),
            (
                "package W {\n    action def Act { in p : A::T1; }\n    action a : Act {\n        ",
                "in z : B::T2;",
                "p",
            ),
            (
                "package W {\n    calc def C { return r : A::T1; }\n    calc c : C {\n        ",
                "return s : B::T2;",
                "result",
            ),
            (
                "package W {\n    requirement def R { subject v : A::T1; }\n    \
                 requirement r : R {\n        ",
                "subject w : B::T2;",
                "subj",
            ),
        ] {
            let tail = "\n    }\n}\n";
            let first = format!("{head}{open}attribute q0 = {receiver}.{tail}");
            let second = format!("{head}{open}{before}\n        attribute q1 = {receiver}.{tail}");
            let q1 = format!("q1 = {receiver}.");
            let mut s = base_library_server();
            labels_after(&mut s, uri, 1, &first, &format!("q0 = {receiver}."));
            let answered = members(labels_after(&mut s, uri, 2, &second, &q1));
            let mut fresh = base_library_server();
            let expected = members(labels_after(&mut fresh, uri, 1, &second, &q1));
            assert_eq!(answered, expected, "{before}");
        }
    }

    /// A unit bracket read off a session built for another statement
    /// lists the units the workspace declares now: one declared since —
    /// in another document or in a statement of this one — renamed, or
    /// taken away is listed as it is, while statements declaring no unit
    /// build nothing.
    #[test]
    fn unit_brackets_follow_the_workspace_units() {
        let mut s = two_package_server();
        let (uri, other) = ("file:///w/u.sysml", "file:///w/v.sysml");
        let unit = |name: &str| {
            format!("attribute {name} : MeasurementReferences::TensorMeasurementReference;")
        };
        let other_doc = |names: &[&str]| {
            let units: Vec<String> = names.iter().map(|n| unit(n)).collect();
            format!("package V {{ {} }}\n", units.join(" "))
        };
        let doc = |statements: &str| {
            format!("package U {{\n    part def P {{\n        {statements}\n    }}\n}}\n")
        };
        put(&mut s, other, 1, &other_doc(&["vOne"]));
        let mut version = 1;
        let mut written = String::new();
        let mut bracket = |s: &mut PushServer, k: usize, before: &str| {
            written.push_str(before);
            let text = doc(&format!("{written}attribute x{k} = 5 ["));
            let labels = labels_after(s, uri, version, &text, &format!("x{k} = 5 ["));
            version += 1;
            written.push_str(&format!("attribute x{k} = 5;\n        "));
            labels
        };
        assert!(bracket(&mut s, 0, "").contains(&"vOne".to_string()));
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        let labels = bracket(&mut s, 1, "attribute y = 3;\n        ");
        assert!(labels.contains(&"vOne".to_string()), "{labels:?}");
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        for (k, (names, listed, unlisted)) in [
            (&["vOne", "vTwo"][..], "vTwo", "vThree"),
            (&["vOne", "vThree"], "vThree", "vTwo"),
            (&["vOne"], "vOne", "vThree"),
        ]
        .into_iter()
        .enumerate()
        {
            put(
                &mut s,
                other,
                i32::try_from(k).expect("short") + 2,
                &other_doc(names),
            );
            let labels = bracket(&mut s, k + 2, "");
            assert!(
                labels.contains(&listed.to_string()),
                "{names:?}: {labels:?}"
            );
            assert!(
                !labels.contains(&unlisted.to_string()),
                "{names:?}: {labels:?}"
            );
        }
        // Declared in a statement of the document typed in.
        let labels = bracket(&mut s, 9, &format!("{}\n        ", unit("uNine")));
        assert!(labels.contains(&"uNine".to_string()), "{labels:?}");
    }

    /// A unit is listed by its qualified name, which another declaration
    /// of its name beside it makes resolve elsewhere: one declared or
    /// taken away there has the next bracket list the units as a session
    /// built for its own text would.
    #[test]
    fn unit_brackets_follow_a_name_declared_twice() {
        let (uri, other) = ("file:///w/u.sysml", "file:///w/v.sysml");
        let other_doc = |twice: bool| {
            format!(
                "package V {{\n    attribute vOne : MeasurementReferences::TensorMeasurementReference;\n    {}\n}}\n",
                if twice { "attribute vOne;" } else { "" }
            )
        };
        let doc = |statements: &str| {
            format!("package U {{\n    part def P {{\n        {statements}\n    }}\n}}\n")
        };
        for (before, after) in [(true, false), (false, true)] {
            let mut s = two_package_server();
            put(&mut s, other, 1, &other_doc(before));
            labels_after(&mut s, uri, 1, &doc("attribute x0 = 5 ["), "x0 = 5 [");
            put(&mut s, other, 2, &other_doc(after));
            let text = doc("attribute x0 = 5;\n        attribute x1 = 5 [");
            let read = labels_after(&mut s, uri, 2, &text, "x1 = 5 [");
            let mut fresh = two_package_server();
            put(&mut fresh, other, 1, &other_doc(after));
            let built = labels_after(&mut fresh, uri, 1, &text, "x1 = 5 [");
            assert_eq!(read, built, "declared twice before: {before}");
            if !after {
                assert!(read.contains(&"vOne".to_string()), "{read:?}");
            }
        }
    }

    /// The units a bracket puts first where its value is an operand are
    /// those of the quantity the other operand measures as the model has
    /// it now: the operand retyped in another document takes the other
    /// type's units.
    #[test]
    fn unit_brackets_follow_the_operand_compared_with() {
        let mut s = two_package_server();
        let (uri, money) = ("file:///w/p.sysml", "file:///w/m.sysml");
        let quantity = |kind: &str| {
            format!(
                "package M {{\n    attribute def Cash :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute def Coin :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute usd : Cash;\n    attribute penny : Coin;\n    \
                 attribute def Money {{ attribute mRef : Cash; }}\n    \
                 attribute def Change {{ attribute mRef : Coin; }}\n    attribute price : {kind};\n}}\n"
            )
        };
        let doc = |statements: &str| {
            format!(
                "package P {{\n    private import M::*;\n    part def Q {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let first = |labels: &[String]| labels.first().cloned().unwrap_or_default();
        put(&mut s, money, 1, &quantity("Money"));
        let text = doc("attribute a = price <= 5 [");
        assert_eq!(first(&labels_after(&mut s, uri, 1, &text, "5 [")), "usd");
        put(&mut s, money, 2, &quantity("Change"));
        let text = doc("attribute a = price <= 5 [usd];\n        attribute b = price <= 5 [");
        assert_eq!(
            first(&labels_after(&mut s, uri, 2, &text, "b = price <= 5 [")),
            "penny"
        );
    }

    /// The units a bracket puts first are those of the quantity declared
    /// as the model has it now: a quantity type whose measurement
    /// reference changes in another document takes the other's units.
    #[test]
    fn unit_brackets_follow_the_declared_quantity() {
        let mut s = two_package_server();
        let (uri, money) = ("file:///w/p.sysml", "file:///w/m.sysml");
        let quantity = |unit: &str| {
            format!(
                "package M {{\n    attribute def Cash :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute def Coin :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute usd : Cash;\n    attribute penny : Coin;\n    \
                 attribute def Money {{ attribute mRef : {unit}; }}\n}}\n"
            )
        };
        let doc = |statements: &str| {
            format!(
                "package P {{\n    private import M::*;\n    part def Q {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let first = |labels: &[String]| labels.first().cloned().unwrap_or_default();
        put(&mut s, money, 1, &quantity("Cash"));
        let text = doc("attribute a : Money = 5 [");
        assert_eq!(first(&labels_after(&mut s, uri, 1, &text, "5 [")), "usd");
        put(&mut s, money, 2, &quantity("Coin"));
        let text = doc("attribute a : Money = 5 [usd];\n        attribute b : Money = 5 [");
        assert_eq!(
            first(&labels_after(&mut s, uri, 2, &text, "b : Money = 5 [")),
            "penny"
        );
    }

    /// The units a bracket puts first where its value is an argument are
    /// those of the quantity the parameter it binds measures as the model
    /// has it now — the callable's own parameter or one it inherits: the
    /// parameter's type specializing another quantity in another document
    /// takes that one's units.
    #[test]
    fn unit_brackets_follow_the_parameter_an_argument_binds() {
        let (uri, money) = ("file:///w/p.sysml", "file:///w/m.sysml");
        let quantity = |kind: &str| {
            format!(
                "package M {{\n    attribute def Cash :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute def Coin :> MeasurementReferences::TensorMeasurementReference;\n    \
                 attribute usd : Cash;\n    attribute penny : Coin;\n    \
                 attribute def Money {{ attribute mRef : Cash; }}\n    \
                 attribute def Change {{ attribute mRef : Coin; }}\n    attribute def Amount :> {kind};\n}}\n"
            )
        };
        let doc = |statements: &str| {
            format!(
                "package P {{\n    private import M::*;\n    calc def Pay {{ in amount : Amount; }}\n    \
                 calc def Repay :> Pay;\n    part def Q {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let first = |labels: &[String]| labels.first().cloned().unwrap_or_default();
        for callee in ["Pay", "Repay"] {
            let mut s = two_package_server();
            put(&mut s, money, 1, &quantity("Money"));
            let text = doc(&format!("attribute a = {callee}(5 ["));
            assert_eq!(
                first(&labels_after(&mut s, uri, 1, &text, "(5 [")),
                "usd",
                "{callee}"
            );
            put(&mut s, money, 2, &quantity("Change"));
            let text = doc(&format!(
                "attribute a = {callee}(5 [usd]);\n        attribute b = {callee}(5 ["
            ));
            let needle = format!("b = {callee}(5 [");
            assert_eq!(
                first(&labels_after(&mut s, uri, 2, &text, &needle)),
                "penny",
                "{callee}"
            );
        }
    }

    /// A library callable's parameter and result types are spelled the
    /// shortest way that resolves where the signature is read — those of
    /// a parameter or a result inherited, or of a parameter redefined
    /// without a type, too: a declaration of the type's name there since
    /// has the next statement's signature help spell it in full, as a
    /// session built for its own text would.
    #[test]
    fn signature_help_spells_types_where_it_is_read() {
        let server = || {
            let mut s = PushServer::with_library_sources(
                vec![(
                    "Calcs.sysml".to_string(),
                    "standard library package ScalarValues { attribute def Real; attribute def Integer; }\n\
                     standard library package Calcs {\n\
                     calc def Twice { in x : ScalarValues::Real; return : ScalarValues::Integer; }\n\
                     }\n"
                        .to_string(),
                )],
                None,
            );
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                    "params": {"capabilities": {"general": {"positionEncodings": ["utf-8"]}}}}),
            );
            s
        };
        let uri = "file:///w/s.sysml";
        let doc = |own: &str, statements: &str| {
            format!(
                "package S {{\n    private import Calcs::*;\n    private import ScalarValues::*;\n    \
                 {own}\n    calc def Thrice :> Twice;\n    calc def Again :> Twice {{ in :>> x; }}\n    \
                 part def U {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let signature = |s: &mut PushServer, version: i32, text: &str, needle: &str| {
            put(s, uri, version, text);
            let (line, character) = after(text, needle);
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": line, "character": character}}}),
            )[0]["result"]["signatures"][0]["label"]
                .clone()
        };
        for callee in ["Twice", "Thrice", "Again"] {
            for (own, spelled) in [
                ("attribute def Real;", "(x: ScalarValues::Real) → Integer"),
                (
                    "attribute def Integer;",
                    "(x: Real) → ScalarValues::Integer",
                ),
            ] {
                let mut s = server();
                let call = format!("{callee}(");
                let text = doc("", &format!("attribute a0 = {call}"));
                assert_eq!(
                    signature(&mut s, 1, &text, &call),
                    format!("{callee}(x: Real) → Integer")
                );
                let text = doc(own, &format!("attribute a0 = {call}"));
                let read = signature(&mut s, 2, &text, &call);
                let mut fresh = server();
                assert_eq!(read, signature(&mut fresh, 1, &text, &call), "{callee}");
                assert_eq!(read, format!("{callee}{spelled}"));
            }
        }
    }

    /// The signature help of the next statement reads the session built
    /// for the last one where the callable is as it was — nothing is
    /// built for it — and shows a parameter it gained since.
    #[test]
    fn signature_help_follows_the_callable() {
        let mut s = base_library_server();
        let (uri, calcs) = ("file:///w/s.sysml", "file:///w/c.sysml");
        let calc = |params: &str| format!("package C {{\n    calc def Twice {{ {params} }}\n}}\n");
        let doc = |statements: &str| {
            format!(
                "package S {{\n    private import C::*;\n    part def U {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let signature = |s: &mut PushServer, version: i32, text: &str, needle: &str| {
            put(s, uri, version, text);
            let (line, character) = after(text, needle);
            let out = responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/signatureHelp",
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": line, "character": character}}}),
            );
            out[0]["result"]["signatures"][0]["label"].clone()
        };
        put(&mut s, calcs, 1, &calc("in f; in x;"));
        let text = doc("attribute a0 = Twice(");
        assert_eq!(signature(&mut s, 1, &text, "Twice("), "Twice(f, x)");
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        let text = doc("attribute a0 = Twice(1, 2);\n        attribute a1 = Twice(");
        assert_eq!(signature(&mut s, 2, &text, "a1 = Twice("), "Twice(f, x)");
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        put(&mut s, calcs, 2, &calc("in f; in x; in y;"));
        let text = doc(
            "attribute a0 = Twice(1, 2);\n        attribute a1 = Twice(1, 2);\n        attribute a2 = Twice(",
        );
        assert_eq!(signature(&mut s, 3, &text, "a2 = Twice("), "Twice(f, x, y)");
    }

    /// A usage named as the type it is typed by (`part T2 : T2;`) has its
    /// typing found around it, not recorded as a target: the members
    /// reached through it follow that type's body all the same.
    #[test]
    fn member_access_follows_a_type_named_as_its_usage() {
        let mut s = base_library_server();
        let (a, b) = ("file:///w/a.sysml", "file:///w/b.sysml");
        let types = |t2: &str| {
            format!(
                "package A {{\n    part def T1 {{ attribute t1; }}\n    part def T2 :> T1 {{ {t2} }}\n}}\n"
            )
        };
        let doc = |statements: &str| {
            format!(
                "package B {{\n    private import A::*;\n    part x : T2;\n    part T2 : T2;\n    \
                 part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        put(&mut s, a, 1, &types("attribute t2;"));
        let text = doc("attribute q0 = x.");
        assert_eq!(
            members(labels_after(&mut s, b, 1, &text, "q0 = x.")),
            ["t1", "t2"]
        );
        put(&mut s, a, 2, &types("attribute w;"));
        let text = doc("attribute q0 = x.t1;\n        attribute q1 = x.");
        assert_eq!(
            members(labels_after(&mut s, b, 2, &text, "q1 = x.")),
            ["t1", "w"]
        );
    }

    /// Over random edits — features gained, lost and retyped, supertypes
    /// swapped, imports, aliases, parameters, annotations and units
    /// declared, statements that do not parse, declarations at a unit's
    /// top level — with re-seeds and navigation rebuilds between them, a
    /// server reading answers off sessions built for other texts answers
    /// each member access, unit bracket, and signature help as a server
    /// building one for it does.
    #[test]
    fn answers_read_off_other_texts_match_new_builds() {
        struct Rng(u64);
        impl Rng {
            fn below(&mut self, n: usize) -> usize {
                self.0 ^= self.0 << 13;
                self.0 ^= self.0 >> 7;
                self.0 ^= self.0 << 17;
                usize::try_from(self.0 % n as u64).expect("small")
            }
            fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
                xs[self.below(xs.len())]
            }
        }
        let names = ["t1", "t2", "x", "y", "z", "w", "p", "T1", "T2", "u1", "C"];
        let types = ["T1", "T2", "Q", "U1", "C::C0"];
        let (a_uri, b_uri, c_uri) = (
            "file:///w/a.sysml",
            "file:///w/b.sysml",
            "file:///w/c.sysml",
        );
        let answer = |s: &mut PushServer, text: &str, offset: usize, signature: bool| {
            let line = text[..offset].matches('\n').count();
            let character = offset - text[..offset].rfind('\n').map_or(0, |i| i + 1);
            let method = if signature {
                "textDocument/signatureHelp"
            } else {
                "textDocument/completion"
            };
            let out = responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": method,
                    "params": {"textDocument": {"uri": b_uri},
                               "position": {"line": line, "character": character}}}),
            );
            out.iter()
                .find(|m| m["id"] == 3)
                .map(|m| m["result"].to_string())
                .unwrap_or_default()
        };
        crate::nav::REUSED_ANSWERS.with(|n| n.set(0));
        for seed in 1..=4u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
            let (mut t1, mut t2) = (
                vec!["attribute t1;".to_string()],
                vec!["attribute t2;".to_string()],
            );
            let mut a_rest = vec![
                "part x : T1;".to_string(),
                "attribute def U1 :> MeasurementReferences::TensorMeasurementReference;"
                    .to_string(),
                "attribute u1 : U1;".to_string(),
                "attribute def Q { attribute mRef : U1; }".to_string(),
                "calc def F { in a; in b; }".to_string(),
            ];
            let (mut general, mut body, mut outer) =
                ("T1", vec!["part y : T2;".to_string()], Vec::new());
            let mut package: Vec<String> = Vec::new();
            let mut c = vec!["part def C0 { attribute c0; }".to_string()];
            let mut long = two_package_server();
            let mut versions = [0; 3];
            for step in 0..40 {
                let (n, m, ty) = (rng.pick(&names), rng.pick(&names), rng.pick(&types));
                match rng.below(16) {
                    0 => t1.push(format!("attribute {n};")),
                    1 => drop(t1.pop()),
                    2 => t2.push(format!("part {n} : {ty};")),
                    3 => a_rest.push(format!("part {n} : {ty};")),
                    4 => general = rng.pick(&["T1", "T2", "Q", "C::C0"]),
                    5 => body.push(format!("part {n} : {ty};")),
                    6 => body.push(format!("attribute {n} = {m};")),
                    7 => body.push(
                        rng.pick(&[
                            "private import C::*;",
                            "alias w for x;",
                            "in p : T2;",
                            "@Q;",
                            "attribute :>> t1;",
                            "part :>> y : T1;",
                            "attribute bad = ;",
                            "doc /* d */",
                        ])
                        .to_string(),
                    ),
                    8 => drop(body.pop()),
                    9 => outer.push(format!("part {n} : {ty};")),
                    10 => a_rest.push(format!("attribute {n} : U1;")),
                    11 => a_rest.push(format!("calc def F {{ in {n}; in {m}; }}")),
                    12 => c.push(format!("part def {n} {{ attribute {m}; }}")),
                    13 => a_rest.push(format!("attribute def Q {{ attribute mRef : {ty}; }}")),
                    14 => package.push(format!("part {n} : {ty};")),
                    _ => t2.push(format!("attribute {n};")),
                }
                let a = format!(
                    "package A {{\n    part def T1 {{ {} }}\n    part def T2 :> T1 {{ {} }}\n    {}\n}}\n",
                    t1.join(" "),
                    t2.join(" "),
                    a_rest.join("\n    ")
                );
                let c_text = format!("package C {{ {} }}\n{}\n", c.join(" "), outer.join("\n"));
                let receiver = rng.pick(&[
                    "x", "y", "z", "w", "t1", "p", "u1", "C::C0", "F(1, 2)", "y.t1",
                ]);
                let (statement, signature) = match rng.below(5) {
                    0 | 1 => (format!("attribute q{step} = {receiver}."), false),
                    2 => (format!("attribute b{step} = 5 ["), false),
                    3 => (format!("attribute b{step} : Q = 5 ["), false),
                    _ => (format!("attribute s{step} = F("), true),
                };
                let before = format!(
                    "package B {{\n    private import A::*;\n    {}\n    part def D :> {general} {{\n        {}\n        ",
                    package.join("\n    "),
                    body.join("\n        ")
                );
                let b = format!("{before}{statement}\n    }}\n}}\n");
                let offset = before.len() + statement.len();
                let texts = [
                    (a_uri, a.as_str()),
                    (c_uri, c_text.as_str()),
                    (b_uri, b.as_str()),
                ];
                if step == 0 || rng.below(3) == 0 {
                    long.set_workspace_sources(
                        texts
                            .iter()
                            .map(|(u, t)| (u.to_string(), t.to_string()))
                            .collect(),
                    );
                }
                for (i, (uri, text)) in texts.iter().enumerate() {
                    versions[i] += 1;
                    put(&mut long, uri, versions[i], text);
                }
                if rng.below(4) == 0 {
                    // A navigation session over the statements finished.
                    versions[2] += 1;
                    put(
                        &mut long,
                        b_uri,
                        versions[2],
                        &format!("{before}\n    }}\n}}\n"),
                    );
                    responses(
                        &mut long,
                        &serde_json::json!({"jsonrpc": "2.0", "id": 4, "method": "textDocument/inlayHint",
                            "params": {"textDocument": {"uri": b_uri},
                                       "range": {"start": {"line": 0, "character": 0},
                                                 "end": {"line": 99, "character": 0}}}}),
                    );
                    versions[2] += 1;
                    put(&mut long, b_uri, versions[2], &b);
                }
                let read = answer(&mut long, &b, offset, signature);
                let mut fresh = two_package_server();
                for (uri, text) in texts {
                    put(&mut fresh, uri, 1, text);
                }
                let built = answer(&mut fresh, &b, offset, signature);
                assert_eq!(read, built, "seed {seed}, step {step}:\n{a}\n{c_text}\n{b}");
            }
        }
        assert!(crate::nav::REUSED_ANSWERS.with(std::cell::Cell::get) > 20);
    }

    /// While a unit does not parse, read-only navigation's tolerant
    /// session — the units that do not parse salvaged — answers the next
    /// member access as any session built does, nothing built for it;
    /// what plans over every reference still answers nothing, and a
    /// hover past the statement being typed still reads the document as
    /// written.
    #[test]
    fn the_tolerant_session_answers_completion_alone() {
        let mut s = base_library_server();
        let (uri, broken) = ("file:///w/a.sysml", "file:///w/b.sysml");
        let doc = |statements: &str| {
            format!(
                "package A {{\n    part def V {{ attribute m; }}\n    part v : V;\n    part def D {{\n        \
                 {statements}\n    }}\n    part w : V;\n}}\n"
            )
        };
        put(
            &mut s,
            broken,
            1,
            "package B {\n    part def X { attribute = ; }\n}\n",
        );
        let text = doc("attribute q0 = 1;");
        put(&mut s, uri, 1, &text);
        let ask = |s: &mut PushServer, method: &str, text: &str, needle: &str| {
            let (line, character) = after(text, needle);
            responses(
                s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 5, "method": method,
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": line, "character": character},
                               "context": {"includeDeclaration": true}}}),
            )[0]["result"]
                .clone()
        };
        // A hover builds the tolerant session: the strict one cannot.
        assert!(!ask(&mut s, "textDocument/hover", &text, "m; }\n    part ").is_null());
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        crate::nav::REUSED_ANSWERS.with(|n| n.set(0));
        let text = doc("attribute q0 = 1;\n        attribute q1 = v.");
        let labels = labels_after(&mut s, uri, 2, &text, "q1 = v.");
        assert_eq!(members(labels), ["m"]);
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        assert_eq!(crate::nav::REUSED_ANSWERS.with(std::cell::Cell::get), 1);
        // References plan over every reference: none off a salvaged model.
        assert!(ask(&mut s, "textDocument/references", &text, "part def ").is_null());
        // A hover past the statement reads the document as written.
        let hover = ask(&mut s, "textDocument/hover", &text, "    }\n    part ");
        let (line, _) = after(&text, "    }\n    part ");
        assert_eq!(hover["range"]["start"]["line"], line, "{hover}");
    }

    /// The members an element inherits are named off a model whose body
    /// may redefine them all — navigation's, built while the statement
    /// being edited was finished — and still come back, as when the body
    /// redefines only some: the statement being edited redefines nothing
    /// yet.
    #[test]
    fn members_come_back_when_the_model_redefines_them_all() {
        let (a, b) = ("file:///w/a.sysml", "file:///w/b.sysml");
        let doc = |statement: &str| {
            format!(
                "package B {{\n    private import A::*;\n    part def D :> T1 {{\n        {statement}\n    }}\n}}\n"
            )
        };
        let mut s = base_library_server();
        put(
            &mut s,
            a,
            1,
            "package A {\n    part def T1 { attribute x; }\n}\n",
        );
        put(&mut s, b, 1, &doc("attribute :>> x;"));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/inlayHint",
                "params": {"textDocument": {"uri": b},
                           "range": {"start": {"line": 0, "character": 0},
                                     "end": {"line": 6, "character": 0}}}}),
        );
        let text = doc("attribute :>> x");
        put(&mut s, b, 2, &text);
        let (line, character) = after(&text, "attribute :>> x");
        assert!(is_member(&mut s, b, line, character, "x"));
    }

    /// The members an element inherits are not named off read-only
    /// navigation's tolerant session, which salvages the statement being
    /// typed into the body as the declaration it reads as: a type with
    /// two features of one name loses neither where that statement
    /// redefines one, as a session built for the statement has it.
    #[test]
    fn members_are_not_named_off_a_statement_salvaged_into_the_body() {
        let (a, b, broken) = (
            "file:///w/a.sysml",
            "file:///w/b.sysml",
            "file:///w/t.sysml",
        );
        let text = "package B {\n    private import A::*;\n    part def E :> T1 {\n        part z;\n        \
                    attribute :>> x\n    }\n}\n";
        let mut s = base_library_server();
        put(
            &mut s,
            a,
            1,
            "package A {\n    part def T1 { attribute x; part x; }\n}\n",
        );
        put(&mut s, broken, 1, "part def f {\n");
        put(&mut s, b, 1, text);
        // A hover builds the tolerant session: a unit does not parse.
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/hover",
                "params": {"textDocument": {"uri": a},
                           "position": {"line": 1, "character": 15}}}),
        );
        let (line, character) = after(text, "attribute :>> x");
        assert!(is_member(&mut s, b, line, character, "x"));
    }

    /// A navigation session built since the last statement — inlay
    /// hints ask for one whenever the documents parse — answers the next
    /// member access: nothing is built for it.
    #[test]
    fn member_access_reads_a_navigation_session() {
        let mut s = base_library_server();
        let uri = "file:///w/n.sysml";
        let body = |statements: &str| {
            format!(
                "package N {{\n    private import VehicleModel::*;\n    part v : Vehicle;\n    \
                 part def D {{\n        {statements}\n    }}\n}}\n"
            )
        };
        let labels = labels_after(&mut s, uri, 1, &body("attribute q = v."), "q = v.");
        assert!(labels.contains(&"mass".to_string()), "{labels:?}");
        put(&mut s, uri, 2, &body("attribute q = v.mass;"));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/inlayHint",
                "params": {"textDocument": {"uri": uri},
                           "range": {"start": {"line": 0, "character": 0},
                                     "end": {"line": 9, "character": 0}}}}),
        );
        crate::nav::SESSION_BUILDS.with(|n| n.set(0));
        crate::nav::REUSED_ANSWERS.with(|n| n.set(0));
        let text = body("attribute q = v.mass;\n        attribute r = v.");
        let labels = labels_after(&mut s, uri, 3, &text, "r = v.");
        assert!(labels.contains(&"mass".to_string()), "{labels:?}");
        assert_eq!(crate::nav::SESSION_BUILDS.with(std::cell::Cell::get), 0);
        assert_eq!(crate::nav::REUSED_ANSWERS.with(std::cell::Cell::get), 1);
    }

    /// A navigation session rebuilt between statements — inlay hints
    /// ask for one whenever the document parses — reads no members
    /// again: those named for an element stand while the text outside
    /// its body does.
    #[test]
    fn a_navigation_rebuild_reads_no_members_again() {
        let mut s = base_library_server();
        let uri = "file:///w/n.sysml";
        let text = |body: &str| {
            format!(
                "package N {{\n    private import VehicleModel::*;\n    \
                 part def Car2 :> Vehicle {{\n        {body}\n    }}\n}}\n"
            )
        };
        put(&mut s, uri, 1, &text("attribute :>> "));
        assert!(is_member(&mut s, uri, 3, 22, "mass"));
        put(&mut s, uri, 2, &text("attribute :>> mass;"));
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "textDocument/inlayHint",
                "params": {"textDocument": {"uri": uri},
                           "range": {"start": {"line": 0, "character": 0},
                                     "end": {"line": 6, "character": 0}}}}),
        );
        crate::nav::MEMBER_READS.with(|n| n.set(0));
        put(
            &mut s,
            uri,
            3,
            &text("attribute :>> mass;\n        port :>> "),
        );
        assert!(is_member(&mut s, uri, 4, 17, "fuelIn"));
        assert_eq!(crate::nav::MEMBER_READS.with(std::cell::Cell::get), 0);
    }

    /// The library's renderings complete after `render`. This pins what
    /// the position rules gave once they classified `render`, before the
    /// enclosing element's members were named: nothing here depends on
    /// those.
    #[test]
    fn render_offers_the_library_renderings() {
        let mut s = base_library_server();
        let (shown, _) = listed(
            &mut s,
            "file:///w/a.sysml",
            "}\n    view def V {\n        render as|",
        );
        assert_eq!(shown, ["asTreeDiagram", "asElementTable"]);
    }

    /// A document is offered its own dialect's keywords only: a KerML
    /// document no `part`, a SysML document no `const`.
    #[test]
    fn documents_get_their_dialects_keywords() {
        for (uri, has, lacks) in [
            (
                "file:///w/k.kerml",
                &["class", "datatype", "feature"],
                &["part", "parallel", "calc"],
            ),
            (
                "file:///w/s.sysml",
                &["part", "calc", "constant"],
                &["const", "datatype", "featuring"],
            ),
        ] {
            let mut s = two_package_server();
            responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": {"uri": uri, "languageId": "sysml",
                                     "version": 1, "text": "package K {\n    \n}\n"}}}),
            );
            let out = responses(
                &mut s,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                    "params": {"textDocument": {"uri": uri},
                               "position": {"line": 1, "character": 4}}}),
            );
            let items = out[0]["result"].as_array().expect("completion items");
            let labels = completion_labels(items);
            for word in has {
                assert!(labels.contains(word), "{uri}: {word}");
            }
            for word in lacks {
                assert!(!labels.contains(word), "{uri}: {word}");
            }
        }
    }

    /// A workspace re-seed on a running server invalidates inlay hints
    /// and code lenses the client already pulled — refresh requests go
    /// out, but only to clients that declared support, and never
    /// before `initialize` (nothing has been pulled yet).
    #[test]
    fn workspace_reseed_requests_refresh() {
        let seed = || vec![("file:///w/a.sysml".to_string(), "package A;".to_string())];
        let outbound = |s: &mut PushServer| -> Vec<String> {
            s.take_outbound()
                .expect("serializable outbound")
                .iter()
                .map(|m| {
                    let v: serde_json::Value = serde_json::from_str(m).expect("valid json");
                    v["method"].as_str().unwrap_or_default().to_string()
                })
                .collect()
        };

        let mut s = PushServer::new();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"workspace": {
                    "inlayHint": {"refreshSupport": true},
                    "codeLens": {"refreshSupport": true}}}}}),
        );
        s.set_workspace_sources(seed());
        let methods = outbound(&mut s);
        assert!(
            methods.contains(&"workspace/inlayHint/refresh".to_string())
                && methods.contains(&"workspace/codeLens/refresh".to_string()),
            "expected refresh requests, got {methods:?}"
        );

        // No declared support: no requests.
        let mut s = PushServer::new();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {}}}),
        );
        s.set_workspace_sources(seed());
        assert_eq!(outbound(&mut s), Vec::<String>::new());

        // Pre-initialize seeding: nothing to refresh.
        let mut s = PushServer::new();
        s.set_workspace_sources(seed());
        assert_eq!(outbound(&mut s), Vec::<String>::new());
    }

    /// Flipping the redundant-hint suppression on a running server
    /// changes pull-tier answers without any source changing — the
    /// client is asked to re-pull inlay hints (a pre-`initialize` flip
    /// just records the value for the server build).
    #[test]
    fn hide_redundant_flip_requests_refresh() {
        let outbound = |s: &mut PushServer| -> Vec<String> {
            s.take_outbound()
                .expect("serializable outbound")
                .iter()
                .map(|m| {
                    let v: serde_json::Value = serde_json::from_str(m).expect("valid json");
                    v["method"].as_str().unwrap_or_default().to_string()
                })
                .collect()
        };

        let mut s = PushServer::new();
        s.set_hide_redundant_value_hints(false);
        assert_eq!(outbound(&mut s), Vec::<String>::new());
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {"capabilities": {"workspace": {
                    "inlayHint": {"refreshSupport": true}}}}}),
        );
        s.set_hide_redundant_value_hints(true);
        let methods = outbound(&mut s);
        assert!(
            methods.contains(&"workspace/inlayHint/refresh".to_string()),
            "expected a refresh request, got {methods:?}"
        );
    }
}
