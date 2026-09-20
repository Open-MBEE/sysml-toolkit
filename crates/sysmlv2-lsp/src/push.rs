//! Push-driven frontend: drive the server one
//! message at a time — no threads, no blocking reads, no filesystem.
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
//! - no root-directory walk (there is no disk); the standard library,
//!   when wanted, arrives as in-memory sources
//!   ([`PushServer::with_library_sources`]) and feeds navigation and
//!   completions, and the workspace's units arrive the same way
//!   ([`PushServer::set_workspace_sources`]) so navigation crosses
//!   into units the client has not opened.

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
                                 "version": 1, "text": "package P { part def X; }"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 0, "character": 12}}}),
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
                                 "text": "package P {\n    private import OtherLib::*;\n    part w : \n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 2, "character": 13}}}),
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
        let items = out[0]["result"].as_array().expect("completion items");
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

    /// Accepting a suggestion also repairs the statement being typed
    /// (autofix): unclosed quantity brackets close and the terminal
    /// `;` appears — riding the main edit on a bare tail, as an
    /// insertion behind an already-auto-closed bracket otherwise.
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
                "newText": "'m/s²'];"
            }),
            "bracket close + terminator ride the main edit"
        );
        // The import edit rides along as before.
        assert_eq!(
            unit["additionalTextEdits"][0]["newText"],
            "private import MiniLib::'m/s²';\n    "
        );

        // Auto-closed variant: `]` already after the cursor — the `;`
        // becomes its own insertion behind it.
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
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(
            unit["textEdit"]["newText"], "'m/s²'",
            "no suffix on the main edit"
        );
        let extras = unit["additionalTextEdits"].as_array().expect("extras");
        assert_eq!(extras.len(), 2, "import + terminator: {extras:?}");
        assert_eq!(
            extras[1],
            serde_json::json!({
                "range": {"start": {"line": 1, "character": 31},
                          "end": {"line": 1, "character": 31}},
                "newText": ";"
            }),
            "terminator lands behind the existing `]`"
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
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(unit["textEdit"]["newText"], "'m/s²'");
        assert_eq!(
            unit["additionalTextEdits"].as_array().map(|a| a.len()),
            Some(1),
            "import only — no repairs on a terminated statement"
        );
    }

    /// A snippet-capable client gets the repair suffix behind a `$0`
    /// stop: accepting leaves the cursor after the accepted name,
    /// before the auto-inserted `];`, where typing continues.
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
            unit["textEdit"]["newText"], "'m/s²'$0];",
            "cursor stop between the name and the repair suffix"
        );
        assert_eq!(unit["insertTextFormat"], 2, "snippet format declared");

        // An import-context accept carries its `;` the same way.
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
        assert_eq!(widget["textEdit"]["newText"], "MiniLib::Widget$0;");
        assert_eq!(widget["insertTextFormat"], 2);

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
        let items = out[0]["result"].as_array().expect("completion items");
        let unit = items.iter().find(|i| i["label"] == "m/s²").expect("m/s²");
        assert_eq!(unit["textEdit"]["newText"], "'m/s²'");
        assert!(unit["insertTextFormat"].is_null(), "plain edit stays plain");
    }

    /// An accept landing mid-chain (`fuelTank.over|.volume`) keeps the
    /// tail and lands the terminator behind it as its own insertion —
    /// the cursor (end of the main insertion) stays at the accepted
    /// name: `fuelTank.overhead|.volume;`.
    #[test]
    fn terminator_lands_behind_a_chain_tail() {
        let mut s = two_package_server();
        responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": "file:///w/m.sysml", "languageId": "sysml",
                                 "version": 1,
                                 "text": "package P {\n    attribute g = Widge.value\n}\n"}}}),
        );
        let out = responses(
            &mut s,
            &serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/completion",
                "params": {"textDocument": {"uri": "file:///w/m.sysml"},
                           "position": {"line": 1, "character": 23}}}),
        );
        let items = out[0]["result"].as_array().expect("completion items");
        let widget = items
            .iter()
            .find(|i| i["label"] == "Widget")
            .expect("Widget");
        let extras = widget["additionalTextEdits"].as_array().expect("extras");
        let terminator = extras.last().expect("terminator edit");
        assert_eq!(
            terminator,
            &serde_json::json!({
                "range": {"start": {"line": 1, "character": 29},
                          "end": {"line": 1, "character": 29}},
                "newText": ";"
            }),
            "terminator lands at the end of the chain tail"
        );
    }

    /// After a feature-chain dot (`oxidizerTank.`) the list is the
    /// members the step can reach — the feature's own body, its
    /// declared type's features, and inherited ones — not the
    /// position-blind pile; and the statement still gets its `;`.
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
            vec!["extra", "containedliquid", "liquidMass", "capacity"],
            "own body, declared type, then inherited — nothing else"
        );
        let mass = items
            .iter()
            .find(|i| i["label"] == "liquidMass")
            .expect("liquidMass");
        assert_eq!(
            mass["textEdit"]["newText"], "liquidMass;",
            "the statement repair rides along"
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

        // An unresolvable head falls back to the position-blind list.
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
        assert!(
            completion_labels(items).contains(&"part"),
            "fallback keeps the keyword tier"
        );
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

    fn two_package_server() -> PushServer {
        two_package_server_with_caps(&serde_json::json!(
            {"general": {"positionEncodings": ["utf-8"]}}))
    }

    fn two_package_server_with_caps(capabilities: &serde_json::Value) -> PushServer {
        let mut s = PushServer::with_library_sources(
            vec![(
                "MiniLib.kerml".to_string(),
                "standard library package MiniLib { class Widget; class Gadget; \
                 feature <'m/s²'> 'metre per second squared'; } \
                 standard library package OtherLib { class Bolt; }"
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

    /// The half-typed import parses as a declaration of the typed word
    /// itself; that phantom symbol must not be offered back (it would
    /// outrank the real target with a self-referential path).
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
