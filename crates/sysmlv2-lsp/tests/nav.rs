#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Navigation harness: definition, references, hover, highlights,
//! rename, workspace symbols — driven through the wire like an editor,
//! over a two-file workspace so cross-file behavior is the default case.

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{DidOpenTextDocument, Exit, Initialized};
use lsp_types::request::{
    GotoDefinition, HoverRequest, Initialize, References, Rename, Shutdown, WorkspaceSymbolRequest,
};
use lsp_types::{
    DidOpenTextDocumentParams, GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverParams,
    InitializeParams, Location, Position, ReferenceContext, ReferenceParams, RenameParams,
    TextDocumentIdentifier, TextDocumentItem, TextDocumentPositionParams, Uri, WorkspaceEdit,
    WorkspaceSymbolParams,
};
use std::str::FromStr;
use std::thread::JoinHandle;

const DEFS: &str =
    "package Defs {\n    part def Wheel {\n        attribute radius : Real;\n    }\n}\n";
const USES: &str =
    "package Uses {\n    import Defs::*;\n    part w1 : Wheel;\n    part w2 : Wheel;\n}\n";

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
        Self::start_with_root(None)
    }

    fn start_with_root(root: Option<&std::path::Path>) -> Client {
        Self::start_configured(root, None)
    }

    fn start_with_library(lib: std::path::PathBuf) -> Client {
        Self::start_configured(None, Some(lib))
    }

    fn start_configured(root: Option<&std::path::Path>, lib: Option<std::path::PathBuf>) -> Client {
        let (server_side, client_side) = Connection::memory();
        let server = std::thread::spawn(move || sysmlv2_lsp::run_with_library(server_side, lib));
        let mut c = Client {
            conn: client_side,
            server: Some(server),
            next_id: 0,
        };
        #[allow(deprecated)] // root_uri: what real clients send
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

    fn request<R: lsp_types::request::Request>(
        &mut self,
        params: R::Params,
    ) -> Result<R::Result, String> {
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
                    if let Some(e) = error {
                        return Err(e.message);
                    }
                    return Ok(serde_json::from_value(result.unwrap_or_default()).unwrap());
                }
                _ => continue,
            }
        }
    }

    fn request_ok<R: lsp_types::request::Request>(&mut self, params: R::Params) -> R::Result {
        self.request::<R>(params).expect("request failed")
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
        // Consume the diagnostics publish so requests stay in lockstep.
        loop {
            if let Message::Notification(n) = self.conn.receiver.recv().unwrap() {
                if n.method == "textDocument/publishDiagnostics" {
                    return;
                }
            }
        }
    }

    fn pos_params(uri: &Uri, line: u32, character: u32) -> TextDocumentPositionParams {
        TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: Position { line, character },
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

fn workspace() -> (Client, Uri, Uri) {
    let client = Client::start();
    let defs = uri("defs.sysml");
    let uses = uri("uses.sysml");
    client.open(&defs, DEFS);
    client.open(&uses, USES);
    (client, defs, uses)
}

#[test]
fn definition_crosses_files() {
    let (mut client, defs, uses) = workspace();
    // `Wheel` in `part w1 : Wheel;` — line 2, col 15.
    let resp = client.request_ok::<GotoDefinition>(GotoDefinitionParams {
        text_document_position_params: Client::pos_params(&uses, 2, 15),
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    });
    let Some(GotoDefinitionResponse::Scalar(loc)) = resp else {
        panic!("expected a definition: {resp:?}");
    };
    assert_eq!(loc.uri, defs);
    assert_eq!(
        loc.range.start,
        Position {
            line: 1,
            character: 13
        }
    );
    assert_eq!(loc.range.end.character, 18, "the `Wheel` name token");
    client.shutdown();
}

/// An `about` target naming a documentation or comment element jumps
/// to that element's declared name — by local name and by qualified
/// name, like any other member.
#[test]
fn definition_reaches_named_documentation() {
    let mut client = Client::start();
    let doc = uri("doc.sysml");
    client.open(
        &doc,
        "package P {\n    part def Vehicle {\n        doc vehicleDoc /* A vehicle. */\n        comment about vehicleDoc /* about the doc */\n    }\n    comment about Vehicle::vehicleDoc /* qualified */\n}\n",
    );
    let mut definition = |line: u32, character: u32| -> Location {
        let resp = client.request_ok::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: Client::pos_params(&doc, line, character),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
        let Some(GotoDefinitionResponse::Scalar(loc)) = resp else {
            panic!("expected a definition at {line}:{character}: {resp:?}");
        };
        loc
    };
    let declared = Position {
        line: 2,
        character: 12,
    };
    // `vehicleDoc` in `comment about vehicleDoc` — line 3, col 22.
    let loc = definition(3, 25);
    assert_eq!(loc.uri, doc);
    assert_eq!(loc.range.start, declared);
    assert_eq!(loc.range.end.character, 22, "the `vehicleDoc` name token");
    // `vehicleDoc` in `comment about Vehicle::vehicleDoc` — line 5, col 27.
    let loc = definition(5, 30);
    assert_eq!(loc.uri, doc);
    assert_eq!(loc.range.start, declared);
    client.shutdown();
}

#[test]
fn references_span_the_workspace() {
    let (mut client, defs, uses) = workspace();
    // Ask from the *declaration* (defs.sysml line 1 col 14).
    let locs: Option<Vec<Location>> = client.request_ok::<References>(ReferenceParams {
        text_document_position: Client::pos_params(&defs, 1, 14),
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: ReferenceContext {
            include_declaration: true,
        },
    });
    let locs = locs.expect("references");
    let in_defs = locs.iter().filter(|l| l.uri == defs).count();
    let in_uses = locs.iter().filter(|l| l.uri == uses).count();
    assert_eq!(in_defs, 1, "the declaration itself: {locs:?}");
    assert_eq!(in_uses, 2, "w1 and w2 typings: {locs:?}");
    client.shutdown();
}

#[test]
fn hover_names_the_element() {
    let (mut client, _, uses) = workspace();
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&uses, 2, 15),
        work_done_progress_params: Default::default(),
    });
    let hover = hover.expect("hover");
    let lsp_types::HoverContents::Markup(m) = hover.contents else {
        panic!("expected markup");
    };
    assert!(
        m.value.contains("Defs::Wheel") && m.value.contains("PartDefinition"),
        "{}",
        m.value
    );
    client.shutdown();
}

#[test]
fn hover_shows_the_resolved_value_at_a_reference_site() {
    let mut client = Client::start();
    let u = uri("v.sysml");
    client.open(
        &u,
        "part def P {\n    attribute a = 5;\n    attribute b = a + 2;\n    assert constraint c { b > 1 }\n}\n",
    );
    // Hovering the `b` reference inside the constraint shows what it
    // resolved to (7), not just its name and metaclass.
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 3, 26),
        work_done_progress_params: Default::default(),
    });
    let hover = hover.expect("hover");
    let lsp_types::HoverContents::Markup(m) = hover.contents else {
        panic!("expected markup");
    };
    assert!(
        m.value.contains("P::b") && m.value.contains("= `7`"),
        "{}",
        m.value
    );
    client.shutdown();
}

/// Hovering a chain member evaluates through the receiver: the card
/// answers for the instance the cursor is on — redefinitions under the
/// receiver shadow the inherited values — not for the declaration in
/// its own scope.
#[test]
fn hover_chain_member_uses_the_receiver_context() {
    let mut client = Client::start();
    let u = uri("chain.sysml");
    client.open(
        &u,
        "package T {\n    part def Vehicle {\n        attribute baseMass = 1000;\n        attribute total = baseMass + 100;\n    }\n    part car : Vehicle { attribute :>> baseMass = 1200; }\n    part garage { part slot : Vehicle { attribute :>> baseMass = 2000; } }\n    attribute carTotal = car.total;\n    attribute deep = garage.slot.total;\n}\n",
    );
    let hover_value = |client: &mut Client, line: u32, character: u32| {
        let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: Client::pos_params(&u, line, character),
            work_done_progress_params: Default::default(),
        });
        let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
            panic!("expected markup");
        };
        m.value
    };
    // `total` in `car.total`: 1200 + 100 through the redefinition, not
    // the declaration-scope 1100.
    let card = hover_value(&mut client, 7, 30);
    assert!(
        card.contains("T::Vehicle::total") && card.contains("= `1300`"),
        "{card}"
    );
    // A longer chain establishes context stepwise: `garage.slot.total`.
    let card = hover_value(&mut client, 8, 34);
    assert!(card.contains("= `2100`"), "{card}");
    client.shutdown();
}

/// A calc def's hover leads with a function signature the way a
/// TypeScript hover does — a fenced source block, `in` implied, local
/// types by simple name, foreign types qualified, the return typing
/// after `→` — at the declaration and at call sites alike.
#[test]
fn hover_shows_calc_def_signature() {
    let mut client = Client::start();
    let u = uri("c.sysml");
    client.open(
        &u,
        "package Lib {\n    attribute def Speed;\n}\npackage P {\n    attribute def Force;\n    attribute def Torque;\n    calc def T { in force : Force; in v : Lib::Speed; return t : Torque = force * v; }\n    part sys {\n        attribute m = T(force = 2, v = 3);\n    }\n}\n",
    );
    let hover_at = |client: &mut Client, u: &Uri, line: u32, character: u32| -> String {
        let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: Client::pos_params(u, line, character),
            work_done_progress_params: Default::default(),
        });
        let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
            panic!("expected markup");
        };
        m.value
    };
    let sig = "```sysml-signature\nT(force: Force, v: Lib::Speed) → Torque\n```";
    // At the declaration…
    let text = hover_at(&mut client, &u, 6, 13);
    assert!(text.contains("P::T"), "{text}");
    assert!(text.contains(sig), "{text}");
    // …and at the call site, where the reference resolves to the def.
    let text = hover_at(&mut client, &u, 8, 22);
    assert!(text.contains(sig), "{text}");
    // An untyped-parameter calc still signs with what it has.
    let u2 = uri("c2.sysml");
    client.open(&u2, "calc def Double { in x; x * 2 }\n");
    let text = hover_at(&mut client, &u2, 0, 10);
    assert!(
        text.contains("```sysml-signature\nDouble(x)\n```"),
        "{text}"
    );
    client.shutdown();
}

/// Parameters declared by subsetting/redefinition (`in g0 :>
/// ISQ::acceleration` — the common quantity-parameter spelling) type
/// the signature by their subsetted feature; same for the return side.
#[test]
fn hover_signature_types_via_subsetting() {
    let mut client = Client::start();
    let u = uri("s.sysml");
    client.open(
        &u,
        "package Lib {\n    attribute q;\n}\npackage P {\n    attribute def Mass;\n    attribute isp : Mass;\n    attribute speed : Mass;\n    calc def C { in a :> isp; in b :> Lib::q; return r :> speed = a; }\n}\n",
    );
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 7, 13),
        work_done_progress_params: Default::default(),
    });
    let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
        panic!("expected markup");
    };
    assert!(
        m.value
            .contains("```sysml-signature\nC(a: isp, b: Lib::q) → speed\n```"),
        "{}",
        m.value
    );
    client.shutdown();
}

/// Every callable an invocation expression can name gets the
/// signature: a package-level calc *usage* (`calc <ln>
/// naturalLogarithm { … }`) and a KerML `function` alike.
#[test]
fn hover_signature_covers_calc_usages_and_kerml_functions() {
    let mut client = Client::start();
    // The Apollo shape: a named calc usage invoked as a function.
    let u = uri("u.sysml");
    client.open(
        &u,
        "package P {\n    attribute def D;\n    calc <n> nat { in x : D; return : D; }\n    part s { attribute v = nat(x = 1); }\n}\n",
    );
    let hover_at = |client: &mut Client, u: &Uri, line: u32, character: u32| -> String {
        let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: Client::pos_params(u, line, character),
            work_done_progress_params: Default::default(),
        });
        let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
            panic!("expected markup");
        };
        m.value
    };
    let sig = "```sysml-signature\nnat(x: D) → D\n```";
    let text = hover_at(&mut client, &u, 2, 14);
    assert!(text.contains("CalculationUsage"), "{text}");
    assert!(text.contains(sig), "{text}");
    // …and at the invocation.
    let text = hover_at(&mut client, &u, 3, 27);
    assert!(text.contains(sig), "{text}");
    // KerML: `function` (typed return, unnamed).
    let k = uri("f.kerml");
    client.open(
        &k,
        "package K {\n    datatype R;\n    function Scale { in x : R; return : R; }\n}\n",
    );
    let text = hover_at(&mut client, &k, 2, 14);
    assert!(text.contains("Function"), "{text}");
    assert!(
        text.contains("```sysml-signature\nScale(x: R) → R\n```"),
        "{text}"
    );
    client.shutdown();
}

/// Constraint and action definitions read as callables too: their
/// hovers carry the same signature block — with `out`/`inout`
/// directions spelled (only `in` is implied).
#[test]
fn hover_shows_constraint_and_action_def_signatures() {
    let mut client = Client::start();
    let u = uri("ca.sysml");
    client.open(
        &u,
        "package P {\n    attribute def Mass;\n    attribute def Flag;\n    constraint def NonNeg { in m : Mass; m >= 0 }\n    action def Move { in dist : Mass; out done : Flag; }\n}\n",
    );
    let hover_at = |line: u32, character: u32, client: &mut Client| -> String {
        let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: Client::pos_params(&u, line, character),
            work_done_progress_params: Default::default(),
        });
        let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
            panic!("expected markup");
        };
        m.value
    };
    let text = hover_at(3, 20, &mut client);
    assert!(
        text.contains("```sysml-signature\nNonNeg(m: Mass)\n```"),
        "{text}"
    );
    let text = hover_at(4, 16, &mut client);
    assert!(
        text.contains("```sysml-signature\nMove(dist: Mass, out done: Flag)\n```"),
        "{text}"
    );
    client.shutdown();
}

#[test]
fn hover_shows_documentation_bodies() {
    let mut client = Client::start();
    let u = uri("d.sysml");
    client.open(
        &u,
        "package P {\n    doc /* The package purpose. */\n    enum def Mode { fast; slow; }\n    part sys {\n        doc /* A system. */\n        attribute m : Mode = Mode::fast;\n    }\n}\n",
    );
    let hover_at = |client: &mut Client, line: u32, character: u32| -> String {
        let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
            text_document_position_params: Client::pos_params(&u, line, character),
            work_done_progress_params: Default::default(),
        });
        let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
            panic!("expected markup");
        };
        m.value
    };
    // The package's own doc joins its card…
    let text = hover_at(&mut client, 0, 8);
    assert!(text.contains("The package purpose."), "{text}");
    // …and a nested element carries its own doc, not its ancestor's.
    let text = hover_at(&mut client, 3, 9);
    assert!(text.contains("A system."), "{text}");
    assert!(!text.contains("package purpose"), "{text}");
    // An enum-typed default renders by literal name, not `<element>`.
    let text = hover_at(&mut client, 5, 18);
    assert!(text.contains("= `fast`"), "{text}");
    client.shutdown();
}

/// A named doc (`doc Description /* … */`) renders its name as a
/// Markdown heading over the body.
#[test]
fn hover_renders_named_doc_as_heading() {
    let mut client = Client::start();
    let u = uri("dh.sysml");
    client.open(
        &u,
        "package P {\n    part def Engine {\n        doc Description /* Converts fuel to torque. */\n        doc /* Unnamed note. */\n    }\n}\n",
    );
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 1, 14),
        work_done_progress_params: Default::default(),
    });
    let lsp_types::HoverContents::Markup(m) = hover.expect("hover").contents else {
        panic!("expected markup");
    };
    assert!(
        m.value
            .contains("### Description\nConverts fuel to torque."),
        "{}",
        m.value
    );
    assert!(m.value.contains("Unnamed note."), "{}", m.value);
    assert!(!m.value.contains("### Unnamed"), "{}", m.value);
    client.shutdown();
}

#[test]
fn rename_rewrites_both_files() {
    let (mut client, defs, uses) = workspace();
    let edit: Option<WorkspaceEdit> = client
        .request::<Rename>(RenameParams {
            text_document_position: Client::pos_params(&uses, 2, 15),
            new_name: "Roue".to_string(),
            work_done_progress_params: Default::default(),
        })
        .expect("rename should succeed");
    let changes = edit.unwrap().changes.expect("changes");
    let new_defs = &changes[&defs][0].new_text;
    let new_uses = &changes[&uses][0].new_text;
    assert!(new_defs.contains("part def Roue"), "{new_defs}");
    assert_eq!(new_uses.matches("Roue").count(), 2, "{new_uses}");
    assert!(!new_uses.contains("Wheel"), "{new_uses}");
    // Everything untouched stays byte-identical (splice-minimal engine
    // under a whole-doc edit wrapper).
    assert!(new_defs.contains("attribute radius : Real;"));
    client.shutdown();
}

#[test]
fn rename_shadow_capture_rejects() {
    let client = Client::start();
    let m = uri("m.sysml");
    // Renaming `Inner` to `Outer` would capture: `x : Outer` inside P
    // would resolve to the renamed sibling instead of the outer def.
    client.open(
        &m,
        "part def Outer;\npackage P {\n    part def Inner;\n    part x : Outer;\n}\n",
    );
    let mut c = client;
    let err = c
        .request::<Rename>(RenameParams {
            text_document_position: Client::pos_params(&m, 2, 14),
            new_name: "Outer".to_string(),
            work_done_progress_params: Default::default(),
        })
        .expect_err("shadow capture must reject");
    assert!(
        err.contains("would resolve to"),
        "expected the semantic-identity refusal: {err}"
    );
    // The document is untouched — a follow-up definition still answers.
    let resp = c.request_ok::<GotoDefinition>(GotoDefinitionParams {
        text_document_position_params: Client::pos_params(&m, 3, 14),
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    });
    assert!(matches!(resp, Some(GotoDefinitionResponse::Scalar(l)) if l.range.start.line == 0));
    c.shutdown();
}

/// Definition must follow import-introduced bindings into units that
/// are on disk under the workspace root but were never opened — the
/// editor shape where one file of a multi-file model is being read.
/// All three reference spellings jump: a name through a direct
/// membership import, a name through a wildcard import, and a
/// qualified reference.
#[test]
fn definition_reaches_unopened_workspace_units() {
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-lsp-nav-root-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let defs = "package Defs {\n    part def Wheel {\n        attribute radius : Real;\n    }\n    part def Axle;\n}\n";
    std::fs::write(dir.join("defs.sysml"), defs).unwrap();
    let defs_uri = Uri::from_str(&format!(
        "file://{}",
        dir.join("defs.sysml")
            .display()
            .to_string()
            .replace(' ', "%20")
    ))
    .unwrap();

    let mut client = Client::start_with_root(Some(&dir));
    let uses = uri("uses.sysml");
    client.open(
        &uses,
        "package Uses {\n    private import Defs::Wheel;\n    private import Defs::*;\n    part w1 : Wheel;\n    part a1 : Axle;\n    part q1 : Defs::Axle;\n}\n",
    );

    let mut definition = |line: u32, character: u32| -> Location {
        let resp = client.request_ok::<GotoDefinition>(GotoDefinitionParams {
            text_document_position_params: Client::pos_params(&uses, line, character),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
        let Some(GotoDefinitionResponse::Scalar(loc)) = resp else {
            panic!("expected a definition at {line}:{character}: {resp:?}");
        };
        loc
    };

    // `Wheel` in `part w1 : Wheel;` — through the direct import.
    let loc = definition(3, 15);
    assert_eq!(loc.uri, defs_uri);
    assert_eq!(
        loc.range.start,
        Position {
            line: 1,
            character: 13
        }
    );
    // `Axle` in `part a1 : Axle;` — through the wildcard import.
    let loc = definition(4, 15);
    assert_eq!(loc.uri, defs_uri);
    assert_eq!(
        loc.range.start,
        Position {
            line: 4,
            character: 13
        }
    );
    // `Axle` in `part q1 : Defs::Axle;` — a qualified reference.
    let loc = definition(5, 21);
    assert_eq!(loc.uri, defs_uri);
    assert_eq!(
        loc.range.start,
        Position {
            line: 4,
            character: 13
        }
    );
    // The qualifier segment `Defs` jumps to the package itself.
    let loc = definition(5, 15);
    assert_eq!(loc.uri, defs_uri);
    assert_eq!(
        loc.range.start,
        Position {
            line: 0,
            character: 8
        }
    );
    // `Wheel` inside the import statement jumps too.
    let loc = definition(1, 26);
    assert_eq!(loc.uri, defs_uri);
    assert_eq!(
        loc.range.start,
        Position {
            line: 1,
            character: 13
        }
    );
    client.shutdown();
}

#[test]
fn workspace_symbols_filter_across_files() {
    let (mut client, defs, uses) = workspace();
    let resp = client.request_ok::<WorkspaceSymbolRequest>(WorkspaceSymbolParams {
        query: "w".to_string(),
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    });
    let Some(lsp_types::WorkspaceSymbolResponse::Flat(syms)) = resp else {
        panic!("expected flat symbols: {resp:?}");
    };
    let names: Vec<&str> = syms.iter().map(|s| s.name.as_str()).collect();
    assert!(names.contains(&"Wheel"), "{names:?}");
    assert!(names.contains(&"w1") && names.contains(&"w2"), "{names:?}");
    assert!(syms.iter().any(|s| s.location.uri == defs));
    assert!(syms.iter().any(|s| s.location.uri == uses));
    client.shutdown();
}

/// A bare usage inside a typed metadata record carries no doc of its
/// own — the vocabulary's documentation lives on the defining
/// attribute. Hover inherits it (attributed), and the record head
/// inherits its typing's doc the same way.
#[test]
fn hover_inherits_metadata_vocabulary_docs() {
    let mut client = Client::start();
    let u = uri("meta-docs.sysml");
    client.open(
        &u,
        "library package Vocab {\n\
         \tmetadata def Record {\n\
         \t\tdoc /* One bookkeeping record. */\n\
         \t\tattribute rowDigest {\n\
         \t\t\tdoc /* sha256 identity of the source row. */\n\
         \t\t}\n\
         \t}\n\
         }\n\
         package P {\n\
         \tmetadata r : Vocab::Record {\n\
         \t\trowDigest = \"sha256:abc\";\n\
         \t}\n\
         }\n",
    );
    // Hover the record's own `rowDigest` assignment (line 10, inside
    // the name) — the def attribute's doc appears, attributed.
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 10, 4),
        work_done_progress_params: Default::default(),
    });
    let hover = hover.expect("hover");
    let lsp_types::HoverContents::Markup(m) = hover.contents else {
        panic!("expected markup");
    };
    assert!(
        m.value.contains("sha256 identity of the source row"),
        "inherited attribute doc missing: {}",
        m.value
    );
    assert!(
        m.value.contains("Vocab::Record::rowDigest"),
        "attribution missing: {}",
        m.value
    );
    // Hover the record usage's name — the typing's doc appears.
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 9, 10),
        work_done_progress_params: Default::default(),
    });
    let hover = hover.expect("hover");
    let lsp_types::HoverContents::Markup(m) = hover.contents else {
        panic!("expected markup");
    };
    assert!(
        m.value.contains("One bookkeeping record"),
        "inherited typing doc missing: {}",
        m.value
    );
    client.shutdown();
}

/// The inherited docs survive the library boundary: the documented
/// vocabulary is a *library* unit (excluded from the user-unit doc
/// sweep), the record a user document — the regression that first
/// surfaced with generated provenance stores hovering bare.
#[test]
fn hover_inherits_library_vocabulary_docs() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-lsp-nav-libdocs-test-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("Vocab.sysml"),
        "library package Vocab {\n\
         \tmetadata def Record {\n\
         \t\tdoc /* One bookkeeping record. */\n\
         \t\tattribute rowDigest {\n\
         \t\t\tdoc /* sha256 identity of the source row. */\n\
         \t\t}\n\
         \t}\n\
         }\n",
    )
    .unwrap();
    let mut client = Client::start_with_library(dir);
    let u = uri("store.sysml");
    client.open(
        &u,
        "package P {\n\
         \t@r : Vocab::Record {\n\
         \t\trowDigest = \"sha256:abc\";\n\
         \t}\n\
         }\n",
    );
    let hover: Option<Hover> = client.request_ok::<HoverRequest>(HoverParams {
        text_document_position_params: Client::pos_params(&u, 2, 4),
        work_done_progress_params: Default::default(),
    });
    let hover = hover.expect("hover");
    let lsp_types::HoverContents::Markup(m) = hover.contents else {
        panic!("expected markup");
    };
    assert!(
        m.value.contains("sha256 identity of the source row"),
        "library-inherited attribute doc missing: {}",
        m.value
    );
    assert!(
        m.value.contains("Vocab::Record::rowDigest"),
        "attribution missing: {}",
        m.value
    );
    client.shutdown();
}

/// A standard-library directory that cannot be read leaves hover,
/// definition, references and rename with nothing to answer from. The
/// empty answers used to be all the client ever heard; the reason now
/// reaches it too, once, before the answer.
#[test]
fn an_unreadable_library_reaches_the_client() {
    use lsp_types::request::Request as _;
    let missing = std::env::temp_dir().join(format!(
        "sysmlv2-lsp-no-such-library-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&missing);
    let client = Client::start_with_library(missing);
    let u = uri("defs.sysml");
    client.open(&u, DEFS);

    let id = RequestId::from(99);
    client
        .conn
        .sender
        .send(Message::Request(Request::new(
            id.clone(),
            HoverRequest::METHOD.to_string(),
            HoverParams {
                text_document_position_params: Client::pos_params(&u, 1, 14),
                work_done_progress_params: Default::default(),
            },
        )))
        .unwrap();
    let mut shown: Option<lsp_types::ShowMessageParams> = None;
    loop {
        match client.conn.receiver.recv().unwrap() {
            Message::Notification(n) if n.method == "window/showMessage" => {
                shown = Some(serde_json::from_value(n.params).unwrap());
            }
            Message::Response(r) if r.id == id => break,
            _ => continue,
        }
    }
    let shown = shown.expect("the library failure reaches the client");
    assert!(
        shown.message.contains("standard library could not be read"),
        "{shown:?}"
    );
    client.shutdown();
}
