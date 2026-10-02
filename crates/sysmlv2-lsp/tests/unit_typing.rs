#![allow(clippy::mutable_key_type)] // lsp-types Uri map keys

//! Completions against the standard library. Typing (the
//! `inferUnitTypes` behavior): accepting a unit completion inside an
//! untyped attribute's quantity bracket also declares the type the unit
//! determines — exactly one, spelled shortest-that-resolves — and the
//! initialization option turns it off. Placement: multi-word unit names
//! are offered inside a bracket and nowhere else. Names: the library's
//! own imports and its operator functions are never offered as bare
//! names.

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
    match completion(client, uri, line, character) {
        Some(CompletionResponse::Array(items)) => items,
        Some(CompletionResponse::List(list)) => list.items,
        None => panic!("expected items"),
    }
}

fn completion(
    client: &mut Client,
    uri: &Uri,
    line: u32,
    character: u32,
) -> Option<CompletionResponse> {
    client.request_ok::<Completion>(CompletionParams {
        text_document_position: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: Position { line, character },
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
        context: None,
    })
}

/// Multi-word unit names (`'atomic mass unit'`) complete inside a
/// quantity bracket and nowhere else: at a type position they would be
/// noise, some 380 labels in every response.
#[test]
fn multiword_unit_names_only_inside_brackets() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("m.sysml");
    client.open(
        &u,
        "package M {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute x : \n    attribute y = 5 [\n}\n",
    );
    // After `attribute x : ` on line 3.
    let typed = complete(&mut client, &u, 3, 18);
    assert!(
        typed.iter().any(|i| i.label == "MassValue"),
        "types offered"
    );
    let spaced: Vec<&str> = typed
        .iter()
        .map(|i| i.label.as_str())
        .filter(|l| l.chars().any(char::is_whitespace))
        .collect();
    assert!(spaced.is_empty(), "multi-word labels at a type: {spaced:?}");
    // After `attribute y = 5 [` on line 4.
    let bracket = complete(&mut client, &u, 4, 21);
    let labels: Vec<&str> = bracket.iter().map(|i| i.label.as_str()).collect();
    assert!(
        labels.contains(&"atomic mass unit"),
        "long name in a bracket"
    );
    assert!(labels.contains(&"u"), "its short symbol too");
    client.shutdown();
}

/// The library's own imports (`private import SI::m;` in a shape
/// package) declare nothing: no label is an import path, an import is
/// no member of the importing package, and a document's own
/// `import ISQ::*` does not stand in for the package it names.
#[test]
fn library_imports_are_not_names() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("n.sysml");
    client.open(
        &u,
        "package N {\n    private import ISQ::*;\n    attribute x : \n    attribute y : ISQ::\n}\n",
    );
    // After `attribute x : ` on line 2.
    let flat = complete(&mut client, &u, 2, 18);
    let paths: Vec<&str> = flat
        .iter()
        .map(|i| i.label.as_str())
        .filter(|l| l.contains("::"))
        .collect();
    assert!(paths.is_empty(), "import paths offered as names: {paths:?}");
    let isq = flat.iter().find(|i| i.label == "ISQ").expect("ISQ offered");
    assert_eq!(isq.detail.as_deref(), Some("standard library"));
    // After `attribute y : ISQ::` on line 3: members of ISQ, and none
    // of the packages it imports.
    let members = complete(&mut client, &u, 3, 23);
    let labels: Vec<&str> = members.iter().map(|i| i.label.as_str()).collect();
    assert!(labels.contains(&"TemperatureDifferenceValue"), "{labels:?}");
    for import in [
        "ScalarValues::Real",
        "Quantities",
        "ISQBase",
        "ISQMechanics",
    ] {
        assert!(
            !labels.contains(&import),
            "import `{import}` listed as a member"
        );
    }
    client.shutdown();
}

/// Operator functions are written as operators, not names: the flat
/// list offers none of the library's (`'+'`, `'['`, `'..'`, `'not'`),
/// while functions with plain names stay, and the units and aliases
/// spelled with symbols (`'°C'`, `'m/s²'`) are no operators: a unit
/// bracket offers them, though an operand outside one does not.
#[test]
fn library_operator_functions_are_not_names() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("o.sysml");
    client.open(
        &u,
        "package O {\n    attribute x = \n    attribute y = 5 [\n}\n",
    );
    // After `attribute x = ` on line 1.
    let flat = complete(&mut client, &u, 1, 18);
    // Names only: the word operators are keywords too.
    let labels: Vec<&str> = flat
        .iter()
        .filter(|i| i.kind != Some(lsp_types::CompletionItemKind::KEYWORD))
        .map(|i| i.label.as_str())
        .collect();
    for op in [
        "!=", "!==", "#", "%", "&", "*", "**", "+", ",", "-", ".", "..", "/", "<", "<=", "==",
        "===", ">", ">=", "??", "@", "@@", "[", "^", "|", "~", "all", "and", "as", "hastype", "if",
        "implies", "istype", "meta", "not", "or", "xor",
    ] {
        assert!(!labels.contains(&op), "operator `{op}` offered");
    }
    assert!(labels.contains(&"sqrt"), "`sqrt` missing");
    // After `attribute y = 5 [` on line 2.
    let bracket = complete(&mut client, &u, 2, 21);
    let labels: Vec<&str> = bracket.iter().map(|i| i.label.as_str()).collect();
    for name in ["°C", "m/s", "m/s²"] {
        assert!(labels.contains(&name), "`{name}` missing");
    }
    client.shutdown();
}

/// The labels in the order a client lists them: by sort text.
fn listed(mut items: Vec<lsp_types::CompletionItem>) -> Vec<String> {
    items.sort_by(|a, b| a.sort_text.cmp(&b.sort_text));
    items.into_iter().map(|i| i.label).collect()
}

/// In a quantity's unit bracket the units of the quantity the value is
/// declared as come first, short symbols ahead of long names, and the
/// list holds units only: narrowing a duration to `mi` meets the minute
/// before the mile, a mass narrowed to `k` meets the kilogram before
/// the kelvin.
#[test]
fn unit_brackets_offer_the_declared_quantitys_units_first() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("d.sysml");
    client.open(
        &u,
        "package D {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute g : ISQ::DurationValue = 5.5 [\n}\n",
    );
    // After `= 5.5 [` on line 3.
    let labels = listed(complete(&mut client, &u, 3, 44));
    assert_eq!(
        labels[..8],
        ["s", "d", "h", "min", "second", "day", "hour", "minute"],
        "{labels:?}"
    );
    let mi: Vec<&str> = labels
        .iter()
        .map(String::as_str)
        .filter(|l| l.starts_with("mi"))
        .collect();
    assert_eq!(mi[..2], ["min", "minute"], "{mi:?}");
    assert!(mi.contains(&"mi"), "the mile stays reachable: {mi:?}");
    for other in ["part", "attribute", "MassValue", "DurationValue"] {
        assert!(!labels.iter().any(|l| l == other), "{other} offered");
    }
    let u = uri("m.sysml");
    client.open(
        &u,
        "package M {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute m : MassValue = 5 [k\n}\n",
    );
    // After `= 5 [k` on line 3.
    let labels = listed(complete(&mut client, &u, 3, 34));
    let k: Vec<&str> = labels
        .iter()
        .map(String::as_str)
        .filter(|l| l.to_lowercase().starts_with('k'))
        .collect();
    assert_eq!(k[..2], ["kg", "kilogram"], "{k:?}");
    client.shutdown();
}

/// A redefinition's value measures the quantity of the feature it
/// redefines; a multiplicity offers nothing.
#[test]
fn redefinitions_take_their_features_units_and_multiplicities_none() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("v.sysml");
    client.open(
        &u,
        "package V {\n    private import ISQ::*;\n    private import SI::*;\n    \
         part def Vehicle { attribute mass : MassValue; }\n    part v : Vehicle {\n        \
         attribute :>> mass = 1500 [\n    }\n    part def Wheel;\n    part wheels : Wheel [\n}\n",
    );
    // After `= 1500 [` on line 5.
    let labels = listed(complete(&mut client, &u, 5, 35));
    let at = |label: &str| {
        labels
            .iter()
            .position(|l| l == label)
            .unwrap_or_else(|| panic!("{label} not offered: {labels:?}"))
    };
    assert!(at("kg") < at("s") && at("kg") < at("K"), "{labels:?}");
    assert!(at("kilogram") < at("s"), "{labels:?}");
    // After `part wheels : Wheel [` on line 8.
    let items = complete(&mut client, &u, 8, 25);
    assert!(items.is_empty(), "{:?}", listed(items));
    client.shutdown();
}

/// The declared quantity also comes from the parameter a directed
/// usage redefines by name and from a type the model specializes from a
/// quantity; a factor of a compound unit is not ordered by it.
#[test]
fn parameters_user_types_and_factors() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("p.sysml");
    client.open(
        &u,
        "package P {\n    private import ISQ::*;\n    private import SI::*;\n    \
         constraint def MassLimit { in mass : MassValue; in limit : MassValue; mass <= limit }\n    \
         attribute def Speed :> SpeedValue;\n    part def V {\n        \
         assert constraint c : MassLimit { in limit = 2000 [kg]; }\n        \
         attribute s : Speed = 5 [m/s];\n        \
         attribute f : SpeedValue = 5 [m*s];\n    }\n}\n",
    );
    let at = |labels: &[String], label: &str| {
        labels
            .iter()
            .position(|l| l == label)
            .unwrap_or_else(|| panic!("{label} not offered: {labels:?}"))
    };
    // After `in limit = 2000 [` on line 6: mass first.
    let labels = listed(complete(&mut client, &u, 6, 59));
    assert!(at(&labels, "kg") < at(&labels, "m"), "{labels:?}");
    // After `s : Speed = 5 [` on line 7: speed first.
    let labels = listed(complete(&mut client, &u, 7, 33));
    assert!(at(&labels, "m/s") < at(&labels, "g"), "{labels:?}");
    // After `[m*` on line 8: a factor, in the library's order.
    let labels = listed(complete(&mut client, &u, 8, 40));
    assert!(at(&labels, "g") < at(&labels, "m/s"), "{labels:?}");
    client.shutdown();
}

/// Where the bracket annotates no declaration's whole value, the
/// quantity comes from its context: the left operand of a comparison or
/// a sum it is the right operand of — a feature, or a value carrying a
/// unit — or the parameter an argument binds, by its position among the
/// inputs or by name, of a calculation definition, one it specializes, or
/// a usage it types.
/// A factor's quantity is not the product's: it takes the list a
/// bracket without a quantity takes.
#[test]
fn unit_brackets_take_the_quantity_of_their_context() {
    let mut client = Client::start_with(InitializeParams::default());
    let prelude = "package K {\n    private import ISQ::*;\n    private import SI::*;\n    \
                   calc def KineticEnergy { in m : MassValue; in v : SpeedValue; return : EnergyValue; }\n    \
                   calc def KE2 :> KineticEnergy; calc def KE3 :> KineticEnergy { in speed redefines v; } \
                   calc def KE5 :> KineticEnergy { in mass : MassValue; } \
                   calc def KE8 :> KineticEnergy { in :>> m; } \
                   calc def Mixed { out o : EnergyValue; in m : MassValue; in v : SpeedValue; }\n    \
                   part def Vehicle {\n        attribute mass : MassValue;\n        \
                   calc ke : KineticEnergy;\n        calc ke2 : KE2;\n        ";
    let labels = |client: &mut Client, i: usize, statement: &str| {
        let u = uri(&format!("c{i}.sysml"));
        client.open(&u, &format!("{prelude}{statement}\n    }}\n}}\n"));
        // After the statement on line 9.
        let at = u32::try_from(8 + statement.len()).unwrap();
        listed(complete(client, &u, 9, at))
    };
    let at = |labels: &[String], label: &str| {
        labels
            .iter()
            .position(|l| l == label)
            .unwrap_or_else(|| panic!("{label} not offered: {labels:?}"))
    };
    for (i, (statement, first, then)) in [
        ("assert constraint { mass <= 1500 [", "kg", "m"),
        ("assert constraint { mass <= -1500 [", "kg", "m"),
        ("attribute e = KineticEnergy(1500 [", "kg", "m"),
        ("attribute e = KineticEnergy(1500 [kg], 20 [", "m/s", "g"),
        ("attribute e = KineticEnergy(v = 20 [", "m/s", "g"),
        ("attribute e = ke(1500 [", "kg", "m"),
        ("attribute e = KE2(1500 [", "kg", "m"),
        ("attribute e = KE2(v = 20 [", "m/s", "g"),
        ("attribute e = ke2(1500 [kg], 20 [", "m/s", "g"),
        // Its own first, then the inherited, but for what they redefine:
        // explicitly, and by position.
        ("attribute e = KE3(1500 [", "m/s", "g"),
        ("attribute e = KE5(1500 [kg], 20 [", "m/s", "g"),
        // Only redefining, it measures what it redefines.
        ("attribute e = KE8(1500 [", "kg", "m"),
        // Arguments bind inputs: the output declared first takes none.
        ("attribute e = Mixed(1500 [", "kg", "J"),
        ("attribute e = Mixed(1500 [kg], 20 [", "m/s", "kg"),
        ("attribute w = 1200 [kg] + 300 [", "kg", "m"),
    ]
    .into_iter()
    .enumerate()
    {
        let labels = labels(&mut client, i, statement);
        let head = &labels[..labels.len().min(12)];
        assert!(
            at(&labels, first) < at(&labels, then),
            "{statement}: {head:?}"
        );
    }
    let plain = labels(&mut client, 100, "attribute x = 1500 [");
    for (i, statement) in [
        "assert constraint { 2 * mass <= 1500 [",
        "attribute p = mass * 2 [",
        // no parameter left to bind: the result is none
        "attribute e = KineticEnergy(1500 [kg], 20 [m/s], 3 [",
        "attribute e = KE5(1500 [kg], 20 [m/s], 3 [",
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(
            labels(&mut client, 200 + i, statement),
            plain,
            "{statement}"
        );
    }
    client.shutdown();
}

/// A KerML function specializing another binds each argument to one
/// parameter: its own take the place of the same-named ones it
/// inherits, so an argument past them binds none.
#[test]
fn a_kerml_functions_arguments_bind_its_parameters_once() {
    let mut client = Client::start_with(InitializeParams::default());
    let labels = |client: &mut Client, name: &str, statement: &str| {
        let u = uri(name);
        client.open(
            &u,
            &format!(
                "package F {{\n    private import ISQ::*;\n    private import SI::*;\n    \
                 function Energy {{ in m : MassValue; in v : SpeedValue; return : EnergyValue; }}\n    \
                 function Again specializes Energy {{ in m : MassValue; in v : SpeedValue; }}\n    \
                 {statement}\n}}\n"
            ),
        );
        // After the statement on line 5.
        let at = u32::try_from(4 + statement.len()).unwrap();
        listed(complete(client, &u, 5, at))
    };
    let at = |labels: &[String], label: &str| {
        labels
            .iter()
            .position(|l| l == label)
            .unwrap_or_else(|| panic!("{label} not offered: {labels:?}"))
    };
    let second = labels(
        &mut client,
        "second.kerml",
        "feature e = Again(1500 [kg], 20 [",
    );
    assert!(at(&second, "m/s") < at(&second, "g"), "{:?}", &second[..8]);
    let plain = labels(&mut client, "plain.kerml", "feature x = 1500 [");
    assert_eq!(
        labels(
            &mut client,
            "third.kerml",
            "feature e = Again(1500 [kg], 20 [m/s], 3 ["
        ),
        plain
    );
    client.shutdown();
}

/// A reading on a scale — a time instant — is compared with or moved by
/// a difference, which the scale's unit measures: the scale's own
/// references (`UTC`) do not lead the list, and a unit's symbol typed
/// whole keeps its whole match (`d` is the day, not the decibel's `dB`).
#[test]
fn a_scale_reading_names_no_quantity_for_its_difference() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("t.sysml");
    client.open(
        &u,
        "package T {\n    private import ISQ::*;\n    private import SI::*;\n    \
         private import Time::*;\n    part def P {\n        attribute t1 : TimeInstantValue;\n        \
         attribute t2 = t1 + 5 [\n    }\n}\n",
    );
    // After `t1 + 5 [` on line 6.
    let items = complete(&mut client, &u, 6, 31);
    let d = items.iter().find(|i| i.label == "d").expect("`d` offered");
    assert_eq!(d.filter_text, None, "{d:?}");
    let labels = listed(items);
    let at = |label: &str| labels.iter().position(|l| l == label).unwrap_or(usize::MAX);
    assert!(at("s") < at("UTC"), "{:?}", &labels[..8]);
    // A reading written on the scale itself.
    let u = uri("t2.sysml");
    client.open(
        &u,
        "package T {\n    private import ISQ::*;\n    private import SI::*;\n    \
         private import Time::*;\n    attribute t = 5 [UTC] + 3 [\n}\n",
    );
    // After `5 [UTC] + 3 [` on line 4.
    let labels = listed(complete(&mut client, &u, 4, 31));
    let at = |label: &str| labels.iter().position(|l| l == label).unwrap_or(usize::MAX);
    assert!(at("s") < at("UTC"), "{:?}", &labels[..8]);
    client.shutdown();
}

/// A unit an operand carries that is typed by one of the library's
/// general references alone — any simple unit — names no quantity: the
/// units of that kind do not all fit it, and the newton's `N`, a derived
/// unit, keeps its place and its whole match.
#[test]
fn a_unit_typed_by_a_general_reference_names_no_quantity() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("g.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         private import MeasurementReferences::*;\n    attribute <gp> genericUnit : SimpleUnit;\n    \
         attribute x = 5 [gp] + 3 [\n}\n",
    );
    // After `5 [gp] + 3 [` on line 5.
    let items = complete(&mut client, &u, 5, 30);
    let n = items.iter().find(|i| i.label == "N").expect("`N` offered");
    assert_eq!(n.filter_text, None, "{n:?}");
    let labels = listed(items);
    let at = |label: &str| labels.iter().position(|l| l == label).unwrap_or(usize::MAX);
    assert!(at("N") < at("nm"), "{:?}", &labels[..8]);
    client.shutdown();
}

/// A unit fits the declared quantity when it is typed by the quantity's
/// measurement reference, even where no dimension can be computed for
/// it: a unit of a quantity the model defines on a base quantity of its
/// own, a vector's coordinate frame — and so does the quantity of a unit
/// an operand carries.
#[test]
fn units_typed_by_the_quantitys_reference_fit_it() {
    let mut client = Client::start_with(InitializeParams::default());
    let currency = |i: usize, value: &str| {
        format!(
            "package C{i} {{\n    private import ISQ::*;\n    private import SI::*;\n    \
             private import Quantities::*;\n    private import MeasurementReferences::*;\n    \
             attribute def CurrencyUnit :> SimpleUnit {{\n        \
             private attribute pf : QuantityPowerFactor[1] {{ :>> quantity = Currency; :>> exponent = 1; }}\n        \
             attribute :>> quantityDimension {{ :>> quantityPowerFactors = pf; }}\n    }}\n    \
             attribute def CurrencyValue :> ScalarQuantityValue {{ attribute :>> num : Real; attribute :>> mRef : CurrencyUnit[1]; }}\n    \
             attribute Currency : CurrencyValue[1];\n    \
             attribute <km2> kilometreSquared : AreaUnit;\n    \
             attribute <'$'> dollar : CurrencyUnit;\n    \
             {value}\n}}\n"
        )
    };
    for (i, value) in [
        "attribute cost : CurrencyValue = 5 [",
        "attribute total = 5 ['$'] + 3 [",
    ]
    .into_iter()
    .enumerate()
    {
        let u = uri(&format!("c{i}.sysml"));
        client.open(&u, &currency(i, value));
        // After the value on line 13.
        let at = u32::try_from(4 + value.len()).unwrap();
        let labels = listed(complete(&mut client, &u, 13, at));
        assert_eq!(
            labels.first().map(String::as_str),
            Some("$"),
            "{value}: {labels:?}"
        );
    }
    let u = uri("v.sysml");
    client.open(
        &u,
        "package V {\n    private import ISQ::*;\n    private import ISQSpaceTime::*;\n    \
         attribute p : CartesianPosition3dVector = (1, 2, 3) [\n}\n",
    );
    // After `(1, 2, 3) [` on line 3.
    let labels = listed(complete(&mut client, &u, 3, 57));
    assert_eq!(
        labels.first().map(String::as_str),
        Some("universalCartesianSpatial3dCoordinateFrame"),
        "{labels:?}"
    );
    // A frame an operand carries: a library frame of its own kind, not
    // one of the general references.
    let u = uri("w.sysml");
    let value =
        "attribute p = (1, 2, 3) [universalCartesianSpatial3dCoordinateFrame] + (4, 5, 6) [";
    client.open(
        &u,
        &format!(
            "package W {{\n    private import ISQ::*;\n    private import ISQSpaceTime::*;\n    {value}\n}}\n"
        ),
    );
    // After the value on line 3.
    let at = u32::try_from(4 + value.len()).unwrap();
    let labels = listed(complete(&mut client, &u, 3, at));
    assert_eq!(
        labels.first().map(String::as_str),
        Some("universalCartesianSpatial3dCoordinateFrame"),
        "{:?}",
        &labels[..labels.len().min(8)]
    );
    client.shutdown();
}

/// A `doc` or a comment ahead of the declaration — it ends with no
/// `;`, so the statement's tokens start with it — does not hide the
/// declared quantity.
#[test]
fn a_comment_ahead_of_the_declaration_keeps_its_quantity() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("d.sysml");
    client.open(
        &u,
        "package D {\n    private import ISQ::*;\n    private import SI::*;\n    \
         part def V {\n        doc /* A vehicle. */\n        attribute m : MassValue = 5 [kg];\n    }\n    \
         part v : V {\n        comment c /* a note */\n        attribute redefines m = 7 [kg];\n    }\n}\n",
    );
    // Right after `= 5 [` on line 5, then `= 7 [` on line 9.
    for (line, character) in [(5, 37), (9, 35)] {
        let labels = listed(complete(&mut client, &u, line, character));
        let at = |label: &str| labels.iter().position(|l| l == label).unwrap_or(usize::MAX);
        assert!(at("kg") < at("m") && at("kg") < at("s"), "{labels:?}");
    }
    client.shutdown();
}

/// The untyped attribute a unit completion declares the type of is read
/// on the document's tokens: the words of a comment ahead of it do not
/// count, and the typing lands after the declared name.
#[test]
fn the_inferred_typing_lands_after_the_declared_name() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("n.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    part def P {\n        \
         doc /* the attribute of it */\n        attribute m = 5 [k\n    }\n}\n",
    );
    // After `= 5 [k` on line 5.
    let items = complete(&mut client, &u, 5, 26);
    let kg = items.iter().find(|i| i.label == "kg").expect("`kg` item");
    let typing = kg
        .additional_text_edits
        .iter()
        .flatten()
        .find(|e| e.new_text == " : MassValue")
        .unwrap_or_else(|| panic!("{:?}", kg.additional_text_edits));
    // Right after `attribute m`, not in the comment above.
    assert_eq!(
        typing.range.start,
        Position {
            line: 5,
            character: 19
        }
    );
    client.shutdown();
}

/// A qualifier offers what the namespace re-exports: `ISQ` publicly
/// imports its part packages (`ISQBase::*`, …), so `ISQ::MassValue` —
/// the conventional spelling — completes, and `SI`, which re-exports
/// `ISQ` and the unit prefixes, offers quantities and prefixes beside
/// its own units.
#[test]
fn qualifiers_offer_re_exported_members() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("q.sysml");
    client.open(
        &u,
        "package Q {\n    attribute x : ISQ::\n    attribute y : SI::\n}\n",
    );
    let detail = |items: &[lsp_types::CompletionItem], label: &str| -> Option<String> {
        items
            .iter()
            .find(|i| i.label == label)
            .and_then(|i| i.detail.clone())
    };
    // After `attribute x : ISQ::` on line 1.
    let isq = complete(&mut client, &u, 1, 23);
    assert_eq!(
        detail(&isq, "MassValue").as_deref(),
        Some("ISQBase::MassValue")
    );
    assert_eq!(
        detail(&isq, "LengthValue").as_deref(),
        Some("ISQBase::LengthValue")
    );
    assert!(detail(&isq, "TemperatureDifferenceValue").is_some());
    // After `attribute y : SI::` on line 2.
    let si = complete(&mut client, &u, 2, 22);
    assert_eq!(detail(&si, "kg").as_deref(), Some("SI::kg"));
    assert_eq!(
        detail(&si, "MassValue").as_deref(),
        Some("ISQBase::MassValue")
    );
    assert_eq!(detail(&si, "kilo").as_deref(), Some("SIPrefixes::kilo"));
    client.shutdown();
}

/// `import ISQ::*;` makes `MassValue` visible — `ISQ` re-exports
/// `ISQBase` — so accepting it adds no import, while `Real`, which
/// `ISQ` imports only privately, still brings its own.
#[test]
fn a_facade_import_admits_what_it_re_exports() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("a.sysml");
    client.open(
        &u,
        "package A {\n    private import ISQ::*;\n    attribute m : \n}\n",
    );
    // After `attribute m : ` on line 2.
    let items = complete(&mut client, &u, 2, 18);
    let edits = |label: &str| {
        items
            .iter()
            .find(|i| i.label == label)
            .unwrap_or_else(|| panic!("`{label}` offered"))
            .additional_text_edits
            .clone()
    };
    assert_eq!(edits("MassValue"), None);
    assert_eq!(edits("TemperatureDifferenceValue"), None);
    let real = edits("Real").expect("an import for `Real`");
    assert!(
        real[0].new_text.contains("import ScalarValues::Real;"),
        "{real:?}"
    );
    client.shutdown();
}

/// Inside a unit bracket too, an existing import admits what the
/// imported package re-exports: `Units` re-exports `SI`, so after
/// `import Units::*;` accepting `kg` needs no import of its own.
#[test]
fn unit_brackets_admit_what_an_import_re_exports() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("u.sysml");
    client.open(
        &u,
        "package Units {\n    public import SI::*;\n}\npackage P {\n    private import ISQ::*;\n    \
         private import Units::*;\n    attribute m : MassValue = 5 [k\n}\n",
    );
    // After `[k` on line 6.
    let items = complete(&mut client, &u, 6, 34);
    let kg = items
        .iter()
        .find(|i| i.label == "kg")
        .expect("`kg` offered");
    let imports: Vec<&str> = kg
        .additional_text_edits
        .iter()
        .flatten()
        .map(|e| e.new_text.as_str())
        .filter(|t| t.contains("import"))
        .collect();
    assert!(imports.is_empty(), "{imports:?}");
    client.shutdown();
}

/// Inserted imports name the conventional path: `ISQ::MassValue`, not
/// the part package that declares it (`ISQBase`), while a type that
/// only function packages re-export keeps its own (`ScalarValues::Real`).
/// Completion's auto-import, import-path completion, and the
/// "Add import" fix agree.
#[test]
fn imports_name_the_conventional_path() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("c.sysml");
    client.open(
        &u,
        "package C {\n    attribute m : \n    private import MassV\n}\n",
    );
    // After `attribute m : ` on line 1.
    let items = complete(&mut client, &u, 1, 18);
    let import = |label: &str| -> String {
        let item = items
            .iter()
            .find(|i| i.label == label)
            .unwrap_or_else(|| panic!("`{label}` offered"));
        item.additional_text_edits.as_ref().expect("an import")[0]
            .new_text
            .clone()
    };
    assert!(import("MassValue").contains("import ISQ::MassValue;"));
    assert!(import("DurationValue").contains("import ISQ::DurationValue;"));
    assert!(import("Real").contains("import ScalarValues::Real;"));
    // After `private import MassV` on line 2.
    let items = complete(&mut client, &u, 2, 24);
    let mass = items
        .iter()
        .find(|i| i.label == "MassValue")
        .expect("`MassValue` offered");
    let Some(lsp_types::CompletionTextEdit::Edit(edit)) = &mass.text_edit else {
        panic!("{mass:?}");
    };
    assert_eq!(edit.new_text, "ISQ::MassValue");

    // The quick fix on an unresolved `MassValue`.
    let v = uri("d.sysml");
    client.open(&v, "package D {\n    attribute m : MassValue;\n}\n");
    let range = lsp_types::Range {
        start: Position {
            line: 1,
            character: 18,
        },
        end: Position {
            line: 1,
            character: 27,
        },
    };
    let actions =
        client.request_ok::<lsp_types::request::CodeActionRequest>(lsp_types::CodeActionParams {
            text_document: TextDocumentIdentifier { uri: v },
            range,
            context: lsp_types::CodeActionContext {
                diagnostics: vec![lsp_types::Diagnostic {
                    range,
                    message: "unresolved reference `MassValue`".to_string(),
                    ..Default::default()
                }],
                ..Default::default()
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        });
    let titles: Vec<String> = actions
        .into_iter()
        .flatten()
        .filter_map(|a| match a {
            lsp_types::CodeActionOrCommand::CodeAction(a) => Some(a.title),
            lsp_types::CodeActionOrCommand::Command(_) => None,
        })
        .collect();
    assert!(
        titles.contains(&"Add import ISQ::MassValue".to_string()),
        "{titles:?}"
    );
    client.shutdown();
}

/// Inside a unit bracket too, an inserted import names the conventional
/// path: a unit its family's package re-exports (`Speeds` re-exports
/// `SpeedsBase`) is imported through that package.
#[test]
fn unit_brackets_import_through_the_conventional_path() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("s.sysml");
    client.open(
        &u,
        "package SpeedsBase {\n    private import ISQ::*;\n    \
         attribute <furl> furlongPerFortnight : SpeedUnit;\n}\npackage Speeds {\n    \
         public import SpeedsBase::*;\n}\npackage P {\n    private import ISQ::*;\n    \
         attribute v : SpeedValue = 5 [fu\n}\n",
    );
    // After `[fu` on line 9.
    let items = complete(&mut client, &u, 9, 35);
    let furl = items
        .iter()
        .find(|i| i.label == "furl")
        .expect("`furl` offered");
    let imports: Vec<&str> = furl
        .additional_text_edits
        .iter()
        .flatten()
        .map(|e| e.new_text.as_str())
        .filter(|t| t.contains("import"))
        .collect();
    assert_eq!(imports, ["\n    private import Speeds::furl;"]);
    assert_eq!(
        furl.label_details
            .as_ref()
            .and_then(|d| d.description.as_deref()),
        Some("import Speeds")
    );
    client.shutdown();
}

/// A unit alias completes as the unit it names, also when it names
/// the unit by its short symbol (`alias arcmin for '′';`).
#[test]
fn unit_aliases_complete_as_units() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("s.sysml");
    client.open(&u, "package S {\n    attribute a : SI::\n}\n");
    // After `attribute a : SI::` on line 1.
    let items = complete(&mut client, &u, 1, 22);
    let kind = |label: &str| {
        items
            .iter()
            .find(|i| i.label == label)
            .unwrap_or_else(|| panic!("`{label}` offered"))
            .kind
    };
    let unit = kind("kg");
    assert_eq!(unit, Some(lsp_types::CompletionItemKind::PROPERTY));
    assert_eq!(kind("arcmin"), unit);
    assert_eq!(kind("m/s²"), unit);
    client.shutdown();
}

/// A name two of a package's re-exported packages both declare denotes
/// neither there: `ISQ::MagneticDipoleMomentValue` is an ambiguous
/// reference (`ISQElectromagnetism` and `ISQAtomicNuclear` each declare
/// one). `ISQ::` does not offer it, `import ISQ::*;` does not count as
/// providing it, and no inserted import runs through `ISQ`, while its
/// unambiguous neighbours are unaffected.
#[test]
fn ambiguous_library_names_are_not_imported_through() {
    let mut client = Client::start_with(InitializeParams::default());
    let q = uri("q.sysml");
    client.open(&q, "package Q {\n    attribute y : ISQ::\n}\n");
    // After `attribute y : ISQ::` on line 1.
    let labels: Vec<String> = complete(&mut client, &q, 1, 23)
        .into_iter()
        .map(|i| i.label)
        .collect();
    assert!(labels.iter().any(|l| l == "MassValue"));
    assert!(!labels.iter().any(|l| l == "MagneticDipoleMomentValue"));

    let a = uri("a.sysml");
    for (text, line) in [
        ("package A {\n    attribute m : \n}\n", 1),
        (
            "package A {\n    private import ISQ::*;\n    attribute m : \n}\n",
            2,
        ),
    ] {
        client.open(&a, text);
        let items = complete(&mut client, &a, line, 18);
        let dipole = items
            .iter()
            .find(|i| i.label == "MagneticDipoleMomentValue")
            .expect("offered");
        let import = &dipole.additional_text_edits.as_ref().expect("an import")[0].new_text;
        assert!(
            import.contains("import ISQAtomicNuclear::MagneticDipoleMomentValue;")
                || import.contains("import ISQElectromagnetism::MagneticDipoleMomentValue;"),
            "{text:?}: {import}"
        );
    }
    client.shutdown();
}

/// The library's private members are no names for a model: `Triggers`
/// publicly imports `Clocks` and `Observation`, but not their private
/// `UniversalClockLife` or `ObserveChange`, which neither `Triggers::`
/// nor their own packages' qualifiers offer, and neither does the flat
/// list.
#[test]
fn private_library_members_are_not_offered() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("p.sysml");
    client.open(
        &u,
        "package P {\n    part a : Triggers::\n    part b : Clocks::\n    part c : \n}\n",
    );
    let labels = |items: Vec<lsp_types::CompletionItem>| -> Vec<String> {
        items.into_iter().map(|i| i.label).collect()
    };
    // After `part a : Triggers::` on line 1.
    let triggers = labels(complete(&mut client, &u, 1, 23));
    assert!(triggers.iter().any(|l| l == "Clock"), "{triggers:?}");
    let clocks = labels(complete(&mut client, &u, 2, 21));
    assert!(clocks.iter().any(|l| l == "Clock"), "{clocks:?}");
    let flat = labels(complete(&mut client, &u, 3, 13));
    for private in ["UniversalClockLife", "ObserveChange", "DefaultMonitorLife"] {
        for (list, labels) in [
            ("Triggers::", &triggers),
            ("Clocks::", &clocks),
            ("flat", &flat),
        ] {
            assert!(!labels.iter().any(|l| l == private), "{private} in {list}");
        }
    }
    client.shutdown();
}

/// After a qualifier, a member the namespace re-exports is offered
/// without its documentation — `ISQ::` re-exports some two thousand —
/// while the namespace's own members, and every member under its own
/// namespace's qualifier (`ISQBase::MassValue`), keep theirs.
#[test]
fn re_exported_members_complete_without_documentation() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("d.sysml");
    client.open(
        &u,
        "package D {\n    attribute a : ISQ::\n    attribute b : ISQBase::\n}\n",
    );
    let documented = |items: &[lsp_types::CompletionItem], label: &str| {
        items
            .iter()
            .find(|i| i.label == label)
            .unwrap_or_else(|| panic!("`{label}` offered"))
            .documentation
            .is_some()
    };
    // After `ISQ::` on line 1, and `ISQBase::` on line 2.
    let isq = complete(&mut client, &u, 1, 23);
    assert!(!documented(&isq, "MassValue"));
    assert!(documented(&isq, "TemperatureDifferenceValue"));
    let base = complete(&mut client, &u, 2, 27);
    assert!(documented(&base, "MassValue"));
    client.shutdown();
}

/// A private unit is offered in a unit bracket only inside its own
/// package, where it needs no import; outside it no import could make
/// it visible, and the library's unit of the same name is offered
/// instead.
#[test]
fn unit_brackets_offer_private_units_only_where_visible() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("h.sysml");
    client.open(
        &u,
        "package Speeds {\n    private import ISQ::*;\n    \
         private attribute <furl> furlongPerFortnight : SpeedUnit;\n    \
         private attribute <m> surveyMetre : LengthUnit;\n    \
         attribute inside : SpeedValue = 5 [fu\n}\npackage P {\n    private import ISQ::*;\n    \
         attribute outside : SpeedValue = 5 [fu\n}\n",
    );
    let unit = |items: &[lsp_types::CompletionItem], label: &str| {
        items
            .iter()
            .find(|i| i.label == label)
            .map(|i| i.detail.clone().unwrap_or_default())
    };
    // After `[fu` inside `Speeds` (line 4), then inside `P` (line 8).
    let inside = complete(&mut client, &u, 4, 42);
    assert!(unit(&inside, "furl").is_some());
    assert_eq!(unit(&inside, "m").as_deref(), Some("Speeds::m"));
    let outside = complete(&mut client, &u, 8, 43);
    assert_eq!(unit(&outside, "furl"), None);
    assert_eq!(unit(&outside, "m").as_deref(), Some("SI::m"));
    client.shutdown();
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

/// A comment above the declaration is not part of its statement: a `;`
/// inside it does not start the statement early, so the words after
/// that `;` are not read as the declaration and the typing lands after
/// the declared name, not inside the comment.
#[test]
fn a_comment_above_the_declaration_is_not_read_as_it() {
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("c.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         /* measured; see attribute below */\n    attribute gravity = 9.8 [k\n}\n",
    );
    // Cursor after `[k` on line 4.
    let items = complete(&mut client, &u, 4, 30);
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
            line: 4,
            character: 21
        }
    );
    client.shutdown();
}

#[test]
fn a_unit_that_does_not_parse_leaves_typing_on() {
    // Another open unit ends mid-declaration: no `;`, no closing brace.
    let mut client = Client::start_with(InitializeParams::default());
    client.open(
        &uri("k.kerml"),
        "package K {\n    private import ScalarValues::*;\n    feature m : Real\n",
    );
    let u = uri("g.sysml");
    client.open(&u, DOC);
    let items = complete(&mut client, &u, 3, 30);
    let kg = items.iter().find(|i| i.label == "kg").expect("`kg` item");
    let typing = kg
        .additional_text_edits
        .iter()
        .flatten()
        .any(|e| e.new_text == " : MassValue");
    assert!(typing, "{:?}", kg.additional_text_edits);
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
fn quoted_multiword_units_replace_the_typed_name_and_type_through() {
    // A multi-word unit typed quoted, word by word: the accept replaces
    // the whole typed spelling from its opening quote (not just `h`),
    // the bracket closes, and the quantity type is declared — the
    // accepted name is the whole bracket content.
    let mut client = Client::start_with(InitializeParams::default());
    let u = uri("s.sysml");
    client.open(
        &u,
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    attribute speed = 90 ['kilometre per h\n}\n",
    );
    let items = complete(&mut client, &u, 3, 42);
    let kph = items
        .iter()
        .find(|i| i.label == "kilometre per hour")
        .expect("`kilometre per hour` item");
    let Some(lsp_types::CompletionTextEdit::Edit(edit)) = &kph.text_edit else {
        panic!("quoted insert text needs an edit: {kph:?}");
    };
    assert_eq!(edit.new_text, "'kilometre per hour']");
    assert_eq!(
        edit.range.start,
        Position {
            line: 3,
            character: 26
        },
        "from the opening quote"
    );
    assert_eq!(kph.filter_text.as_deref(), Some("'kilometre per hour'"));
    let typing = kph
        .additional_text_edits
        .iter()
        .flatten()
        .any(|e| e.new_text == " : SpeedValue");
    assert!(typing, "{:?}", kph.additional_text_edits);
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

/// `text` with `item` accepted: its main edit — the snippet stop dropped
/// — and its additional edits applied (the text is ASCII, so a position's
/// character is its byte on the line).
fn accepted(text: &str, item: &lsp_types::CompletionItem) -> String {
    let offset = |p: Position| {
        let line: usize = text
            .split_inclusive('\n')
            .take(p.line as usize)
            .map(str::len)
            .sum();
        line + p.character as usize
    };
    let mut edits: Vec<(usize, usize, String)> = item
        .additional_text_edits
        .iter()
        .flatten()
        .map(|e| {
            (
                offset(e.range.start),
                offset(e.range.end),
                e.new_text.clone(),
            )
        })
        .collect();
    match &item.text_edit {
        Some(lsp_types::CompletionTextEdit::Edit(e)) => edits.push((
            offset(e.range.start),
            offset(e.range.end),
            e.new_text.replace("$0", ""),
        )),
        other => panic!("expected a main edit: {other:?}"),
    }
    edits.sort_by_key(|&(start, _, _)| std::cmp::Reverse(start));
    let mut out = text.to_string();
    for (start, end, new_text) in edits {
        out.replace_range(start..end, &new_text);
    }
    out
}

/// A unit accepted in a bracket left open before the statement's `;`
/// closes the bracket right behind it, and — being then the whole
/// bracket — declares the type an untyped attribute's value takes.
#[test]
fn a_unit_accepted_before_the_terminator_closes_its_bracket() {
    for (line, expected) in [
        (
            "attribute d = 3 [h;",
            "attribute d : DurationValue = 3 [h];",
        ),
        (
            "attribute d : DurationValue = 3 [h;",
            "attribute d : DurationValue = 3 [h];",
        ),
    ] {
        for snippets in [false, true] {
            let mut client = Client::start_with(InitializeParams {
                capabilities: serde_json::from_value(serde_json::json!({
                    "textDocument": {"completion": {"completionItem": {"snippetSupport": snippets}}}
                }))
                .unwrap(),
                ..InitializeParams::default()
            });
            let u = uri("d.sysml");
            let text = format!(
                "package G {{\n    private import ISQ::*;\n    private import SI::*;\n    {line}\n}}\n"
            );
            client.open(&u, &text);
            let character = 4 + line.find('[').unwrap() as u32 + 2;
            let items = complete(&mut client, &u, 3, character);
            let h = items.iter().find(|i| i.label == "h").expect("`h` item");
            let out = accepted(&text, h);
            assert_eq!(
                out.lines().nth(3),
                Some(format!("    {expected}").as_str()),
                "{h:?}"
            );
            client.shutdown();
        }
    }
}

/// A list read with a `]` right after the cursor — the one an editor
/// adds with the `[` — is sent incomplete: its accepts count on that
/// `]` (a unit's carries no `]` of its own, and declares the type as
/// the bracket's whole content), and the user may delete it and type
/// on, so the list is to be asked for again. With no `]` there, the
/// accepts close the bracket themselves, and the list is complete.
#[test]
fn a_list_read_before_the_added_closer_is_asked_for_again() {
    let mut client = Client::start_with(InitializeParams::default());
    for (line, character, incomplete) in [
        ("attribute d = 3 [];", 21, true),
        ("attribute d = 3 [h];", 22, true),
        ("attribute d = 3 [h;", 22, false),
        ("attribute d = 3 [h", 22, false),
        // a multiplicity's bound takes names, and asks for no list again
        ("part w [0..n];", 16, false),
    ] {
        let u = uri(&format!("i{character}{incomplete}.sysml"));
        let text = format!(
            "package G {{\n    private import ISQ::*;\n    private import SI::*;\n    {line}\n}}\n"
        );
        client.open(&u, &text);
        let sent = match completion(&mut client, &u, 3, character) {
            Some(CompletionResponse::List(list)) => list.is_incomplete,
            Some(CompletionResponse::Array(_)) => false,
            None => panic!("expected items: {line}"),
        };
        assert_eq!(sent, incomplete, "{line}");
    }
    client.shutdown();
}

/// A unit accepted before the statement's `;` declares the type only
/// where the accept also writes the bracket's `]`: nothing but blanks
/// may follow that `;` on the line. Before a `}` or a comment the
/// bracket stays open, and no typing is added to a value that does not
/// parse.
#[test]
fn a_unit_accepted_where_its_bracket_stays_open_declares_no_type() {
    let mut client = Client::start_with(InitializeParams::default());
    for (n, (line, typed)) in [
        ("attribute d = 3 [h;   ", true),
        ("part def Q { attribute d = 3 [h; }", false),
        ("attribute d = 3 [h; attribute e = 4;", false),
        ("attribute d = 3 [h;  // note", false),
    ]
    .into_iter()
    .enumerate()
    {
        let u = uri(&format!("o{n}.sysml"));
        let text = format!(
            "package G {{\n    private import ISQ::*;\n    private import SI::*;\n    {line}\n}}\n"
        );
        client.open(&u, &text);
        let character = 4 + line.find('[').unwrap() as u32 + 2;
        let items = complete(&mut client, &u, 3, character);
        let h = items.iter().find(|i| i.label == "h").expect("`h` item");
        let typing = h
            .additional_text_edits
            .iter()
            .flatten()
            .any(|e| e.new_text == " : DurationValue");
        assert_eq!(typing, typed, "{line}: {h:?}");
        if typed {
            let out = accepted(&text, h);
            assert!(out.contains("[h];"), "{out}");
        }
    }
    client.shutdown();
}

/// A list sent incomplete is asked for again at every keystroke, so it
/// carries only the items the word typed can still match; with no word
/// typed yet it carries them all.
#[test]
fn an_incomplete_list_carries_what_the_typed_word_matches() {
    let mut client = Client::start_with(InitializeParams::default());
    let mut all = 0;
    for (n, (line, character)) in [
        ("attribute m : MassValue = 5 [];", 33),
        ("attribute m : MassValue = 5 [kg];", 35),
    ]
    .into_iter()
    .enumerate()
    {
        let u = uri(&format!("f{n}.sysml"));
        let text = format!(
            "package G {{\n    private import ISQ::*;\n    private import SI::*;\n    {line}\n}}\n"
        );
        client.open(&u, &text);
        let Some(CompletionResponse::List(list)) = completion(&mut client, &u, 3, character) else {
            panic!("an incomplete list: {line}");
        };
        if n == 0 {
            all = list.items.len();
            continue;
        }
        let labels: Vec<&str> = list.items.iter().map(|i| i.label.as_str()).collect();
        assert!(
            labels.contains(&"kg") && labels.contains(&"kilogram"),
            "{labels:?}"
        );
        assert!(labels.len() < all, "{} of {all}", labels.len());
        // Every item holds `k` then `g`, case aside.
        for item in &list.items {
            let spelled = item
                .filter_text
                .as_deref()
                .unwrap_or(&item.label)
                .to_lowercase();
            let k = spelled.find('k').unwrap_or_else(|| panic!("{spelled}"));
            assert!(spelled[k..].contains('g'), "{spelled}");
        }
    }
    client.shutdown();
}

/// Accepting a document's own unit declares its quantity type when
/// another open document declares a package of the same name: the unit
/// is found where it is declared, not by a path the other package
/// answers.
#[test]
fn a_unit_of_a_package_two_documents_declare_declares_its_type() {
    let mut client = Client::start_with(InitializeParams::default());
    let a = uri("a.sysml");
    let b = uri("b.sysml");
    client.open(
        &a,
        "package Money {\n    private import ISQ::*;\n    \
         attribute <fur> furlong : LengthUnit;\n}\n",
    );
    client.open(
        &b,
        "package Money {\n    private import ISQ::*;\n    \
         attribute <lea> league : LengthUnit;\n    attribute trip = 3 [\n}\n",
    );
    // After `[` on line 3.
    let items = complete(&mut client, &b, 3, 24);
    let lea = items.iter().find(|i| i.label == "lea").expect("`lea` item");
    let typing = lea
        .additional_text_edits
        .iter()
        .flatten()
        .find(|e| e.new_text == " : LengthValue")
        .unwrap_or_else(|| panic!("expected ` : LengthValue`: {:?}", lea.additional_text_edits));
    // Right after the declared name `trip`.
    assert_eq!(
        typing.range.start,
        Position {
            line: 3,
            character: 18
        }
    );
    client.shutdown();
}

/// A document's own units stay in its unit brackets when another open
/// document declares a package of the same name: the units are found
/// where they are declared, not by a path the other package answers.
#[test]
fn units_of_a_package_two_documents_declare_stay_offered() {
    let mut client = Client::start_with(InitializeParams::default());
    let a = uri("a.sysml");
    let b = uri("b.sysml");
    client.open(
        &a,
        "package Money {\n    attribute def CurrencyUnit :> MeasurementReferences::SimpleUnit;\n    \
         attribute <'€'> euro : CurrencyUnit;\n}\n",
    );
    client.open(
        &b,
        "package Money {\n    attribute def CurrencyUnit :> MeasurementReferences::SimpleUnit;\n    \
         attribute <'$'> dollar : CurrencyUnit;\n    attribute price = 5 [\n}\n",
    );
    let items = complete(&mut client, &b, 3, 25);
    for label in ["$", "dollar"] {
        assert!(
            items.iter().any(
                |i| i.label == label && i.detail.as_deref() == Some(&format!("Money::{label}"))
            ),
            "{label} offered"
        );
    }
    client.shutdown();
}
