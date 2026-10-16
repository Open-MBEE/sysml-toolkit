//! The batch reads answer what the per-element reads they stand for
//! answer: `outline` what a walk through `roots`, `members` and the
//! name, metaclass and id reads assembles, and `rows` what each
//! per-element read answers.
use std::path::{Path, PathBuf};

use serde_json::{Value, json};
use sysmlv2_wasm::{Element, PreparedLibrary, Session};

fn sources(units: &[(String, String)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

fn owned(units: &[(&str, &str)]) -> Vec<(String, String)> {
    units
        .iter()
        .map(|(name, text)| (name.to_string(), text.to_string()))
        .collect()
}

const FLASHLIGHT: &str = "package Flashlight {\n    part def Body;\n    part def Battery {\n        attribute voltage = 3;\n    }\n    part flashlight {\n        part body : Body;\n        part battery : Battery;\n    }\n}\n";

/// Anonymous elements, nameless redefinitions named by what they
/// redefine, sequences, defaults, docs and a second unit.
const MIXED: &str = "package P {
    doc /* the package */
    attribute def Mass;
    part def Chassis { attribute mass : Mass; attribute wheelbase : Mass; attribute ratios[*] ordered nonunique = (1, 2, 3); }
    part def Crawler { part chassis : Chassis; attribute tags[*] = (\"a\", \"b\"); attribute mode default 2; }
    part med : Crawler { attribute :>> chassis.mass; attribute :>> mode = 3; }
    part tiny : Crawler { part :>> chassis { attribute :>> mass; } }
    part : Crawler;
    connect med.chassis to tiny.chassis;
    package Deep { package A { package B { package C { part def Leaf { attribute x = 1; } } } } }
    comment about Chassis /* a chassis */
}
";

const SECOND: &str =
    "package Q { private import P::*; part q : Crawler { attribute :>> tags = (\"c\"); } }\n";

/// The budgets of one walk.
#[derive(Clone, Copy)]
struct Budgets {
    outline_nodes: usize,
    outline_depth: usize,
    shape_nodes: usize,
    shape_depth: usize,
}

impl Budgets {
    const DEFAULT: Budgets = Budgets {
        outline_nodes: 4000,
        outline_depth: 24,
        shape_nodes: 20000,
        shape_depth: 64,
    };

    fn opts(self) -> String {
        json!({
            "outlineNodes": self.outline_nodes,
            "outlineDepth": self.outline_depth,
            "shapeNodes": self.shape_nodes,
            "shapeDepth": self.shape_depth,
        })
        .to_string()
    }
}

/// The host's walk, read element by element: one traversal building the
/// outline and the shape under the same budgets.
struct CallWalk {
    budgets: Budgets,
    outline_left: i64,
    nodes: Vec<Value>,
    truncated: bool,
}

/// `derived(e, "name")` when that is a string, else the declared name.
fn display_name(s: &mut Session, e: &Element) -> Option<String> {
    let derived: Value = serde_json::from_str(&s.derived(e, "name").unwrap()).unwrap();
    match derived {
        Value::String(name) => Some(name),
        _ => s.name(e).unwrap(),
    }
}

impl CallWalk {
    fn visit(&mut self, s: &mut Session, e: &Element, owner: i64, depth: usize) -> Option<Value> {
        let name = display_name(s, e);
        let qualified_name = s.qualified_name(e).unwrap();
        let metaclass = s.metaclass(e).unwrap();
        let mut this = owner;
        let named = name.as_deref().is_some_and(|n| !n.is_empty())
            && qualified_name.as_deref().is_some_and(|q| !q.is_empty());
        if named {
            if self.nodes.len() >= self.budgets.shape_nodes {
                self.truncated = true;
            } else {
                this = i64::try_from(self.nodes.len()).unwrap();
                self.nodes.push(json!({
                    "id": s.element_id(e).unwrap(),
                    "name": name,
                    "qualifiedName": qualified_name,
                    "metaclass": metaclass,
                    "owner": owner,
                }));
            }
        }
        let in_outline = self.outline_left > 0;
        self.outline_left -= 1;
        let mut children = Vec::new();
        let members = s.members(e).unwrap();
        if depth < self.budgets.shape_depth {
            for m in &members {
                let child = self.visit(s, m, this, depth + 1);
                if let Some(child) = child {
                    if depth < self.budgets.outline_depth {
                        children.push(child);
                    }
                }
            }
        } else if !members.is_empty() {
            self.truncated = true;
        }
        in_outline.then(|| {
            json!({
                "name": name,
                "metaclass": metaclass,
                "qualifiedName": qualified_name,
                "children": children,
            })
        })
    }
}

fn walk_by_calls(s: &mut Session, budgets: Budgets) -> Value {
    let mut walk = CallWalk {
        budgets,
        outline_left: i64::try_from(budgets.outline_nodes).unwrap(),
        nodes: Vec::new(),
        truncated: false,
    };
    let mut outline = Vec::new();
    for root in s.roots() {
        if let Some(node) = walk.visit(s, &root, -1, 0) {
            outline.push(node);
        }
    }
    json!({
        "outline": outline,
        "shape": { "nodes": walk.nodes, "truncated": walk.truncated },
    })
}

fn outline(s: &mut Session, budgets: Budgets) -> Value {
    serde_json::from_str(&s.outline(Some(budgets.opts())).unwrap()).unwrap()
}

/// Every budget combination worth telling apart on a model of this size:
/// the defaults, and tight ones cutting each product at a node and a
/// depth limit.
fn budget_matrix(nodes: usize) -> Vec<Budgets> {
    let few = (nodes / 3).max(1);
    vec![
        Budgets::DEFAULT,
        Budgets {
            outline_nodes: few,
            outline_depth: 1,
            shape_nodes: few * 2,
            shape_depth: 2,
        },
        Budgets {
            outline_nodes: 0,
            outline_depth: 0,
            shape_nodes: 0,
            shape_depth: 0,
        },
        Budgets {
            outline_nodes: few * 2,
            outline_depth: 5,
            shape_nodes: few,
            shape_depth: 3,
        },
        // an outline deeper than the walk goes
        Budgets {
            outline_nodes: nodes,
            outline_depth: 8,
            shape_nodes: nodes,
            shape_depth: 4,
        },
    ]
}

fn assert_outline_matches_calls(s: &mut Session, label: &str) -> usize {
    let whole = outline(s, Budgets::DEFAULT);
    let nodes = whole["shape"]["nodes"].as_array().unwrap().len();
    for budgets in budget_matrix(nodes) {
        let by_calls = walk_by_calls(s, budgets);
        let batch = outline(s, budgets);
        assert!(
            by_calls == batch,
            "{label} {}: the batch outline differs from the per-call walk",
            budgets.opts()
        );
    }
    nodes
}

/// The fields `rows` reads, every one of the vocabulary.
const FIELDS: &[&str] = &[
    "name",
    "shortName",
    "qualifiedName",
    "referenceSpelling",
    "metaclass",
    "owner",
    "isLibraryElement",
    "valueSource",
    "valueIsDefault",
    "docs",
    "declarationSite",
    "memberExtent",
    "property:isOrdered",
    "property:isUnique",
    "property:declaredName",
    "property:ownedRelationship",
    "derived:name",
    "derived:qualifiedName",
    "derived:ownedFeature",
];

/// A read as a `Result` of JSON, the way `rows` folds it.
fn read<T: serde::Serialize>(r: Result<T, String>) -> Result<Value, String> {
    r.map(|v| serde_json::to_value(v).unwrap())
}

fn decoded(r: Result<Option<String>, String>) -> Result<Value, String> {
    r.map(|v| v.map_or(Value::Null, |text| serde_json::from_str(&text).unwrap()))
}

/// One field of `e` through its per-element read.
fn per_call(s: &mut Session, e: &Element, field: &str) -> Result<Value, String> {
    if let Some(name) = field.strip_prefix("property:") {
        return s
            .property(e, name)
            .map(|text| serde_json::from_str(&text).unwrap());
    }
    if let Some(name) = field.strip_prefix("derived:") {
        return s
            .derived(e, name)
            .map(|text| serde_json::from_str(&text).unwrap());
    }
    match field {
        "name" => read(s.name(e)),
        "shortName" => read(s.short_name(e)),
        "qualifiedName" => read(s.qualified_name(e)),
        "referenceSpelling" => read(s.reference_spelling(e)),
        "metaclass" => read(s.metaclass(e)),
        "owner" => s
            .owner(e)
            .map(|o| o.map_or(Value::Null, |o| json!(s.element_id(&o).unwrap()))),
        "isLibraryElement" => read(s.is_library_element(e)),
        "valueSource" => read(s.value_source(e)),
        "valueIsDefault" => read(s.value_is_default(e)),
        "docs" => read(s.docs(e)),
        "declarationSite" => decoded(s.declaration_site(e)),
        "memberExtent" => decoded(s.member_extent_js(e)),
        _ => unreachable!("{field}"),
    }
}

/// Every element the outline walk reaches, by id, anonymous ones too.
fn every_id(s: &mut Session) -> Vec<String> {
    fn visit(s: &mut Session, e: &Element, out: &mut Vec<String>) {
        out.push(s.element_id(e).unwrap());
        for m in s.members(e).unwrap() {
            visit(s, &m, out);
        }
    }
    let mut out = Vec::new();
    for root in s.roots() {
        visit(s, &root, &mut out);
    }
    out
}

fn assert_rows_match_calls(s: &mut Session, ids: &[String], label: &str) {
    let rows: Value = serde_json::from_str(
        &s.rows(
            &serde_json::to_string(ids).unwrap(),
            &serde_json::to_string(FIELDS).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let rows = rows.as_array().unwrap();
    assert_eq!(rows.len(), ids.len());
    for (id, row) in ids.iter().zip(rows) {
        let e = s.element_by_id(id).expect("every walked id resolves");
        for field in FIELDS {
            match per_call(s, &e, field) {
                Ok(value) => {
                    assert_eq!(row.get(*field), Some(&value), "{label} {id} {field}");
                    assert!(row["errors"].get(*field).is_none());
                }
                Err(message) => {
                    assert!(row.get(*field).is_none(), "{label} {id} {field}");
                    assert_eq!(
                        row["errors"][*field],
                        json!(message),
                        "{label} {id} {field}"
                    );
                }
            }
        }
        let extra: Vec<&String> = row
            .as_object()
            .unwrap()
            .keys()
            .filter(|k| *k != "errors" && !FIELDS.contains(&k.as_str()))
            .collect();
        assert!(extra.is_empty(), "{label} {id}: unasked fields {extra:?}");
    }
}

#[test]
fn outline_matches_the_per_call_walk() {
    let mut s =
        Session::from_sources(&sources(&owned(&[("flashlight.sysml", FLASHLIGHT)]))).unwrap();
    assert_eq!(assert_outline_matches_calls(&mut s, "flashlight"), 7);
    let mut s = Session::from_sources(&sources(&owned(&[
        ("mixed.sysml", MIXED),
        ("second.sysml", SECOND),
    ])))
    .unwrap();
    assert_outline_matches_calls(&mut s, "mixed");
    let whole = outline(&mut s, Budgets::DEFAULT);
    // A nameless redefinition is named by what it redefines, and is in the shape.
    let med_mass = whole["shape"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["qualifiedName"] == "P::med::mode")
        .expect("the nameless redefinition is shaped by its derived name");
    assert_eq!(med_mass["name"], "mode");
    // The anonymous part is in the outline, not in the shape.
    let p = &whole["outline"][0];
    assert!(
        p["children"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["name"].is_null() && c["metaclass"] == "PartUsage")
    );
    assert_eq!(whole["shape"]["truncated"], false);
    // The empty document is the defaults.
    assert_eq!(
        s.outline(None).unwrap(),
        s.outline(Some(String::new())).unwrap()
    );
    assert_eq!(
        s.outline(None).unwrap(),
        s.outline(Some(Budgets::DEFAULT.opts())).unwrap()
    );
    assert!(
        s.outline(Some(r#"{"bogus":1}"#.into()))
            .unwrap_err()
            .contains("bad options")
    );
}

#[test]
fn outline_budgets_cut_where_the_walk_does() {
    let mut s = Session::from_sources(&sources(&owned(&[("mixed.sysml", MIXED)]))).unwrap();
    // the depth limit below an element with members truncates the shape
    let shallow = outline(
        &mut s,
        Budgets {
            shape_depth: 1,
            ..Budgets::DEFAULT
        },
    );
    assert_eq!(shallow["shape"]["truncated"], true);
    // the outline stops attaching below its own depth
    let flat = outline(
        &mut s,
        Budgets {
            outline_depth: 0,
            ..Budgets::DEFAULT
        },
    );
    assert_eq!(flat["outline"][0]["children"], json!([]));
    // the outline budget is claimed in visiting order, the root first
    let one = outline(
        &mut s,
        Budgets {
            outline_nodes: 1,
            ..Budgets::DEFAULT
        },
    );
    assert_eq!(one["outline"].as_array().unwrap().len(), 1);
    assert_eq!(one["outline"][0]["children"], json!([]));
    // the shape budget keeps a prefix
    let whole = outline(&mut s, Budgets::DEFAULT);
    let three = outline(
        &mut s,
        Budgets {
            shape_nodes: 3,
            ..Budgets::DEFAULT
        },
    );
    assert_eq!(three["shape"]["truncated"], true);
    assert_eq!(
        three["shape"]["nodes"].as_array().unwrap()[..],
        whole["shape"]["nodes"].as_array().unwrap()[..3]
    );
}

#[test]
fn rows_match_the_per_element_reads() {
    let mut s = Session::from_sources(&sources(&owned(&[
        ("mixed.sysml", MIXED),
        ("second.sysml", SECOND),
    ])))
    .unwrap();
    let ids = every_id(&mut s);
    assert!(ids.len() > 30);
    assert_rows_match_calls(&mut s, &ids, "mixed");
    // A sequence value reads with its feature's order and uniqueness.
    let ratios = s.resolve("P::Chassis::ratios").unwrap();
    let ratios_id = s.element_id(&ratios).unwrap();
    let rows: Value = serde_json::from_str(
        &s.rows(
            &json!([
                ratios_id,
                "not-an-id",
                "00000000-0000-0000-0000-000000000000"
            ])
            .to_string(),
            r#"["valueSource","property:isOrdered","property:isUnique"]"#,
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        rows,
        json!([
            {"valueSource": "(1, 2, 3)", "property:isOrdered": true, "property:isUnique": false},
            null,
            null,
        ])
    );
    // No fields, no ids.
    assert_eq!(
        s.rows(&json!([ratios_id]).to_string(), "[]").unwrap(),
        "[{}]"
    );
    assert_eq!(s.rows("[]", r#"["name"]"#).unwrap(), "[]");
    assert!(s.rows("[1]", "[]").unwrap_err().contains("bad ids"));
    assert!(s.rows("[]", "{}").unwrap_err().contains("bad fields"));
    assert!(
        s.rows("[]", r#"["name","nope"]"#)
            .unwrap_err()
            .contains("unknown row field: nope")
    );
}

/// The corpus checkout's directory, `None` (with a note) when absent.
fn corpus_dir(relative: &str) -> Option<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/sysmlv2-wasm sits two levels below the root")
        .join("spec-refs/SysML-v2-Release")
        .join(relative);
    if dir.is_dir() {
        Some(dir)
    } else {
        eprintln!("corpus not found at {}; skipping", dir.display());
        None
    }
}

fn units_under(dir: &Path) -> Vec<(String, String)> {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            ) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let name = p.strip_prefix(dir).unwrap().display().to_string();
            (name, std::fs::read_to_string(&p).unwrap())
        })
        .collect()
}

#[test]
fn batch_reads_match_the_per_call_reads_on_the_spec_examples() {
    let (Some(library), Some(examples)) = (
        corpus_dir("sysml.library"),
        corpus_dir("sysml/src/examples"),
    ) else {
        return;
    };
    let mut library = units_under(&library);
    library.extend(sysmlv2_model::ambient::units());
    let library = PreparedLibrary::new(&sources(&library), None).unwrap();
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(&examples)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    let mut walked = 0;
    for dir in dirs {
        let label = dir.file_name().unwrap().to_string_lossy().to_string();
        let units = units_under(&dir);
        if units.is_empty() {
            continue;
        }
        let Ok(mut s) = Session::from_sources_with_prepared_library(&sources(&units), &library)
        else {
            eprintln!("{label}: does not build; skipped");
            continue;
        };
        let nodes = assert_outline_matches_calls(&mut s, &label);
        let ids = every_id(&mut s);
        assert_rows_match_calls(&mut s, &ids, &label);
        if label == "Vehicle Example" {
            assert!(nodes > 500, "the vehicle example shapes {nodes} nodes");
        }
        eprintln!("{label}: {nodes} shape nodes, {} elements", ids.len());
        walked += 1;
    }
    assert!(walked >= 15, "only {walked} example directories built");
}
