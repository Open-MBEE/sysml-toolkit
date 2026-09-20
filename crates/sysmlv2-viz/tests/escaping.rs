//! Label and note escaping gates: names carrying line breaks, carriage
//! returns, quotes and brackets reach every PlantUML emitter that
//! quotes labels without breaking the diagram text, link URLs stay
//! inside their `[[…]]`, and note bodies can spell the note terminator.

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_viz::{View, VizOptions, plantuml};

fn resolved_named(name: &str, src: &str) -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source(name.to_string(), src);
    assert!(
        unit.diagnostics.is_empty(),
        "fixture must parse: {:?}",
        unit.diagnostics
    );
    ResolvedModel::build(&model)
}

fn resolved(src: &str) -> ResolvedModel {
    resolved_named("odd.sysml", src)
}

fn view_opts(view: View) -> VizOptions {
    VizOptions::default().with_view(view)
}

/// Names whose escape sequences the lexer decodes into real line
/// breaks, carriage returns and quotes.
const ODD: &str = r#"package 'Pkg\nOne' {
    part def 'Def "Q"\r\n[x]' {
        attribute 'att\nr' = "va\nl";
        part 'sub\npart' : 'Def "Q"\r\n[x]';
        port 'po\nrt';
    }
    enum def 'En\num' { 'li\nt'; }
    part 'top\npart' : 'Def "Q"\r\n[x]';
    part def 'Sy\ns' { part 'a\n1'; part 'b\n2'; flow from 'a\n1' to 'b\n2'; }
    state def 'St\nDef' { state 'st\nate'; }
    action def 'Ac\ntion' { action 'a\nct'; }
    use case def 'Use\nCase' { actor 'ac\ntor'; subject 'sub\nj'; }
}
"#;

/// Every command line closes the quotes it opens (a decoded line
/// break would split a quoted label across two lines, each with one
/// quote) and nothing carries a carriage return.
fn assert_well_formed(out: &str) {
    assert!(out.starts_with("@startuml\n"), "{out}");
    assert!(out.ends_with("@enduml\n"), "{out}");
    assert!(!out.contains('\r'), "carriage return survived: {out:?}");
    for line in out.lines() {
        assert_eq!(
            line.matches('"').count() % 2,
            0,
            "unbalanced quotes on line {line:?} of\n{out}"
        );
    }
}

#[test]
fn tree_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert_well_formed(&out);
    assert!(out.contains("package \"Pkg\\nOne\" as"), "{out}");
    assert!(out.contains("class \"Def ''Q''\\n[x]\" as"), "{out}");
    assert!(
        out.contains("class \"top\\npart : Def ''Q''\\n[x]\" as"),
        "{out}"
    );
    assert!(out.contains("enum \"En\\num\" as"), "{out}");
    // Compartment lines are unquoted member syntax: line breaks become
    // spaces there.
    assert!(out.contains("    att r = \"va l\"\n"), "{out}");
    assert!(out.contains("    li t\n"), "{out}");
}

#[test]
fn interconnection_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::Interconnection));
    assert_well_formed(&out);
    assert!(out.contains("package \"Pkg\\nOne\" as"), "{out}");
    assert!(out.contains("rectangle \"Def ''Q''\\n[x]\" as"), "{out}");
    assert!(out.contains("port \"po\\nrt\" as"), "{out}");
    assert!(
        out.contains("rectangle \"sub\\npart : Def ''Q''\\n[x]\" as"),
        "{out}"
    );
}

#[test]
fn behavior_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::State));
    assert_well_formed(&out);
    assert!(out.contains("state \"St\\nDef\" as"), "{out}");
    assert!(out.contains("state \"st\\nate\" as"), "{out}");
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::Action));
    assert_well_formed(&out);
    assert!(out.contains("state \"Ac\\ntion\" as"), "{out}");
    assert!(out.contains("state \"a\\nct\" as"), "{out}");
}

#[test]
fn sequence_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::Sequence));
    assert_well_formed(&out);
    assert!(out.contains("box \"Sy\\ns\"\n"), "{out}");
    assert!(out.contains("participant \"a\\n1\" as"), "{out}");
    assert!(out.contains("participant \"b\\n2\" as"), "{out}");
}

#[test]
fn case_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::Case));
    assert_well_formed(&out);
    assert!(out.contains("usecase \"Use\\nCase\" as"), "{out}");
    assert!(out.contains("actor \"ac\\ntor\" as"), "{out}");
    assert!(out.contains("rectangle \"sub\\nj\" as"), "{out}");
}

#[test]
fn mixed_labels_escape_line_breaks() {
    let mut r = resolved(ODD);
    let out = plantuml(&mut r, None, &view_opts(View::Mixed));
    assert_well_formed(&out);
    assert!(out.contains("package \"Pkg\\nOne\" as"), "{out}");
    assert!(out.contains("usecase \"Use\\nCase\" as"), "{out}");
    assert!(out.contains("actor \"ac\\ntor\" as"), "{out}");
    assert!(out.contains("rectangle \"St\\nDef\" as"), "{out}");
}

#[test]
fn link_urls_encode_link_delimiters() {
    // `{file}` carries the unit name verbatim; `{qname}` carries the
    // element's (re-escaped) qualified name.
    let mut r = resolved_named(
        "odd ]{}\r\nname.sysml",
        "package P { part def 'a]b{c}'; }\n",
    );
    let opts = VizOptions::default().with_link_template(Some("edit://{file}#{qname}".to_string()));
    let out = plantuml(&mut r, None, &opts);
    assert_well_formed(&out);
    assert!(
        out.contains("[[edit://odd%20%5D%7B%7D%0D%0Aname.sysml#P::'a%5Db%7Bc%7D']]"),
        "{out}"
    );
    // Neither delimiter survives inside any link.
    for line in out.lines() {
        if let Some(start) = line.find("[[") {
            let link = &line[start + 2..line.rfind("]]").unwrap()];
            assert!(
                !link.contains([']', '{', '}', ' ', '\n']),
                "unencoded delimiter in link {link:?}"
            );
        }
    }
}

/// The quoted note form cannot be ended by its own body: every
/// spelling the renderer accepts as the block terminator stays inside
/// the note, and each body line is one `\n`-separated line of it.
#[test]
fn note_bodies_cannot_end_the_note() {
    let src = "package P {
    part def A {
        doc /* first line
             * end note
             * endnote
             *    END NOTE
             * end  note
             * says \"end note\" and goes on */
    }
    use case def U {
        objective { doc /* aim
                         * end note
                         * still the aim */ }
    }
}
";
    let terminator = |line: &str| {
        line.trim()
            .to_lowercase()
            .split_whitespace()
            .collect::<String>()
            == "endnote"
    };
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert_well_formed(&out);
    assert!(!out.lines().any(terminator), "{out}");
    assert!(
        out.contains(
            "note \"first line\\nend note\\nendnote\\nEND NOTE\\nend  note\\nsays ''end note'' and goes on \" as c1\n"
        ),
        "{out}"
    );
    assert!(out.contains("\nc1 .. n"), "{out}");

    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &view_opts(View::Case));
    assert_well_formed(&out);
    assert!(!out.lines().any(terminator), "{out}");
    assert!(
        out.contains("note \"«objective»\\naim\\nend note\\nstill the aim \" as o1\n"),
        "{out}"
    );
    assert!(out.contains("\no1 .. n1\n"), "{out}");
}

/// A name carrying the two characters `\` and `n` must not reach the
/// renderer spelled like one carrying a line break: the backslash is
/// doubled, so the two labels stay distinguishable and the mapping is
/// reversible.
#[test]
fn labels_double_a_literal_backslash() {
    let src = r#"package P {
    part def 'Lit\\nEral';
    part def 'Bro\nken';
}
"#;
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert_well_formed(&out);
    assert!(out.contains(r#"class "Lit\\nEral" as"#), "{out}");
    assert!(out.contains(r#"class "Bro\nken" as"#), "{out}");
}
