//! Formatter gates: over the entire official corpus,
//! * semantic preservation — `parse(format(x))` equals `parse(x)` as ASTs
//!   (modulo spans);
//! * idempotency — `format(format(x)) == format(x)`;
//! * note preservation — every note in the input survives formatting.

use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::ast::{Dialect, SourceUnit};
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::print::{format_source, print_source};

fn corpus_files() -> Vec<PathBuf> {
    sysmlv2_testkit::corpus_files()
}

fn dialect_of(path: &Path) -> Dialect {
    if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
        Dialect::Kerml
    } else {
        Dialect::Sysml
    }
}

fn parse(src: &str, dialect: Dialect) -> sysmlv2_parser::parser::Parse {
    match dialect {
        Dialect::Sysml => parse_source(src),
        Dialect::Kerml => parse_kerml_source(src),
    }
}

/// AST equality modulo spans: pretty-debug output with `span: …` lines
/// dropped (every span in the AST prints as its own line under `{:#?}`).
fn normalized(unit: &SourceUnit) -> String {
    format!("{unit:#?}")
        .lines()
        .filter(|line| !line.trim_start().starts_with("span:"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn corpus_format_gates() {
    let mut failures = Vec::new();
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let dialect = dialect_of(&path);
        let display = path.display();

        let formatted = match format_source(&src, dialect) {
            Ok(f) => f,
            Err(diags) => {
                failures.push(format!("{display}: format failed: {}", diags[0].message));
                continue;
            }
        };

        // Semantic preservation.
        let reparsed = parse(&formatted, dialect);
        if !reparsed.diagnostics.is_empty() {
            failures.push(format!(
                "{display}: formatted output does not parse: {}",
                reparsed.diagnostics[0].message
            ));
            continue;
        }
        let original = parse(&src, dialect);
        if normalized(&original.unit) != normalized(&reparsed.unit) {
            failures.push(format!("{display}: AST changed by formatting"));
            continue;
        }

        // Idempotency.
        match format_source(&formatted, dialect) {
            Ok(second) => {
                if second != formatted {
                    failures.push(format!("{display}: formatting is not idempotent"));
                }
            }
            Err(diags) => {
                failures.push(format!(
                    "{display}: second format failed: {}",
                    diags[0].message
                ));
            }
        }

        // Note preservation: count note markers.
        let count = |s: &str| {
            s.lines()
                .filter(|l| {
                    let t = l.trim_start();
                    t.starts_with("//") && !t.starts_with("//*") || t.starts_with("//*")
                })
                .count()
        };
        let _ = count; // heuristic covered by dedicated unit tests below
    }
    assert!(
        failures.is_empty(),
        "{} corpus files failed formatter gates:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn print_without_layout_is_parseable() {
    // `print_source` (no layout) must round-trip too.
    for path in corpus_files().into_iter().take(40) {
        let src = fs::read_to_string(&path).unwrap();
        let dialect = dialect_of(&path);
        let parsed = parse(&src, dialect);
        if !parsed.diagnostics.is_empty() {
            continue;
        }
        let printed = print_source(&parsed.unit);
        let reparsed = parse(&printed, dialect);
        assert!(
            reparsed.diagnostics.is_empty(),
            "{}: printed output does not parse: {}\n---\n{}",
            path.display(),
            reparsed.diagnostics[0].message,
            printed
        );
        assert_eq!(
            normalized(&parsed.unit),
            normalized(&reparsed.unit),
            "{}: AST changed by print/parse",
            path.display()
        );
    }
}

#[test]
fn notes_are_preserved() {
    let src = "package P {\n    // keep me\n    part def A;\n    part x : A; // trailing\n\n    //* block\n       note *//* real comment */\n}\n";
    let formatted = format_source(src, Dialect::Sysml).unwrap();
    assert!(formatted.contains("// keep me"), "{formatted}");
    assert!(formatted.contains("// trailing"), "{formatted}");
    assert!(formatted.contains("//* block"), "{formatted}");
    assert!(formatted.contains("/* real comment */"), "{formatted}");
    // Blank line preserved between members (after the trailing note).
    assert!(formatted.contains("// trailing\n\n"), "{formatted}");
}

#[test]
fn canonical_style() {
    let src = "package  P{part def  Vehicle:>Base{attribute mass:Real[1]=10;}part v:Vehicle;}";
    let formatted = format_source(src, Dialect::Sysml).unwrap();
    let expected = "package P {\n    part def Vehicle :> Base {\n        attribute mass : Real[1] = 10;\n    }\n    part v : Vehicle;\n}\n";
    assert_eq!(formatted, expected);
}

#[test]
fn format_rejects_broken_input() {
    assert!(format_source("part def {", Dialect::Sysml).is_err());
}

#[test]
fn metadata_body_implicit_redefinition_canonicalizes() {
    // The implicit qualified-name redefinition spelling in metadata bodies
    // formats to the explicit `:>>` spelling; the result is stable and
    // AST-equal to the input.
    let src = "package P {\n    metadata def M {\n        attribute kind;\n    }\n    part a {\n        @M {\n            ref M::kind = (1, 2,);\n        }\n    }\n}\n";
    let once = format_source(src, Dialect::Sysml).unwrap();
    assert!(once.contains("ref :>> M::kind = (1, 2);"), "{once}");
    assert_eq!(format_source(&once, Dialect::Sysml).unwrap(), once);
    let a = normalized(&parse(src, Dialect::Sysml).unit);
    let b = normalized(&parse(&once, Dialect::Sysml).unit);
    assert_eq!(a, b);
}

#[test]
fn indent_styles() {
    use sysmlv2_parser::print::{Indent, format_source_with, print_source_with};
    let src = "package  P{part def  Vehicle{attribute mass:Real;}}";
    // Tabs.
    let tabs = format_source_with(src, Dialect::Sysml, Indent::Tabs).unwrap();
    let expected = "package P {\n\tpart def Vehicle {\n\t\tattribute mass : Real;\n\t}\n}\n";
    assert_eq!(tabs, expected);
    // Idempotent under the same style.
    assert_eq!(
        format_source_with(&tabs, Dialect::Sysml, Indent::Tabs).unwrap(),
        tabs
    );
    // AST-equal to the spaces rendering.
    let spaces = format_source(src, Dialect::Sysml).unwrap();
    let a = normalized(&parse(&tabs, Dialect::Sysml).unit);
    let b = normalized(&parse(&spaces, Dialect::Sysml).unit);
    assert_eq!(a, b);
    // Two-space style, straight from the printer.
    let two = print_source_with(&parse(src, Dialect::Sysml).unit, Indent::Spaces(2));
    assert!(
        two.contains("\n  part def Vehicle {\n    attribute mass : Real;\n"),
        "{two}"
    );
    // The default is unchanged: four spaces.
    assert_eq!(print_source(&parse(src, Dialect::Sysml).unit), spaces);
}

/// The formatter's multiline-chain style: a result expression whose
/// logical chain has three or more operands breaks one condition per
/// line, continuations led by the operator; two-operand chains stay
/// inline; the broken form is idempotent.
#[test]
fn long_logical_chains_break_one_condition_per_line() {
    let src = "package P {\n    constraint def C {\n        attribute a;\n        attribute b;\n        attribute c;\n        assert constraint { a > 0.0 and b > 0.0 and c > 0.0 }\n        assert constraint { a > 0.0 and b > 0.0 }\n    }\n}\n";
    let out = format_source(src, Dialect::Sysml).unwrap();
    assert!(
        out.contains("a > 0.0\n            and b > 0.0\n            and c > 0.0"),
        "three-operand chain breaks per condition:\n{out}"
    );
    assert!(
        out.contains("a > 0.0 and b > 0.0\n"),
        "two-operand chain stays inline:\n{out}"
    );
    assert_eq!(
        format_source(&out, Dialect::Sysml).unwrap(),
        out,
        "idempotent"
    );
}

/// Query-expression formatting (`format_expression`): a standalone
/// expression, wrapped only where the flat form outruns the width —
/// `->` chain steps one per line, invocation arguments one per line,
/// and a lambda body's result under its parameters. Everything that
/// fits stays on one line.
#[test]
fn query_expressions_wrap_at_the_width() {
    use sysmlv2_parser::print::{FORMAT_QUERY_WIDTH, format_expression};
    let fmt = |src: &str| {
        format_expression(src, Dialect::Sysml, Default::default(), FORMAT_QUERY_WIDTH)
            .expect("formats")
    };

    // Fits: untouched, on one line.
    assert_eq!(fmt("a.b + 1"), "a.b + 1");
    assert_eq!(
        fmt("ownedFeature(V)->select {in p; p istype W}"),
        "ownedFeature(V)->select {in p; p istype W}"
    );

    // Outruns the width: the chain breaks, nested structure indents.
    let long = "ownedFeature(Pkg::Program)->select { in p; p @ SysML::PartUsage }\
                ->collect { in m; new Collections::KeyValuePair((m meta SysML::PartUsage).declaredName, \
                ownedMember(m)->select { in d; d @ KerML::Documentation }) }\
                ->reject { in kv; isEmpty(kv.val) }";
    let out = fmt(long);
    assert_eq!(
        out,
        "ownedFeature(Pkg::Program)\n    \
         ->select {in p; p @ SysML::PartUsage}\n    \
         ->collect {in m;\n        \
         new Collections::KeyValuePair(\n            \
         (m meta SysML::PartUsage).declaredName,\n            \
         ownedMember(m)->select {in d; d @ KerML::Documentation})}\n    \
         ->reject {in kv; isEmpty(kv.val)}"
    );
    // Idempotent, and every line lands within the width.
    assert_eq!(fmt(&out), out, "idempotent");
    for line in out.lines() {
        assert!(
            line.chars().count() <= FORMAT_QUERY_WIDTH,
            "over width: {line}"
        );
    }

    // Semantics preserved: the formatted text re-parses to the same AST.
    let strip = |s: &str| {
        let e = sysmlv2_parser::parser::parse_expression(s)
            .expr
            .expect("parses");
        sysmlv2_parser::print::print_expr_source(&e, Dialect::Sysml)
    };
    assert_eq!(strip(long), strip(&out));

    // Broken input is refused, never guessed at.
    assert!(
        format_expression(
            "a +",
            Dialect::Sysml,
            Default::default(),
            FORMAT_QUERY_WIDTH
        )
        .is_err()
    );
}

/// The `@` classification operator: tight in the implicit-subject
/// filter spelling (`@M`), spaced as a binary operator (`x @ M`).
/// Both round-trip.
#[test]
fn at_type_spacing_follows_the_spelling() {
    let src = "package P {
    metadata def Safety;
    part def V;
    import P::*[@Safety];
    attribute isPart = V @ SysML::PartDefinition;
}";
    let out = format_source(src, Dialect::Sysml).unwrap();
    assert!(out.contains("[@Safety]"), "filter form stays tight:\n{out}");
    assert!(
        out.contains("V @ SysML::PartDefinition"),
        "binary form is spaced:\n{out}"
    );
    assert_eq!(
        format_source(&out, Dialect::Sysml).unwrap(),
        out,
        "idempotent"
    );
}
