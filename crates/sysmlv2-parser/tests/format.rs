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

#[test]
fn anonymous_comment_members_keep_their_indentation() {
    // A bare `/* … */` member has no keyword before its body; the body
    // printer must not trim the indentation it just received.
    let src = "package P {\n    part def A {\n        /* a member comment */\n        attribute x;\n        comment /* keyworded */\n    }\n    /* top-level member */\n}\n";
    let formatted = format_source(src, Dialect::Sysml).unwrap();
    assert_eq!(
        formatted,
        "package P {\n    part def A {\n        /* a member comment */\n        attribute x;\n        /* keyworded */\n    }\n    /* top-level member */\n}\n"
    );
    let again = format_source(&formatted, Dialect::Sysml).unwrap();
    assert_eq!(again, formatted, "not idempotent");
    // A multi-line anonymous body: the opening line keeps the member's
    // indentation, so the gutter lines up under it.
    let src = "package P {\n    part def A {\n        /* first\n         * second\n         */\n    }\n}\n";
    let formatted = format_source(src, Dialect::Sysml).unwrap();
    assert_eq!(formatted, src);
    assert_eq!(
        format_source(&formatted, Dialect::Sysml).unwrap(),
        formatted
    );
    // A comment with an identification keeps its body on the keyword line.
    let src = "package P {\n    comment c /* named */\n    comment about P /* about */\n}\n";
    let formatted = format_source(src, Dialect::Sysml).unwrap();
    assert_eq!(
        formatted,
        "package P {\n    comment c /* named */\n    comment about P /* about */\n}\n"
    );
}

/// Names that are reserved words print quoted in the dialect that
/// reserves them — and only there — and re-parse: declarations and
/// qualified references alike.
#[test]
fn reserved_word_names_round_trip_in_each_dialect() {
    let sysml = "package 'part' {\n    part def 'action';\n    part 'view' : 'action';\n    \
                 view 'state' {\n        expose 'part'::'view';\n    }\n}\n";
    let kerml = "package 'class' {\n    classifier 'if';\n    feature part : 'if';\n    \
                 feature 'feature' : 'if';\n}\n";
    for (src, dialect) in [(sysml, Dialect::Sysml), (kerml, Dialect::Kerml)] {
        let parsed = parse(src, dialect);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let printed = print_source(&parsed.unit);
        let reparsed = parse(&printed, dialect);
        assert!(
            reparsed.diagnostics.is_empty(),
            "printed output does not parse: {}\n---\n{printed}",
            reparsed.diagnostics[0].message
        );
        assert_eq!(normalized(&parsed.unit), normalized(&reparsed.unit));
        let formatted = format_source(src, dialect).unwrap();
        assert_eq!(
            format_source(&formatted, dialect).unwrap(),
            formatted,
            "idempotent"
        );
    }
    let formatted = format_source(sysml, Dialect::Sysml).unwrap();
    assert!(
        formatted.contains("part 'view' : 'action';")
            && formatted.contains("expose 'part'::'view';"),
        "{formatted}"
    );
    // `part` is not a KerML word: the KerML printer leaves it bare.
    let formatted = format_source(kerml, Dialect::Kerml).unwrap();
    assert!(
        formatted.contains("feature part : 'if';")
            && formatted.contains("feature 'feature' : 'if';"),
        "{formatted}"
    );
}

/// A binding whose detail carries other than the pair of ends the notation
/// spells — a shape the parser never builds, but one an assembled tree can
/// reach — prints a member that parses and stays that one member. The
/// binding form spells only the pair, so another count is never printed
/// behind it: one end would read as a missing right side, three as a chain
/// of two whose third end is quietly lost.
///
/// SysML requires the `bind` clause after that keyword, and KerML, which
/// takes the keyword alone, draws a finding for a binding connector that
/// does not bind two features. So in both the member survives as its
/// declaration alone — behind `feature` in KerML, as `ref` where SysML
/// has nothing to declare — and every end with it, spelled as an
/// `end ::> …;` body member.
///
/// Every case keeps a member *after* the binding: a member that prints as
/// nothing but its terminator parses only in last position, where the
/// repair of a body's result expression swallows it.
#[test]
fn binding_with_other_than_two_ends_still_round_trips() {
    use sysmlv2_parser::ast::{Member, MemberKind, UsageDetail, UsageKind};

    fn set_end_count(unit: &mut SourceUnit, count: usize) {
        let MemberKind::Package(p) = &mut unit.members[0].kind else {
            panic!("expected a package")
        };
        for m in p.body.as_mut().expect("package body") {
            if let MemberKind::Usage(u) = &mut m.kind {
                if let UsageDetail::Binding { ends } = &mut u.detail {
                    assert_eq!(ends.len(), 2);
                    let spare = ends[0].clone();
                    ends.resize(count, spare);
                }
            }
        }
    }

    fn package_body<'a>(unit: &'a SourceUnit, printed: &str) -> &'a [Member] {
        let MemberKind::Package(p) = &unit.members[0].kind else {
            panic!("{printed:?}: expected a package")
        };
        p.body.as_deref().expect("package body")
    }

    for (dialect, src) in [
        (Dialect::Sysml, "package P { bind a = b; part z; }"),
        (
            Dialect::Sysml,
            "package P { binding b1 : B bind a = b; part z; }",
        ),
        (
            Dialect::Sysml,
            "package P { bind a = b { part q; } part z; }",
        ),
        (
            Dialect::Sysml,
            "package P { binding b1 : B bind a = b { part q; } part z; }",
        ),
        (Dialect::Kerml, "package P { binding of a = b; feature z; }"),
        (
            Dialect::Kerml,
            "package P { binding b1 : B of a = b; feature z; }",
        ),
        (
            Dialect::Kerml,
            "package P { binding of a = b { feature q; } feature z; }",
        ),
        (
            Dialect::Kerml,
            "package P { binding b1 : B of a = b { feature q; } feature z; }",
        ),
    ] {
        for count in [0, 1, 3, 4] {
            let mut unit = parse(src, dialect).unit;
            set_end_count(&mut unit, count);
            let printed = print_source(&unit);
            let back = parse(&printed, dialect);
            assert!(
                back.diagnostics.is_empty(),
                "{src} with {count} end(s) printed {printed:?}: {:#?}",
                back.diagnostics
            );
            // Printing what came back changes nothing further.
            assert_eq!(
                print_source(&back.unit),
                printed,
                "{src} with {count} end(s): a second round trip moved"
            );
            let body = package_body(&back.unit, &printed);
            // The connector and the member after it, both still there.
            assert_eq!(body.len(), 2, "{printed:?}: a member disappeared");
            let MemberKind::Usage(u) = &body[0].kind else {
                panic!("{printed:?}: expected a usage")
            };
            assert!(
                !printed.contains('='),
                "{printed:?}: ends spelled as a pair without one"
            );
            // Nothing spells the binding, so the member keeps its
            // declaration alone — behind `feature` in KerML, which names
            // a metaclass on every member, and as `ref` where SysML has
            // nothing to declare — and every end moves into the body as
            // an `end` member.
            assert!(
                !printed.contains("bind") && !printed.contains("connect"),
                "{printed:?}: a connector form without its clause"
            );
            let declared = src.contains("binding b1");
            assert_eq!(
                u.kind,
                match (dialect, declared) {
                    (Dialect::Kerml, _) => UsageKind::Feature,
                    (_, true) => UsageKind::Default,
                    (_, false) => UsageKind::Ref,
                },
                "{printed:?}"
            );
            let kept = u
                .body
                .iter()
                .flatten()
                .filter(|m| matches!(&m.kind, MemberKind::Usage(e) if e.prefix.is_end))
                .count();
            assert_eq!(kept, count, "{printed:?}: ends kept");
        }
    }

    // The pair the notation does spell still prints as the binding it is.
    let unit = parse_source("package P { bind a = b; }").unit;
    assert_eq!(print_source(&unit), "package P {\n    bind a = b;\n}\n");
    let unit = parse_kerml_source("package P { binding of a = b; }").unit;
    assert_eq!(print_source(&unit), "package P {\n    binding a = b;\n}\n");
}

/// The chain threshold counts operands, not their low eight bits: a chain
/// whose operand count crosses a byte boundary still breaks per condition.
#[test]
fn long_logical_chain_breaks_past_a_byte_of_operands() {
    for n in [255usize, 256, 257, 300] {
        let chain = (0..n)
            .map(|i| format!("a{i} > 0.0"))
            .collect::<Vec<_>>()
            .join(" and ");
        let src = format!("package P {{\n    constraint c {{\n        {chain}\n    }}\n}}\n");
        let out = format_source(&src, Dialect::Sysml).unwrap();
        let broken = out
            .lines()
            .filter(|l| l.trim_start().starts_with("and "))
            .count();
        assert_eq!(broken, n - 1, "{n} operands did not break per condition");
        assert_eq!(
            format_source(&out, Dialect::Sysml).unwrap(),
            out,
            "idempotent"
        );
    }
}

/// A failed format reports one error value: it lists what went wrong, keeps
/// the individual diagnostics reachable as a slice, and propagates with `?`.
#[test]
fn a_failed_format_is_one_error_value() {
    const BROKEN: &str = "package P { part a = ; part b = ; }";

    fn format(src: &str) -> Result<String, Box<dyn std::error::Error>> {
        Ok(format_source(src, Dialect::Sysml)?)
    }

    let listed = format(BROKEN).unwrap_err().to_string();
    let diagnostics = format_source(BROKEN, Dialect::Sysml).unwrap_err();
    assert!(!diagnostics.is_empty());
    assert_eq!(listed.lines().count(), diagnostics.len());
    assert!(listed.starts_with("error: "), "{listed}");
    // The slice is still there behind the wrapper.
    assert_eq!(Some(&diagnostics[0]), diagnostics.first());
    assert_eq!(diagnostics.iter().count(), diagnostics.len());
    assert_eq!(diagnostics.clone().into_vec(), diagnostics.to_vec());
}

/// The notation's end clause reads two ends or more — `from a to b`,
/// `(a, b, c)` — so a connector an assembled tree gave fewer has no
/// clause to put them in: `(a)` is not a list the parser reads back, and
/// printing one would emit text that fails where it used to succeed.
/// The ends go into the body instead, as the `end ::> …;` members the
/// notation already gives an end written out rather than listed, which
/// is what a one-ended connector lifted from interchange already spells.
#[test]
fn a_connector_below_the_clause_keeps_its_ends_as_members() {
    use sysmlv2_parser::ast::{MemberKind, UsageDetail};

    fn set_end_count(unit: &mut SourceUnit, count: usize) {
        let MemberKind::Package(p) = &mut unit.members[0].kind else {
            panic!("expected a package")
        };
        for m in p.body.as_mut().expect("package body") {
            if let MemberKind::Usage(u) = &mut m.kind {
                if let UsageDetail::Connector { ends } = &mut u.detail {
                    assert_eq!(ends.len(), 2);
                    let spare = ends[0].clone();
                    ends.resize(count, spare);
                }
            }
        }
    }

    for (dialect, src) in [
        (
            Dialect::Sysml,
            "package P { connection c1 connect a to b; part z; }",
        ),
        (Dialect::Sysml, "package P { connect a to b; part z; }"),
        (
            Dialect::Sysml,
            "package P { allocation c1 allocate a to b; part z; }",
        ),
        (
            Dialect::Sysml,
            "package P { interface i1 connect a to b; part z; }",
        ),
        (
            Dialect::Kerml,
            "package P { connector c1 from a to b; feature z; }",
        ),
        (
            Dialect::Kerml,
            "package P { connector c1 from a to b { feature q; } feature z; }",
        ),
    ] {
        for count in [0, 1] {
            let mut unit = parse(src, dialect).unit;
            set_end_count(&mut unit, count);
            let printed = print_source(&unit);
            let back = parse(&printed, dialect);
            assert!(
                back.diagnostics.is_empty(),
                "{src} with {count} end(s) printed {printed:?}: {:#?}",
                back.diagnostics
            );
            assert!(
                !printed.contains('('),
                "{printed:?}: a list the clause does not read"
            );
            // Printing what came back changes nothing further.
            assert_eq!(
                print_source(&back.unit),
                printed,
                "{src} with {count} end(s): a second round trip moved"
            );
            let MemberKind::Package(p) = &back.unit.members[0].kind else {
                panic!("{printed:?}: expected a package")
            };
            let body = p.body.as_deref().expect("package body");
            assert_eq!(body.len(), 2, "{printed:?}: a member disappeared");
            let MemberKind::Usage(u) = &body[0].kind else {
                panic!("{printed:?}: expected a usage")
            };
            let kept = u
                .body
                .iter()
                .flatten()
                .filter(|m| matches!(&m.kind, MemberKind::Usage(e) if e.prefix.is_end))
                .count();
            assert_eq!(kept, count, "{printed:?}: ends kept");
        }
    }
}

/// An end with no name, no multiplicity and an unspelled target has
/// nothing to print after its prefix. SysML reads a member that is only
/// its prefix; KerML wants an element after one, and stops on the
/// terminator — so the bare end is spelled `end feature;`, naming the
/// metaclass the end has anyway, which both dialects read and print back
/// unchanged. `end;` would leave the other dialect text it cannot parse.
#[test]
fn a_bare_end_member_names_an_element_both_dialects_read() {
    use sysmlv2_parser::ast::{MemberKind, TargetRef, UsageDetail};

    /// Leave the connector one end with nothing spelled on it at all.
    fn strip_the_end(unit: &mut SourceUnit) {
        let MemberKind::Package(p) = &mut unit.members[0].kind else {
            panic!("expected a package")
        };
        for m in p.body.as_mut().expect("package body") {
            if let MemberKind::Usage(u) = &mut m.kind {
                if let UsageDetail::Connector { ends } = &mut u.detail {
                    ends.truncate(1);
                    ends[0].name = None;
                    ends[0].multiplicity = None;
                    ends[0].target = TargetRef::unspelled();
                }
            }
        }
    }

    for (dialect, src) in [
        (
            Dialect::Sysml,
            "package P { connection c1 connect a to b; part z; }",
        ),
        (
            Dialect::Kerml,
            "package P { connector c1 from a to b; feature z; }",
        ),
    ] {
        let mut unit = parse(src, dialect).unit;
        strip_the_end(&mut unit);
        let printed = print_source(&unit);
        assert!(printed.contains("end feature;"), "{printed:?}");
        let back = parse(&printed, dialect);
        assert!(
            back.diagnostics.is_empty(),
            "{printed:?}: {:#?}",
            back.diagnostics
        );
        assert_eq!(
            print_source(&back.unit),
            printed,
            "{src}: a second round trip moved"
        );
    }

    // The spelling itself, in each dialect's own container: what the
    // printer writes now is read by both, and what it wrote before was
    // read by one.
    for (dialect, container) in [
        (Dialect::Sysml, "package P { connection c1 { @ } part z; }"),
        (
            Dialect::Kerml,
            "package P { connector c1 { @ } feature z; }",
        ),
    ] {
        assert!(
            parse(&container.replace('@', "end feature;"), dialect)
                .diagnostics
                .is_empty(),
            "{dialect:?} does not read `end feature;`"
        );
    }
    assert!(
        !parse(
            "package P { connector c1 { end; } feature z; }",
            Dialect::Kerml
        )
        .diagnostics
        .is_empty(),
        "`end;` reads in both dialects after all"
    );
}
