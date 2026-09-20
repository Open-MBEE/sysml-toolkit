//! The option surface hosts sit on: the options builder, the spelling
//! of the option enums (parse, display, serde), and the typed error the
//! structured graph returns for a view it has no emitter for.

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_viz::{Direction, GraphError, LineStyle, View, VizOptions, graph};

#[test]
fn setters_change_one_option_each() {
    let d = VizOptions::default();
    assert_eq!(d.direction, Direction::TopToBottom);
    assert_eq!(d.view, View::Tree);
    assert_eq!(d.line_style, LineStyle::Default);
    assert!(d.show_values && d.show_notes && d.show_metadata);
    assert!(!d.show_inherited && !d.show_lib && !d.show_imported && !d.std_color);
    assert!(d.link_template.is_none() && d.roots.is_none());

    let opts = VizOptions::default()
        .with_direction(Direction::LeftToRight)
        .with_show_values(false)
        .with_view(View::Mixed)
        .with_show_notes(false)
        .with_show_metadata(false)
        .with_show_inherited(true)
        .with_show_lib(true)
        .with_show_imported(true)
        .with_line_style(LineStyle::Ortho)
        .with_std_color(true)
        .with_link_template(Some("edit://{file}".to_string()))
        .with_roots(Some(Vec::new()));
    assert_eq!(opts.direction, Direction::LeftToRight);
    assert!(!opts.show_values);
    assert_eq!(opts.view, View::Mixed);
    assert!(!opts.show_notes);
    assert!(!opts.show_metadata);
    assert!(opts.show_inherited);
    assert!(opts.show_lib);
    assert!(opts.show_imported);
    assert_eq!(opts.line_style, LineStyle::Ortho);
    assert!(opts.std_color);
    assert_eq!(opts.link_template.as_deref(), Some("edit://{file}"));
    assert_eq!(opts.roots.as_deref(), Some(&[][..]));
}

/// Every view round-trips through its canonical spelling, and the two
/// shorthands hosts accept parse to the same views.
#[test]
fn view_spellings_round_trip() {
    let all = [
        (View::Tree, "tree"),
        (View::Interconnection, "interconnection"),
        (View::State, "state"),
        (View::Action, "action"),
        (View::Sequence, "sequence"),
        (View::Case, "case"),
        (View::Mixed, "mixed"),
    ];
    for (view, spelling) in all {
        assert_eq!(view.as_str(), spelling);
        assert_eq!(view.to_string(), spelling);
        assert_eq!(spelling.parse::<View>().unwrap(), view);
        assert_eq!(
            serde_json::to_string(&view).unwrap(),
            format!("\"{spelling}\"")
        );
        assert_eq!(
            serde_json::from_str::<View>(&format!("\"{spelling}\"")).unwrap(),
            view
        );
    }
    for (short, view) in [("ic", View::Interconnection), ("seq", View::Sequence)] {
        assert_eq!(short.parse::<View>().unwrap(), view);
        assert_eq!(
            serde_json::from_str::<View>(&format!("\"{short}\"")).unwrap(),
            view
        );
    }
}

#[test]
fn line_style_spellings_round_trip() {
    for (style, spelling) in [
        (LineStyle::Default, "default"),
        (LineStyle::Polyline, "polyline"),
        (LineStyle::Ortho, "ortho"),
    ] {
        assert_eq!(style.as_str(), spelling);
        assert_eq!(style.to_string(), spelling);
        assert_eq!(spelling.parse::<LineStyle>().unwrap(), style);
        assert_eq!(
            serde_json::to_string(&style).unwrap(),
            format!("\"{spelling}\"")
        );
        assert_eq!(
            serde_json::from_str::<LineStyle>(&format!("\"{spelling}\"")).unwrap(),
            style
        );
    }
}

/// A spelling that names nothing says what was named and what it could
/// have been.
#[test]
fn unknown_spellings_report_the_alternatives() {
    let e = "treee".parse::<View>().unwrap_err();
    assert_eq!(e.option(), "view");
    assert_eq!(e.spelling(), "treee");
    assert_eq!(e.expected().first(), Some(&"tree"));
    assert_eq!(
        e.to_string(),
        "unknown view: treee (expected tree, interconnection, state, action, sequence, case, or mixed)"
    );

    let e = "dotted".parse::<LineStyle>().unwrap_err();
    assert_eq!(e.option(), "line style");
    assert_eq!(
        e.to_string(),
        "unknown line style: dotted (expected default, polyline, or ortho)"
    );
}

/// The structured graph names the view it cannot draw, and the views it
/// can draw label their output with the same spelling.
#[test]
fn graph_reports_the_view_it_cannot_draw() {
    let mut model = Model::new();
    model.add_source("p.sysml".to_string(), "package P { part def A; }\n");
    let mut r = ResolvedModel::build(&model);

    for view in [View::Tree, View::Interconnection, View::State, View::Action] {
        let g = graph(&mut r, None, &VizOptions::default().with_view(view)).unwrap();
        assert_eq!(g["view"].as_str(), Some(view.as_str()));
    }

    for view in [View::Sequence, View::Case, View::Mixed] {
        let e = graph(&mut r, None, &VizOptions::default().with_view(view)).unwrap_err();
        assert_eq!(e, GraphError::UnsupportedView(view));
        assert_eq!(
            e.to_string(),
            format!("no structured-graph emitter for view: {view}")
        );
    }
}
