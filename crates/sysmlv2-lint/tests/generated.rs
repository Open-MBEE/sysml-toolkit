//! Generated-element guard gates: the six drift
//! classes classify distinctly, every ownership-corruption shape is
//! found, and clean models stay silent.

use sysmlv2_lint::{
    Config, Finding, Severity, canonical_member_text, canonicalization_digest, generated_inventory,
    lint_units,
};
use sysmlv2_model::structure::{member_structure_digest, sha256_hex};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

const META: &str = "library package TransformMeta {
\tmetadata def Generated;
\tmetadata def ProvenanceStore;
\tmetadata def TransformState {
\t\tattribute transformId;
\t\tattribute transformerPath;
\t\tattribute scriptDigest;
\t\tattribute forcedSchemaDrift;
\t}
\tmetadata def TransformSource {
\t\tattribute sourceAlias;
\t\tattribute sourceRef;
\t\tattribute inputDigest;
\t\tattribute rowCount;
\t}
\tmetadata def TransformProvenance {
\t\tattribute transformId;
\t\tattribute key;
\t\tattribute rowDigest;
\t\tattribute spellingDigest;
\t\tattribute structureDigest;
\t\tattribute policyDigest;
\t}
\tmetadata def TransformExclusion {
\t\tattribute transformId;
\t\tattribute key;
\t\tattribute source;
\t\tattribute transformerPath;
\t}
}
";

/// The generated member in top-level (canonical) form.
const MEMBER: &str =
    "#TransformMeta::Generated part def <'R-1'> beam {\n\tdoc /* emits the beam */\n}";

fn run(sources: &[(&str, &str)], config: &Config) -> Vec<Finding> {
    let mut model = Model::new();
    for (name, src) in sources {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let units: Vec<(usize, &str, &str)> = sources
        .iter()
        .enumerate()
        .map(|(i, (name, text))| (i, *name, *text))
        .collect();
    lint_units(&mut resolved, config, &units)
}

fn guard_findings(sources: &[(&str, &str)], config: &Config) -> Vec<Finding> {
    run(sources, config)
        .into_iter()
        .filter(|f| f.rule.starts_with("generated-"))
        .collect()
}

struct Baseline {
    text_digest: String,
    structure_digest: String,
    policy: String,
}

fn baseline(member: &str, config: &Config) -> Baseline {
    let canonical = canonical_member_text(member, config).expect("member formats");
    Baseline {
        text_digest: format!("sha256:{}", sha256_hex(canonical.as_bytes())),
        structure_digest: member_structure_digest(member).expect("member parses"),
        policy: canonicalization_digest(config),
    }
}

/// The engine spelling of `member` at one tab of depth.
fn indented(member: &str) -> String {
    member
        .split('\n')
        .map(|l| {
            if l.is_empty() {
                String::new()
            } else {
                format!("\t{l}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn content_unit(member_in_unit: &str) -> String {
    format!("package Flashlight {{\n{member_in_unit}\n}}\n")
}

/// The per-transformer state record (AA7h0) every managed record in
/// these fixtures resolves through.
fn state_record() -> String {
    "\tmetadata <'sync/@state'> s_sync : TransformMeta::TransformState {\n\
     \t\ttransformId = \"sync\";\n\
     \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
     \t\tscriptDigest = \"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\";\n\
     \t\tmetadata src0 : TransformMeta::TransformSource {\n\
     \t\t\tsourceAlias = \"source\";\n\
     \t\t\tsourceRef = \"reqs.csv\";\n\
     \t\t\tinputDigest = \"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\";\n\
     \t\t\trowCount = 11;\n\
     \t\t}\n\
     \t}\n"
        .to_string()
}

fn sidecar(record_fields: &str) -> String {
    format!(
        "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n\
         {state}\
         \tmetadata <'sync/R-1'> p_r1 : TransformMeta::TransformProvenance about Flashlight::beam {{\n\
         {record_fields}\
         \t}}\n\
         }}\n",
        state = state_record()
    )
}

fn fields(b: &Baseline, with_baseline: bool) -> String {
    let mut out = String::new();
    out.push_str("\t\ttransformId = \"sync\";\n");
    out.push_str("\t\tkey = \"R-1\";\n");
    out.push_str(&format!("\t\tspellingDigest = \"{}\";\n", b.text_digest));
    if with_baseline {
        out.push_str(&format!(
            "\t\tstructureDigest = \"{}\";\n",
            b.structure_digest
        ));
        out.push_str(&format!("\t\tpolicyDigest = \"{}\";\n", b.policy));
    }
    out
}

fn fixture(member_in_unit: &str, record_fields: &str) -> Vec<(String, String)> {
    vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(member_in_unit)),
        ("m.provenance.sysml".to_string(), sidecar(record_fields)),
    ]
}

fn borrow(sources: &[(String, String)]) -> Vec<(&str, &str)> {
    sources
        .iter()
        .map(|(n, t)| (n.as_str(), t.as_str()))
        .collect()
}

#[test]
fn clean_pair_is_silent() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let sources = fixture(&indented(MEMBER), &fields(&b, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn format_only_drift_classifies_as_formatting() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    // Same structure and canonical bytes, mangled spelling in place.
    let mangled = indented(MEMBER).replace("\tdoc", "   doc");
    let sources = fixture(&mangled, &fields(&b, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-element-modified");
    assert!(
        findings[0].message.contains("formatting drifted"),
        "{}",
        findings[0].message
    );
    assert_eq!(findings[0].severity, Severity::Warn);
}

#[test]
fn semantic_drift_classifies_as_modified() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let edited = indented(MEMBER).replace("emits the beam", "emits the modified beam");
    let sources = fixture(&edited, &fields(&b, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-element-modified");
    assert!(
        findings[0].message.contains("structure differs"),
        "{}",
        findings[0].message
    );
    assert!(
        findings[0].message.contains("reqs.csv"),
        "{}",
        findings[0].message
    );
}

#[test]
fn policy_change_is_baseline_drift_not_tamper() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let stale = Baseline {
        policy: format!("sha256:{}", "0".repeat(64)),
        ..b
    };
    let sources = fixture(&indented(MEMBER), &fields(&stale, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-element-modified");
    assert!(
        findings[0].message.contains("policy changed"),
        "{}",
        findings[0].message
    );
}

#[test]
fn legacy_records_read_as_outdated_baseline() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let sources = fixture(&indented(MEMBER), &fields(&b, false));
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-provenance-baseline-outdated");
    assert_eq!(findings[0].severity, Severity::Info);
}

#[test]
fn corrupt_baseline_joins_the_integrity_rule() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let corrupt = Baseline {
        text_digest: format!("sha256:{}", "f".repeat(64)),
        ..b
    };
    let sources = fixture(&indented(MEMBER), &fields(&corrupt, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-provenance-invalid");
    assert!(
        findings[0].message.contains("corrupt baseline"),
        "{}",
        findings[0].message
    );
    assert_eq!(findings[0].severity, Severity::Error);
}

#[test]
fn malformed_digest_is_corruption() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let bad = Baseline {
        structure_digest: "sha256:nothex".to_string(),
        ..b
    };
    let sources = fixture(&indented(MEMBER), &fields(&bad, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("malformed structureDigest")),
        "{findings:?}"
    );
}

#[test]
fn marker_only_member_is_ownership_corruption() {
    let config = Config::default();
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "generated-provenance-invalid");
    assert!(
        findings[0].message.contains("no provenance record"),
        "{}",
        findings[0].message
    );
}

#[test]
fn unmarked_target_and_wrong_key_are_corruption() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    // Unmarked: the member lost its #Generated marker.
    let unmarked = indented(MEMBER).replace("#TransformMeta::Generated ", "");
    let sources = fixture(&unmarked, &fields(&b, true));
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("does not carry the Generated marker")),
        "{findings:?}"
    );

    // Wrong key: the record claims R-2 but annotates <'R-1'>.
    let wrong = fields(&b, true).replace("key = \"R-1\"", "key = \"R-2\"");
    let sources = fixture(&indented(MEMBER), &wrong);
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("whose short name is")),
        "{findings:?}"
    );
}

#[test]
fn duplicate_and_contradictory_claims_are_corruption() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let f = fields(&b, true);
    // Two provenance records for one pair.
    let two = format!(
        "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n\
         \tmetadata <'sync/R-1'> p_a : TransformMeta::TransformProvenance about Flashlight::beam {{\n{f}\t}}\n\
         \tmetadata p_b : TransformMeta::TransformProvenance about Flashlight::beam {{\n{f}\t}}\n\
         }}\n"
    );
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), two),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("duplicate provenance claims")),
        "{findings:?}"
    );

    // A provenance record and an exclusion for the same pair.
    let both = format!(
        "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n\
         \tmetadata <'sync/R-1'> p_a : TransformMeta::TransformProvenance about Flashlight::beam {{\n{f}\t}}\n\
         \tmetadata x_a : TransformMeta::TransformExclusion {{\n\
         \t\ttransformId = \"sync\";\n\t\tkey = \"R-1\";\n\
         \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tmetadata source0 : TransformMeta::TransformSource {{\n\
         \t\t\tsourceAlias = \"source\";\n\t\t\tsourceRef = \"reqs.csv\";\n\
         \t\t\tinputDigest = \"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\";\n\t\t}}\n\t}}\n\
         }}\n"
    );
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), both),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings.iter().any(|f| f
            .message
            .contains("both a provenance record and an exclusion")),
        "{findings:?}"
    );
}

#[test]
fn different_transformers_cannot_claim_the_same_member() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let a = fields(&b, true);
    let b_fields = a.replace("transformId = \"sync\"", "transformId = \"other\"");
    let two = format!(
        "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n\
         \tmetadata p_a : TransformMeta::TransformProvenance about Flashlight::beam {{\n{a}\t}}\n\
         \tmetadata p_b : TransformMeta::TransformProvenance about Flashlight::beam {{\n{b_fields}\t}}\n\
         }}\n"
    );
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), two),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("claimed by multiple provenance records")),
        "{findings:?}"
    );
}

#[test]
fn record_target_must_belong_to_the_store_package() {
    let config = Config::default();
    let other_member = MEMBER.replace("beam", "otherBeam").replace("R-1", "R-2");
    let b = baseline(&other_member, &config);
    let record = sidecar(&fields(&b, true).replace("R-1", "R-2"))
        .replace("about Flashlight::beam", "about Other::otherBeam");
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        (
            "m.sysml".to_string(),
            format!(
                "package Flashlight {{\n\tpart def Body;\n}}\npackage Other {{\n{}\n}}\n",
                indented(&other_member)
            ),
        ),
        ("m.provenance.sysml".to_string(), record),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("outside its store package")),
        "{findings:?}"
    );
}

#[test]
fn store_outside_its_derived_sidecar_is_corruption() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    // The store rides a wrong unit name.
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        (
            "other.provenance.sysml".to_string(),
            sidecar(&fields(&b, true)),
        ),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("derived sidecar")),
        "{findings:?}"
    );

    // Legacy in-target store: not top-level, unkeyed.
    let legacy = format!(
        "package Flashlight {{\n{member}\n\
         \t#TransformMeta::ProvenanceStore package <'AA-PROVENANCE'> oldProv {{\n\
         \t\tmetadata <'sync/R-1'> p_a : TransformMeta::TransformProvenance about beam {{\n\
         {f}\t\t}}\n\
         \t}}\n}}\n",
        member = indented(MEMBER),
        f = fields(&b, true).replace("\t\t", "\t\t\t"),
    );
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), legacy),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("not a top-level member")),
        "{findings:?}"
    );
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "generated-provenance-invalid"
                && f.message.contains("short-name key")),
        "{findings:?}"
    );
}

#[test]
fn exclusion_targeting_a_marked_member_is_corruption() {
    let config = Config::default();
    let excl = "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {\n\
         \tmetadata x_a : TransformMeta::TransformExclusion about Flashlight::beam {\n\
         \t\ttransformId = \"sync\";\n\t\tkey = \"R-1\";\n\
         \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tmetadata source0 : TransformMeta::TransformSource {\n\
         \t\t\tsourceAlias = \"reqs\";\n\t\t\tsourceRef = \"reqs.csv\";\n\
         \t\t\tinputDigest = \"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\";\n\t\t}\n\
         \t\tmetadata source1 : TransformMeta::TransformSource {\n\
         \t\t\tsourceAlias = \"owners\";\n\t\t\tsourceRef = \"db:app#owners\";\n\
         \t\t\tinputDigest = \"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\";\n\t\t}\n\t}\n\
         }\n";
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), excl.to_string()),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("still carrying the Generated marker")),
        "{findings:?}"
    );
    // The marked member itself is also unclaimed by any provenance.
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("no provenance record")),
        "{findings:?}"
    );
}

#[test]
fn targetless_exclusion_tombstone_is_legal() {
    let config = Config::default();
    let excl = "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {\n\
         \tmetadata x_a : TransformMeta::TransformExclusion {\n\
         \t\ttransformId = \"sync\";\n\t\tkey = \"R-9\";\n\
         \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tmetadata source0 : TransformMeta::TransformSource {\n\
         \t\t\tsourceAlias = \"source\";\n\t\t\tsourceRef = \"reqs.csv\";\n\
         \t\t\tinputDigest = \"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\";\n\t\t}\n\
         \t\tmetadata source1 : TransformMeta::TransformSource {\n\
         \t\t\tsourceAlias = \"owners\";\n\t\t\tsourceRef = \"db:app#owners\";\n\
         \t\t\tinputDigest = \"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\";\n\t\t}\n\t}\n\
         }\n";
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        (
            "m.sysml".to_string(),
            "package Flashlight {\n\tpart def Body;\n}\n".to_string(),
        ),
        ("m.provenance.sysml".to_string(), excl.to_string()),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(findings.is_empty(), "{findings:?}");
    let inventory = inventory_of(&borrow(&sources));
    assert_eq!(inventory.tombstones.len(), 1);
    assert_eq!(inventory.tombstones[0].sources.len(), 2);
    assert_eq!(inventory.tombstones[0].sources[0].source_ref, "reqs.csv");
    assert_eq!(
        inventory.tombstones[0].sources[1].source_ref,
        "db:app#owners"
    );
}

#[test]
fn exclusion_cannot_target_multiple_members() {
    let config = Config::default();
    let excl = "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {\n\
         \tmetadata x_a : TransformMeta::TransformExclusion about Flashlight::a, Flashlight::b {\n\
         \t\ttransformId = \"sync\";\n\t\tkey = \"R-9\";\n\
         \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tmetadata source0 : TransformMeta::TransformSource {\n\
         \t\t\tsourceAlias = \"source\";\n\t\t\tsourceRef = \"reqs.csv\";\n\
         \t\t\tinputDigest = \"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\";\n\t\t}\n\t}\n\
         }\n";
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        (
            "m.sysml".to_string(),
            "package Flashlight {\n\tpart def a;\n\tpart def b;\n}\n".to_string(),
        ),
        ("m.provenance.sysml".to_string(), excl.to_string()),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("at most one adopted member")),
        "{findings:?}"
    );
}

#[test]
fn canonicalization_fingerprint_tracks_only_fix_effective_contexts() {
    let base = canonicalization_digest(&Config::default());
    let attribute_fix =
        Config::from_json(r#"{"rules":{"untyped-usage":{"scopes":{"AttributeUsage":"warn"}}}}"#)
            .unwrap();
    assert_ne!(base, canonicalization_digest(&attribute_fix));

    let non_fix_scope =
        Config::from_json(r#"{"rules":{"untyped-usage":{"scopes":{"PartUsage":"warn"}}}}"#)
            .unwrap();
    assert_eq!(base, canonicalization_digest(&non_fix_scope));

    let dimension_scope =
        Config::from_json(r#"{"rules":{"dimensional-consistency":{"scopes":{"untyped":"off"}}}}"#)
            .unwrap();
    assert_ne!(base, canonicalization_digest(&dimension_scope));

    let unrelated = Config::from_json(r#"{"rules":{"naming-convention":"error"}}"#).unwrap();
    assert_eq!(base, canonicalization_digest(&unrelated));
}

#[test]
fn native_inventory_omits_invalid_sidecars_and_ambiguous_owners() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let sources = fixture(&indented(MEMBER), &fields(&b, true));
    let borrowed = borrow(&sources);
    let mut model = Model::new();
    for (name, src) in &borrowed {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let units: Vec<_> = borrowed
        .iter()
        .enumerate()
        .map(|(i, (name, text))| (i, *name, *text))
        .collect();
    let inventory = generated_inventory(&mut resolved, &units);
    assert_eq!(inventory.members.len(), 1);

    let mut wrong = sources.clone();
    wrong[2].0 = "wrong.provenance.sysml".to_string();
    let borrowed = borrow(&wrong);
    let mut model = Model::new();
    for (name, src) in &borrowed {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let units: Vec<_> = borrowed
        .iter()
        .enumerate()
        .map(|(i, (name, text))| (i, *name, *text))
        .collect();
    assert!(
        generated_inventory(&mut resolved, &units)
            .members
            .is_empty()
    );
}

#[test]
fn nameless_hosts_get_a_note_not_silence() {
    // Only an explicitly configured rule complains; the defaults skip
    // silently on nameless hosts.
    let config =
        Config::from_json(r#"{ "rules": { "generated-element-modified": "error" } }"#).unwrap();
    let b = baseline(MEMBER, &config);
    let sources = fixture(&indented(MEMBER), &fields(&b, true));
    let borrowed = borrow(&sources);
    let mut model = Model::new();
    for (name, src) in &borrowed {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let nameless: Vec<(usize, &str, &str)> = borrowed
        .iter()
        .enumerate()
        .map(|(i, (_, text))| (i, "", *text))
        .collect();
    let findings = lint_units(&mut resolved, &config, &nameless);
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "lint-config" && f.message.contains("unit names")),
        "{findings:?}"
    );
}

// ---- AA7h0: the per-transformer state record ----

fn inventory_of(sources: &[(&str, &str)]) -> sysmlv2_lint::GeneratedInventory {
    let mut model = Model::new();
    for (name, src) in sources {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let units: Vec<(usize, &str, &str)> = sources
        .iter()
        .enumerate()
        .map(|(i, (name, text))| (i, *name, *text))
        .collect();
    generated_inventory(&mut resolved, &units)
}

/// A sidecar with an arbitrary store body (state + records spelled by
/// the caller).
fn sidecar_body(body: &str) -> String {
    format!(
        "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n{body}}}\n"
    )
}

fn record_r1(b: &Baseline) -> String {
    format!(
        "\tmetadata <'sync/R-1'> p_r1 : TransformMeta::TransformProvenance about Flashlight::beam {{\n{}\t}}\n",
        fields(b, true)
    )
}

#[test]
fn managed_records_without_state_are_corruption_and_emit_no_rows() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        (
            "m.provenance.sysml".to_string(),
            sidecar_body(&record_r1(&b)),
        ),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("no TransformState record")),
        "{findings:?}"
    );
    let inventory = inventory_of(&borrow(&sources));
    assert!(inventory.members.is_empty(), "rows must be omitted");
    assert!(inventory.states.is_empty());
}

#[test]
fn duplicate_states_are_corruption_and_emit_no_rows() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let body = format!("{}{}{}", state_record(), state_record(), record_r1(&b));
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), sidecar_body(&body)),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("duplicate TransformState")),
        "{findings:?}"
    );
    let inventory = inventory_of(&borrow(&sources));
    assert!(inventory.members.is_empty(), "rows must be omitted");
    assert!(
        inventory.states.is_empty(),
        "no surface row under duplicates"
    );
}

#[test]
fn orphan_state_is_named() {
    let config = Config::default();
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit("\tpart def hand;")),
        (
            "m.provenance.sysml".to_string(),
            sidecar_body(&state_record()),
        ),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|f| f.message.contains("no managed provenance records")),
        "{findings:?}"
    );
    let inventory = inventory_of(&borrow(&sources));
    assert!(inventory.states.is_empty(), "orphan state must not surface");
}

#[test]
fn malformed_state_emits_neither_state_nor_member_rows() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let malformed = state_record().replace(
        "\t\tscriptDigest = \"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\";\n",
        "",
    );
    let body = format!("{}{}", malformed, record_r1(&b));
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), sidecar_body(&body)),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|finding| finding.message.contains("valid scriptDigest")),
        "{findings:?}"
    );
    let inventory = inventory_of(&borrow(&sources));
    assert!(
        inventory.members.is_empty(),
        "managed row must not resolve through invalid state"
    );
    assert!(
        inventory.states.is_empty(),
        "invalid state must not surface"
    );
}

#[test]
fn malformed_forced_flag_emits_neither_state_nor_member_rows() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let malformed = state_record().replace(
        "\t\ttransformerPath = \"scripts/reqs.transform.ts\";\n",
        "\t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tforcedSchemaDrift = \"false\";\n",
    );
    let body = format!("{}{}", malformed, record_r1(&b));
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        ("m.provenance.sysml".to_string(), sidecar_body(&body)),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(
        findings
            .iter()
            .any(|finding| finding.message.contains("malformed forcedSchemaDrift")),
        "{findings:?}"
    );
    let inventory = inventory_of(&borrow(&sources));
    assert!(inventory.members.is_empty());
    assert!(inventory.states.is_empty());
}

#[test]
fn rows_resolve_source_facts_through_the_state() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let sources = fixture(&indented(MEMBER), &fields(&b, true));
    let inventory = inventory_of(&borrow(&sources));
    assert_eq!(inventory.members.len(), 1);
    let row = &inventory.members[0];
    assert_eq!(row.source.as_deref(), Some("reqs.csv"));
    assert_eq!(
        row.transformer_path.as_deref(),
        Some("scripts/reqs.transform.ts")
    );
    assert_eq!(inventory.states.len(), 1);
    let state = &inventory.states[0];
    assert_eq!(state.transform_id, "sync");
    assert_eq!(state.transformer_path, "scripts/reqs.transform.ts");
    assert_eq!(state.target_qn.as_deref(), Some("Flashlight"));
    assert!(!state.forced_schema_drift);
    assert_eq!(state.sources.len(), 1);
    assert_eq!(state.sources[0].alias, "source");
    assert_eq!(state.sources[0].source_ref, "reqs.csv");
    assert_eq!(
        state.sources[0].input_digest.as_deref(),
        Some("sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
    );
    // The diagnostic-tier row count parses; it is never validity.
    assert_eq!(state.sources[0].row_count, Some(11));
}

#[test]
fn row_digest_and_state_digests_surface() {
    let config = Config::default();
    let b = baseline(MEMBER, &config);
    let row_digest = format!("sha256:{}", "a".repeat(64));
    let script_digest = format!("sha256:{}", "b".repeat(64));
    let input_digest = format!("sha256:{}", "c".repeat(64));
    let state = format!(
        "\tmetadata <'sync/@state'> s_sync : TransformMeta::TransformState {{\n\
         \t\ttransformId = \"sync\";\n\
         \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
         \t\tscriptDigest = \"{script_digest}\";\n\
         \t\tforcedSchemaDrift = \"true\";\n\
         \t\tmetadata src0 : TransformMeta::TransformSource {{\n\
         \t\t\tsourceAlias = \"source\";\n\
         \t\t\tsourceRef = \"reqs.csv\";\n\
         \t\t\tinputDigest = \"{input_digest}\";\n\
         \t\t}}\n\
         \t}}\n"
    );
    let record = format!(
        "\tmetadata <'sync/R-1'> p_r1 : TransformMeta::TransformProvenance about Flashlight::beam {{\n\
         {}\t\trowDigest = \"{row_digest}\";\n\t}}\n",
        fields(&b, true)
    );
    let sources = vec![
        ("TransformMeta.sysml".to_string(), META.to_string()),
        ("m.sysml".to_string(), content_unit(&indented(MEMBER))),
        (
            "m.provenance.sysml".to_string(),
            sidecar_body(&format!("{state}{record}")),
        ),
    ];
    let findings = guard_findings(&borrow(&sources), &config);
    assert!(findings.is_empty(), "{findings:?}");
    let inventory = inventory_of(&borrow(&sources));
    assert_eq!(
        inventory.members[0].row_digest.as_deref(),
        Some(row_digest.as_str())
    );
    let state = &inventory.states[0];
    assert_eq!(state.script_digest.as_deref(), Some(script_digest.as_str()));
    assert!(state.forced_schema_drift);
    assert_eq!(
        state.sources[0].input_digest.as_deref(),
        Some(input_digest.as_str())
    );
}
