//! Property audit: emitted property sets per metaclass against the
//! normative metamodel XMI (`spec-refs/{KerML,SysML}.xmi`, 20250201).
//!
//! The XMI carries facts the JSON schemas do not: the owned-vs-derived
//! split (`isDerived`), defaults, lower multiplicity bounds, and
//! property redefinitions. Over the whole corpus emission:
//!
//! 1. compact form — every key names a non-derived property of its
//!    element's concrete metaclass (KerML 10.4: owned properties only);
//! 2. per element — every *required* owned property (lower bound ≥ 1, no
//!    default, not derived) is present, either under its own name or a
//!    name that transitively redefines it (the pilot emits the
//!    most-specific redefining name: `subclassifier` for
//!    `specific`/`target`);
//! 3. coverage — an owned property never emitted corpus-wide must be
//!    *explained*: replaced by an emitted redefiner, defaulted,
//!    optional, or on the documented-omission list below;
//! 4. full form — every key stays within the metaclass's property
//!    closure (owned + derived).
//!
//! Failures print per-(metaclass, property) tallies so emitter drift is
//! named directly.

#![cfg(feature = "json")]

use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use sysmlv2_parser::full::model_to_full_json;
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;
use sysmlv2_testkit as testkit;
use testkit::xmi_props::{XMI_DERIVED, XMI_HAS_DEFAULT, XMI_OPTIONAL, XmiProp};

/// Keys that are JSON-serialization bookkeeping, not metamodel
/// properties (KerML 10.4: `@type` = metaclass, `@id` = elementId).
const BOOKKEEPING: [&str; 2] = ["@type", "@id"];

/// Every `validate…` rule the pinned metamodel XMI declares.
fn pinned_rules() -> BTreeSet<String> {
    let root = testkit::workspace_root();
    let mut rules = BTreeSet::new();
    for file in ["spec-refs/KerML.xmi", "spec-refs/SysML.xmi"] {
        let text = std::fs::read_to_string(root.join(file)).unwrap();
        for line in text.lines().filter(|line| line.contains("<ownedRule ")) {
            let Some(name) = line
                .split(" name=\"")
                .nth(1)
                .and_then(|tail| tail.split('"').next())
            else {
                continue;
            };
            if name.starts_with("validate") {
                rules.insert(name.to_string());
            }
        }
    }
    rules
}

#[test]
fn normative_validation_rule_inventory_and_implemented_registry() {
    let rules = pinned_rules();
    assert_eq!(
        rules.len(),
        180,
        "the pinned normative validation-rule inventory changed; classify the delta"
    );
    for implemented in sysmlv2_parser::check::IMPLEMENTED_NORMATIVE_VALIDATION_RULES
        .iter()
        .chain(sysmlv2_parser::check::IMPLEMENTED_NORMATIVE_SEMANTIC_RULES)
    {
        assert!(
            rules.contains(*implemented),
            "implemented rule `{implemented}` is not present in the pinned XMI"
        );
    }
}

/// A finding that reports a named rule carries the identifier as a
/// field, so a consumer never has to read it back out of the message,
/// and the identifier it carries is the one the pinned metamodel spells.
/// Where a rule reached this implementation under a different spelling,
/// the message keeps that spelling and only the field is normalized.
#[test]
fn semantic_findings_carry_the_rule_they_report() {
    use sysmlv2_parser::{check, json::ResolvedModel};
    let rules = pinned_rules();
    let implemented: BTreeSet<&str> = check::IMPLEMENTED_NORMATIVE_SEMANTIC_RULES
        .iter()
        .copied()
        .collect();
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    // One prepared library, shared by every probe build.
    let prepared = base.prepare_library().unwrap();
    let probes =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml/probes");
    let mut coded = 0usize;
    for entry in std::fs::read_dir(&probes).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        if !name.ends_with(".sysml") && !name.ends_with(".kerml") {
            continue;
        }
        let source = std::fs::read_to_string(&path).unwrap();
        let mut model = Model::new();
        prepared.clone().install(&mut model).unwrap();
        model.add_source(&name, &source);
        let mut r = ResolvedModel::build(&model);
        for (_, d) in check::validate_semantics_with(&mut r, &model) {
            let spelled = d
                .message
                .strip_suffix(']')
                .and_then(|head| head.rsplit_once(" ["))
                .map(|(_, rule)| rule)
                .filter(|rule| rule.starts_with("validate"));
            let Some(spelled) = spelled else {
                assert!(
                    d.code.is_none(),
                    "{name}: a finding naming no rule carries a code: {d:?}"
                );
                continue;
            };
            let code = d
                .code
                .unwrap_or_else(|| panic!("{name}: finding reports `{spelled}` with no code"));
            assert!(
                code == spelled || (rules.contains(code) && !rules.contains(spelled)),
                "{name}: code `{code}` differs from the message's `{spelled}` \
                 without being the pinned spelling of it"
            );
            if rules.contains(code) {
                assert!(
                    implemented.contains(code),
                    "{name}: rule `{code}` is reported and pinned, but missing \
                     from the implemented-rule registry"
                );
            }
            coded += 1;
        }
    }
    assert!(coded > 100, "the probe sweep reported only {coded} rules");
}

/// Documented omissions: required or coverage-expected properties the
/// compact emitter deliberately never spells, each with its reason.
const OMISSIONS: [(&str, &str, &str); 3] = [
    (
        "*",
        "aliasIds",
        "no textual-notation spelling — alias ids arrive only through the \
         REST API surface; schema default is the empty array",
    ),
    (
        "*",
        "memberElement",
        "on OwningMembership the derived `ownedMemberElement` redefines it \
         and the element is carried in `ownedRelatedElement`; spelled \
         explicitly only on non-owning Memberships (aliases)",
    ),
    (
        "ConjugatedPortTyping",
        "conjugatedPortDefinition",
        "TRACKED GAP (INTEROP.md 'Known gaps'): the compact owner-side \
         property remains omitted; the implicit `~P` element and the \
         full-form owner-side property are emitted",
    ),
];

fn suppressed(ty: &str, prop: &str) -> bool {
    OMISSIONS
        .iter()
        .any(|(t, p, _)| (*t == "*" || *t == ty) && *p == prop)
}

fn corpus_model() -> Model {
    let mut model = Model::new();
    model
        .load_library_dir(&testkit::library_dir())
        .expect("library loads");
    for f in testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    assert!(!model.has_errors(), "corpus parses clean");
    model
}

/// Every element of a flat-array emission, as (metaclass, keys).
fn elements_of(json: Value) -> Vec<(String, Vec<String>)> {
    let Value::Array(elements) = json else {
        panic!("emission is a flat element array");
    };
    elements
        .into_iter()
        .map(|e| {
            let Value::Object(obj) = e else {
                panic!("element is an object")
            };
            let ty = obj["@type"].as_str().expect("@type is a string").to_owned();
            let keys = obj
                .keys()
                .filter(|k| !BOOKKEEPING.contains(&k.as_str()))
                .cloned()
                .collect();
            (ty, keys)
        })
        .collect()
}

fn find(props: &'static [XmiProp], name: &str) -> Option<&'static XmiProp> {
    props
        .binary_search_by(|(n, _, _)| n.cmp(&name))
        .ok()
        .map(|i| &props[i])
}

/// `name` plus everything it transitively redefines within `props`.
fn redefinition_closure(props: &'static [XmiProp], name: &str) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    let mut stack = vec![name.to_owned()];
    while let Some(n) = stack.pop() {
        let Some((n, _, redefined)) = find(props, &n) else {
            continue;
        };
        if out.insert(*n) {
            stack.extend(redefined.iter().map(|r| (*r).to_owned()));
        }
    }
    out
}

#[test]
fn compact_properties_match_xmi_owned_sets() {
    let model = corpus_model();
    let mut unknown_metaclass: BTreeMap<String, usize> = BTreeMap::new();
    let mut abstract_metaclass: BTreeMap<String, usize> = BTreeMap::new();
    let mut unknown_prop: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut derived_in_compact: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut missing_required: BTreeMap<(String, String), usize> = BTreeMap::new();
    // metaclass → union of emitted keys, for the coverage rule.
    let mut emitted_union: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for (ty, keys) in elements_of(model_to_compact_json(&model)) {
        let Some((is_abstract, props)) = testkit::xmi_metaclass(&ty) else {
            *unknown_metaclass.entry(ty).or_default() += 1;
            continue;
        };
        if is_abstract {
            *abstract_metaclass.entry(ty.clone()).or_default() += 1;
        }
        for key in &keys {
            match find(props, key) {
                None => {
                    *unknown_prop.entry((ty.clone(), key.clone())).or_default() += 1;
                }
                Some((_, flags, _)) if flags & XMI_DERIVED != 0 => {
                    *derived_in_compact
                        .entry((ty.clone(), key.clone()))
                        .or_default() += 1;
                }
                Some(_) => {}
            }
        }
        // Required properties: present under their own or a redefining name.
        let satisfied: BTreeSet<&str> = keys
            .iter()
            .flat_map(|k| redefinition_closure(props, k))
            .collect();
        for (name, flags, _) in props {
            let required = flags & (XMI_DERIVED | XMI_HAS_DEFAULT | XMI_OPTIONAL) == 0;
            if required && !satisfied.contains(name) && !suppressed(&ty, name) {
                *missing_required
                    .entry((ty.clone(), (*name).to_owned()))
                    .or_default() += 1;
            }
        }
        emitted_union.entry(ty).or_default().extend(keys);
    }

    // Coverage: owned properties never emitted corpus-wide must be
    // explained (redefined-by-emitted, defaulted, optional, documented).
    let mut unexplained_omission: BTreeMap<(String, String), &str> = BTreeMap::new();
    for (ty, union) in &emitted_union {
        let (_, props) = testkit::xmi_metaclass(ty).unwrap();
        let replaced: BTreeSet<&str> = union
            .iter()
            .flat_map(|k| redefinition_closure(props, k))
            .collect();
        for (name, flags, _) in props {
            if flags & XMI_DERIVED != 0 || union.contains(*name) {
                continue;
            }
            if replaced.contains(name)
                || flags & (XMI_HAS_DEFAULT | XMI_OPTIONAL) != 0
                || suppressed(ty, name)
            {
                continue;
            }
            unexplained_omission.insert((ty.clone(), (*name).to_owned()), "never emitted");
        }
    }

    let mut report = String::new();
    for (name, map) in [
        ("emitted @type not in the metamodel", &unknown_metaclass),
        (
            "emitted @type is abstract in the metamodel",
            &abstract_metaclass,
        ),
    ] {
        for (ty, n) in map {
            report.push_str(&format!("  {name}: {ty} (×{n})\n"));
        }
    }
    for (name, map) in [
        ("property not in the metaclass closure", &unknown_prop),
        ("derived property in compact form", &derived_in_compact),
        ("required property missing", &missing_required),
    ] {
        for ((ty, key), n) in map {
            report.push_str(&format!("  {name}: {ty}.{key} (×{n})\n"));
        }
    }
    for ((ty, key), why) in &unexplained_omission {
        report.push_str(&format!("  unexplained omission: {ty}.{key} ({why})\n"));
    }
    assert!(
        report.is_empty(),
        "XMI property audit violations:\n{report}"
    );
}

#[test]
fn full_form_stays_within_xmi_closures() {
    let model = corpus_model();
    let mut violations: BTreeMap<(String, String), usize> = BTreeMap::new();
    for (ty, keys) in elements_of(model_to_full_json(&model)) {
        let Some((_, props)) = testkit::xmi_metaclass(&ty) else {
            *violations
                .entry((ty, "<unknown metaclass>".into()))
                .or_default() += 1;
            continue;
        };
        for key in keys {
            if find(props, &key).is_none() {
                *violations.entry((ty.clone(), key)).or_default() += 1;
            }
        }
    }
    let report: String = violations
        .iter()
        .map(|((ty, key), n)| format!("  {ty}.{key} (×{n})\n"))
        .collect();
    assert!(
        report.is_empty(),
        "full-form keys outside the XMI closure:\n{report}"
    );
}
