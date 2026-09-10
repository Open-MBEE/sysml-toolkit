//! `sysmlv2` — CLI for the sysmlv2-parser library: convert, format, and check
//! SysML v2 / KerML models.

use clap::{Parser, Subcommand, ValueEnum};
use std::collections::{HashMap, HashSet};
use std::fs::{OpenOptions, Permissions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use sysmlv2_parser::Diagnostic;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::full::{model_to_full_json_with, to_full_json_with};
use sysmlv2_parser::json::{library_name_map, model_to_compact_json_with_units, to_compact_json};
use sysmlv2_parser::lift::from_compact_json_with_names;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};
use sysmlv2_parser::print::{Indent, PrintOptions, format_source_with, print_source_opts};
use sysmlv2_parser::span::{LineIndex, Span};

mod kpar;

/// Load the standard library into `model` through the resolution cache
/// (`~/.cache/sysmlv2`; override the directory with `SYSMLV2_CACHE_DIR`,
/// disable caching with `SYSMLV2_LIB_CACHE=off`). A cache hit replays the
/// recorded outcomes during the next build; a miss arms recording — pass
/// the returned path to [`save_library_cache`] once the model was built.
fn load_library(model: &mut Model, dir: &Path) -> std::io::Result<Option<PathBuf>> {
    model.load_library_dir(dir)?;
    // The generated ambient libraries (`Web`, `Template`, engine
    // overlays, `TransformMeta`) ride along with every library load;
    // their content is part of the cache key.
    sysmlv2_parser::ambient::add_to(model);
    if std::env::var_os("SYSMLV2_LIB_CACHE").is_some_and(|v| v == "off") {
        return Ok(None);
    }
    let Ok(key) = sysmlv2_parser::libcache::hash_library_dir(dir) else {
        return Ok(None);
    };
    let key = sysmlv2_parser::ambient::mix_key(key);
    let Some(path) = sysmlv2_parser::libcache::default_cache_path(key) else {
        return Ok(None);
    };
    match sysmlv2_parser::libcache::LibraryCache::load(&path) {
        Some(cache) => {
            model.set_library_cache(cache);
            // The path is still returned: a failed snapshot validation
            // rebuilds cold and re-records, and the save then overwrites
            // the stale file (saves only happen when something recorded).
            Ok(Some(path))
        }
        None => {
            model.record_library_cache();
            Ok(Some(path))
        }
    }
}

/// Inverse of [`flexo_payload`] for Flexo *responses*: unwrap
/// `{payload, identity}` change records when present and normalize the
/// server's empty-string property values back to null, so the element
/// list lifts like ordinary interchange JSON.
fn flexo_unwrap(value: serde_json::Value) -> serde_json::Value {
    fn empties_to_null(v: &mut serde_json::Value) {
        match v {
            serde_json::Value::Object(map) => {
                for (_, val) in map.iter_mut() {
                    if val.as_str() == Some("") {
                        *val = serde_json::Value::Null;
                    } else {
                        empties_to_null(val);
                    }
                }
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(empties_to_null),
            _ => {}
        }
    }
    let serde_json::Value::Array(items) = value else {
        return value;
    };
    let wrapped = !items.is_empty()
        && items
            .iter()
            .all(|r| r.get("payload").is_some() && r.get("identity").is_some());
    let mut elements: Vec<serde_json::Value> = if wrapped {
        items.into_iter().map(|mut r| r["payload"].take()).collect()
    } else {
        items
    };
    elements.iter_mut().for_each(empties_to_null);
    serde_json::Value::Array(elements)
}

/// Flexo MMS commit conventions: name each root namespace after its source
/// file (Flexo stores the file name in the root's `qualifiedName` and
/// splits documents on it when reading back), then wrap every element as a
/// `{payload, identity}` change record with null property values emptied
/// (matching the Flexo MMS payload shape byte for byte).
fn flexo_payload(mut json: serde_json::Value, input_names: &[String]) -> serde_json::Value {
    let serde_json::Value::Array(elements) = &mut json else {
        return json;
    };
    let mut root_i = 0usize;
    for e in elements.iter_mut() {
        let is_root = e.get("@type").and_then(|v| v.as_str()) == Some("Namespace")
            && e.get("owningRelationship")
                .is_none_or(serde_json::Value::is_null);
        if is_root {
            if let Some(name) = input_names.get(root_i) {
                e["qualifiedName"] = serde_json::Value::String(name.clone());
            }
            root_i += 1;
        }
    }
    fn nulls_to_empty(v: &mut serde_json::Value) {
        match v {
            serde_json::Value::Object(map) => {
                for (_, val) in map.iter_mut() {
                    if val.is_null() {
                        *val = serde_json::Value::String(String::new());
                    } else {
                        nulls_to_empty(val);
                    }
                }
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(nulls_to_empty),
            _ => {}
        }
    }
    let wrapped = elements
        .iter()
        .map(|e| {
            let id = e.get("@id").cloned().unwrap_or(serde_json::Value::Null);
            let mut payload = e.clone();
            nulls_to_empty(&mut payload);
            serde_json::json!({ "payload": payload, "identity": { "@id": id } })
        })
        .collect();
    serde_json::Value::Array(wrapped)
}

/// File name for one split document: the root namespace's recorded name
/// when it is a plain model file name (the Flexo convention), else a
/// numbered fallback.
fn doc_file_name(root_name: Option<&str>, index: usize) -> String {
    if let Some(name) = root_name {
        let base = Path::new(name)
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let safe = !base.is_empty()
            && base
                .chars()
                .all(|c| c != ':' && c != '*' && c != '?' && c != '"');
        if safe && (base.ends_with(".sysml") || base.ends_with(".kerml")) {
            return base;
        }
    }
    format!("document-{}.sysml", index + 1)
}

/// Persist the outcomes recorded by the first build after [`load_library`]
/// armed recording. Best-effort: the cache is an accelerator only.
fn save_library_cache(model: &Model, path: Option<PathBuf>) {
    if let (Some(path), Some(cache)) = (path, model.take_recorded_library_cache()) {
        let _ = cache.save(&path);
    }
}

#[derive(Parser)]
#[command(
    name = "sysmlv2",
    version,
    about = "Parse, convert, format, and check SysML v2 / KerML models",
    long_about = "Parse, convert, format, and check OMG SysML v2 / KerML textual models.\n\
                  \n\
                  Conversion matrix (--to):\n\
                  \x20 text          textual notation (.sysml / .kerml)\n\
                  \x20 compact-json  KerML 10.4 compact interchange form\n\
                  \x20 compact-cbor  binary re-encoding of the compact form\n\
                  \x20 full-json     derived properties + implied relationships (schema-valid)\n\
                  \x20 full-cbor     binary re-encoding of the full form (emit view)\n\
                  \x20 kpar          KerML 10.3 project archive (zipped units + manifests)\n\
                  \n\
                  Inputs may be textual (.sysml / .kerml), interchange JSON (.json),\
                  compact CBOR (.s2c), or project archives (.kpar, expanded to\n\
                  their textual units);\n\
                  full-form JSON input is normalized to compact automatically.\n\
                  Pass --lib <dir> (e.g. the OMG sysml.library directory) to resolve\n\
                  standard-library references to their normative element IDs — and to\n\
                  name them again when converting JSON back to text.\n\
                  \n\
                  Anywhere a file path is accepted, `-` reads from stdin (parsed as\n\
                  SysML unless the input is sniffed as JSON).\n\
                  \n\
                  Standard-library loads are cached automatically: the first run\n\
                  against a library records a sealed snapshot (resolutions + element\n\
                  ids) under ~/.cache/sysmlv2/, keyed by library content and stamped\n\
                  with the exact toolkit build — later runs replay it, and any\n\
                  mismatch (including a toolkit rebuilt from changed sources at the\n\
                  same version) rebuilds cold and refreshes the file. Set\n\
                  SYSMLV2_CACHE_DIR to relocate the cache or SYSMLV2_LIB_CACHE=off\n\
                  to disable it (e.g. for benchmarking).\n\
                  \n\
                  Ambient model context: when SYSMLV2_MODEL_DIR names a directory,\n\
                  its .sysml/.kerml files stand in for omitted input files (fmt\n\
                  honors this under --check only), and a stderr note records that\n\
                  ambient state supplied the inputs (silence it with -q).\n\
                  SYSMLV2_LIB_DIR fills --lib the same way wherever it is accepted.\n\
                  With the variable set, --help ends with the active context.",
    after_help = "EXAMPLES:\n\
                  \x20 sysmlv2 convert model.sysml --to compact-json\n\
                  \x20 sysmlv2 convert model.sysml --to compact-json --lib sysml.library/ -o model.json\n\
                  \x20 cat model.sysml | sysmlv2 convert - --to compact-json\n\
                  \x20 sysmlv2 fmt src/**/*.sysml\n\
                  \x20 sysmlv2 fmt --check model.sysml\n\
                  \x20 sysmlv2 check model.sysml lib.kerml\n\
                  \x20 sysmlv2 parse model.sysml --ast"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
    /// Suppress informational stderr notes (e.g. the ambient
    /// model-context line printed when SYSMLV2_MODEL_DIR supplies the
    /// input files)
    #[arg(short, long, global = true)]
    quiet: bool,
    /// Keep quoted power-product unit spellings (`'m³⋅s⁻²'`) opaque
    /// instead of expanding them by parsing the name — the evaluator
    /// then treats such a unit as its own base dimension, convertible
    /// with nothing [env: SYSMLV2_UNIT_SPELLINGS=off]
    #[arg(long = "no-unit-spellings", global = true)]
    no_unit_spellings: bool,
}

#[derive(Clone, Copy, PartialEq, ValueEnum)]
enum Target {
    /// Textual notation
    Text,
    /// Compact interchange JSON (KerML 10.4; no implied relationships)
    CompactJson,
    /// Compact interchange CBOR: the deterministic binary
    /// re-encoding of compact JSON (binary output; use -o)
    CompactCbor,
    /// Full interchange JSON: derived properties + implied relationships
    FullJson,
    /// Full interchange CBOR: the binary re-encoding of full JSON
    /// (emit view only; binary output; use -o)
    FullCbor,
    /// KerML 10.3 project archive (.kpar): zipped textual units + manifests
    Kpar,
}

#[derive(Subcommand)]
enum Command {
    /// Convert a model between textual notation and interchange JSON
    #[command(
        long_about = "Convert a model between textual notation and interchange JSON/CBOR.\n\
                      \n\
                      The input format is detected from the file extension:\n\
                      .sysml / .kerml parse as textual notation; .json is lifted from\n\
                      the interchange form (full-form JSON is normalized to compact —\n\
                      implied relationships dropped, derived properties ignored);\n\
                      .s2c decodes as compact-form CBOR and then flows like .json.\n\
                      With --lib, text→JSON resolves standard-library references to\n\
                      their normative KerML 9.1 element IDs, and JSON→text turns those\n\
                      IDs back into qualified names.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 convert model.sysml --to compact-json\n\
                      \x20 sysmlv2 convert model.json --to text -o model.sysml\n\
                      \x20 sysmlv2 convert model.json --to text --min-qual   # shortest reference spellings\n\
                      \x20 sysmlv2 convert full.json --to compact-json     # normalize full → compact\n\
                      \x20 sysmlv2 convert model.sysml --to compact-cbor -o model.s2c\n\
                      \x20 sysmlv2 convert model.s2c --to text             # binary → textual notation\n\
                      \x20 sysmlv2 convert model.sysml --to compact-json --lib spec-refs/SysML-v2-Release/sysml.library"
    )]
    Convert {
        /// Input files (.sysml / .kerml — several form one model with one
        /// root namespace per file), or a single .json / .s2c; `-` for
        /// stdin (text or JSON); optional when SYSMLV2_MODEL_DIR is set
        inputs: Vec<PathBuf>,
        /// Output format
        #[arg(long, value_enum)]
        to: Target,
        /// Output file (defaults to stdout). For `--to text` with a
        /// multi-document JSON input, an existing directory splits the
        /// output into one file per root namespace
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Flexo MMS conventions on JSON output: each root namespace's
        /// qualifiedName is set to its source file name and every element
        /// is wrapped as a `{payload, identity}` change record
        #[arg(long)]
        flexo: bool,
        /// JSON → text only: respell every reference with the shortest
        /// spelling that still resolves to the same element (bare name
        /// where unambiguous, a qualified suffix where needed), verified
        /// by reparse; without it references print as always-correct
        /// `$::`-rooted paths
        #[arg(long = "min-qual")]
        min_qual: bool,
        /// --to compact-cbor only: omit graph-derivable element ids
        /// (IDS.md) — receivers recompute them, verified by the
        /// payload's integrity digest. Composes with --delta-base
        /// (strict deltas: created ids elide). Decode/apply against
        /// the same --lib version the payload was encoded with
        #[arg(long = "elide-ids")]
        elide_ids: bool,
        /// Delta base (compact .json or .s2c). With --to compact-cbor
        /// the output becomes a delta against it; with a
        /// delta .s2c input the delta is applied to it first
        #[arg(long = "delta-base")]
        delta_base: Option<PathBuf>,
        /// Delta output only: id-keyed identities, applicable
        /// best-effort to divergent bases (larger than the strict
        /// indexed default)
        #[arg(long = "delta-portable")]
        delta_portable: bool,
        /// Indentation for textual output: `tabs` or a space count
        /// (default 4)
        #[arg(long, value_parser = parse_indent_arg, default_value = "4")]
        indent: Indent,
        /// Emit the resolved standard library itself — every element
        /// of the --lib units, each under its normative KerML 9.1 id —
        /// instead of converting a model. The complement of a normal
        /// conversion, whose output holds just the user units' elements
        /// while its library references dangle by design. Takes no
        /// inputs; targets compact-json and compact-cbor
        #[arg(long, requires = "lib")]
        library: bool,
    },
    /// Inspect payload files, or diff/apply them at payload identity
    #[command(
        long_about = "Inspect interchange payload files without loading them as a\n\
                      model: what each file is (compact/full snapshot or delta),\n\
                      its header versions, element and change counts, and its\n\
                      content digests. Snapshots (.s2c or compact .json) report\n\
                      their state digest — the digest a delta's base digest is\n\
                      matched against. Deltas report their base and result\n\
                      digests without needing the base present.\n\
                      \n\
                      With --find-base, every snapshot file under a directory is\n\
                      digested once and each delta input reports which of them it\n\
                      applies to cleanly (state digest = the delta's base digest)\n\
                      and which already hold its result. A delta with no base\n\
                      match fails the command, so the verb scripts as a check.\n\
                      \n\
                      Every mode of this verb works at payload identity: files\n\
                      are read exactly as their producer wrote them — no model\n\
                      lift, no id re-derivation, no rebase. --delta-from diffs\n\
                      two snapshots by element @id (a store whose ids are\n\
                      authoritative diffs its own states losslessly; contrast\n\
                      `convert --delta-base`, which re-derives and rebases ids\n\
                      for freshly parsed inputs). --apply-to applies a delta and\n\
                      reports what happened. --ids prints a snapshot's\n\
                      delta-canonical element id sequence — the index space\n\
                      strict deltas address their base through.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 payload model.s2c\n\
                      \x20 sysmlv2 payload edit.s2c --find-base exports/\n\
                      \x20 sysmlv2 payload base.s2c edit.s2c    # digests to match by hand\n\
                      \x20 sysmlv2 payload new.json --delta-from old.json -o commit.s2c\n\
                      \x20 sysmlv2 payload commit.s2c --apply-to old.json -o new.json\n\
                      \x20 sysmlv2 payload model.s2c --ids"
    )]
    Payload {
        /// Payload files: .s2c (snapshot or delta) or compact
        /// interchange .json
        inputs: Vec<PathBuf>,
        /// Directory to scan (recursively) for snapshot files whose
        /// state digest matches each delta's base or result digest
        #[arg(long = "find-base", value_name = "DIR")]
        find_base: Option<PathBuf>,
        /// Standard-library directory — lets id-elided snapshots with
        /// library-typed elements re-derive their ids for digesting
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Emit a delta from BASE to the single snapshot input, pairing
        /// elements by @id — producer ids are authoritative on both
        /// sides. Strict (indexed) unless --portable
        #[arg(long = "delta-from", value_name = "BASE",
              conflicts_with_all = ["find_base", "apply_to", "ids"])]
        delta_from: Option<PathBuf>,
        /// With --delta-from: id-keyed delta identities, applicable
        /// best-effort to a divergent base
        #[arg(long, requires = "delta_from")]
        portable: bool,
        /// With --delta-from: claim key 0 — the project the delta
        /// belongs to (routing hint; the digest is the proof)
        #[arg(long = "claim-project", value_name = "UUID", requires = "delta_from")]
        claim_project: Option<String>,
        /// With --delta-from: claim key 1 — the commit the base names
        #[arg(long = "claim-commit", value_name = "UUID", requires = "delta_from")]
        claim_commit: Option<String>,
        /// With --delta-from: claim key 2 — the emitting service
        #[arg(long = "claim-service", value_name = "URI", requires = "delta_from")]
        claim_service: Option<String>,
        /// Apply the single delta input to the snapshot BASE; the
        /// applied compact JSON goes to --output, the apply report
        /// (JSON) to stdout
        #[arg(long = "apply-to", value_name = "BASE",
              conflicts_with_all = ["find_base", "ids"])]
        apply_to: Option<PathBuf>,
        /// With --apply-to: portable deltas apply best-effort to a
        /// divergent base; the report counts the divergences
        #[arg(long, requires = "apply_to")]
        lenient: bool,
        /// Print each snapshot input's delta-canonical element id
        /// sequence with its state digest
        #[arg(long, conflicts_with = "find_base")]
        ids: bool,
        /// Print the codec tables as versioned JSON — the artifact a
        /// consumer vendors to label payload structure without this
        /// toolkit: metaclass wire codes with per-ordinal field tables
        /// (property, kind, enum table, presence default), both the
        /// compact and full ordinal spaces, the enum vocabularies, and
        /// the header version axes and flags. Takes no payload inputs
        #[arg(long, conflicts_with_all = ["find_base", "delta_from", "apply_to", "ids"])]
        tables: bool,
        /// Encode the single compact-JSON snapshot input to `.s2c` at
        /// payload identity — no lift, no id re-derivation (contrast
        /// `convert`, which parses its input as a model and re-derives
        /// ids). The store-side inverse of a snapshot decode
        #[arg(long, conflicts_with_all = ["find_base", "delta_from", "apply_to", "ids", "tables"])]
        encode: bool,
        /// Output file: the delta payload (--delta-from) or the applied
        /// compact JSON (--apply-to)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Format .sysml / .kerml files in place (canonical style)
    #[command(
        long_about = "Format textual models to the canonical style: four-space\n\
                      indentation, one member per line, symbolic specialization\n\
                      operators. Notes (// …) and blank lines are preserved.\n\
                      Files with parse errors are left untouched and reported.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 fmt model.sysml                # rewrite in place\n\
                      \x20 sysmlv2 fmt a.sysml b.kerml            # several files\n\
                      \x20 sysmlv2 fmt --check model.sysml        # exit 1 if not formatted\n\
                      \x20 sysmlv2 fmt --stdout model.sysml       # print instead of rewriting\n\
                      \x20 cat model.sysml | sysmlv2 fmt --stdout -  # format stdin"
    )]
    Fmt {
        /// Files to format; `-` reads stdin (requires --stdout or
        /// --check); with --check, optional when SYSMLV2_MODEL_DIR is set
        files: Vec<PathBuf>,
        /// Verify formatting without writing; exit 1 if any file differs
        #[arg(long)]
        check: bool,
        /// Print the formatted output instead of rewriting the file
        #[arg(long)]
        stdout: bool,
        /// Indentation for formatted output: `tabs` or a space count
        /// (default 4)
        #[arg(long, value_parser = parse_indent_arg, default_value = "4")]
        indent: Indent,
    },
    /// Parse and validate files (syntax + body-context legality; exit 1 on
    /// any error). With --lib, also runs referential checks as warnings.
    #[command(after_help = "Checks run in stages: parse diagnostics, then\n\
                            body-context validation (members that the grammar\n\
                            does not allow in their surrounding body, e.g. a\n\
                            `transition` inside a plain `part` body, or a\n\
                            `variant` member outside a `variation`).\n\
                            With --lib, all files form one model resolved\n\
                            against the library; referential findings are\n\
                            warnings (unresolved references, alias targets,\n\
                            circular imports), and semantic constraints are\n\
                            checked (multiplicity bounds, self/circular\n\
                            specialization — errors; duplicate\n\
                            specializations — warnings). Private imports\n\
                            that provably feed nothing in their unit warn\n\
                            as `unused private import`.\n\
                            Warnings never fail the run unless --strict is\n\
                            given, which exits 1 on any finding at all.\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 check model.sysml\n\
                            \x20 sysmlv2 check src/*.sysml lib/*.kerml\n\
                            \x20 sysmlv2 check model.sysml --lib spec-refs/SysML-v2-Release/sysml.library\n\
                            \x20 sysmlv2 check --strict --lib sysml.library/ model.sysml\n\
                            \x20 cat model.sysml | sysmlv2 check -")]
    Check {
        /// Files to check; `-` reads stdin; optional when
        /// SYSMLV2_MODEL_DIR is set
        files: Vec<PathBuf>,
        /// Standard-library directory; enables referential checks
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Treat warnings as failures: exit 1 on any finding (for
        /// pipelines that must refuse incomplete models, e.g. gating a
        /// Flexo commit)
        #[arg(long)]
        strict: bool,
    },
    /// Lint the model against configurable project-policy rules
    #[command(after_help = "Rules are policy, not language law: lint runs\n\
                            beside `check` and never changes its verdicts.\n\
                            Config JSON: { \"rules\": { \"<id>\": \"off\" |\n\
                            \"hint\" | \"info\" | \"warn\" | \"error\" |\n\
                            { \"severity\": …, \"scopes\": { \"<Metaclass>\":\n\
                            … }, …options } } } — default sysmlint.json\n\
                            beside the first input. Policy rules default\n\
                            off (undocumented-element,\n\
                            untyped-usage, unused-definition,\n\
                            unused-parameter, unit-spelling,\n\
                            multiline-conditions, indentation) — opt in per\n\
                            rule or per stereotype scope;\n\
                            naming-convention defaults info (a casing\n\
                            nudge — tighten or disable per project) and\n\
                            dimensional-consistency warns by default (a\n\
                            declared quantity type contradicting its value's\n\
                            unit is a finding anywhere).\n\
                            --fix applies safe fixes; fixes that DELETE model\n\
                            text (e.g. removing an unused parameter) are\n\
                            guarded behind --fix-deletes so information is\n\
                            never lost without explicit approval.\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 lint model.sysml\n\
                            \x20 sysmlv2 lint --config sysmlint.json src/*.sysml\n\
                            \x20 sysmlv2 lint --rule unused-definition=warn model.sysml\n\
                            \x20 sysmlv2 lint --fix --fix-deletes model.sysml\n\
                            \x20 sysmlv2 lint --strict model.sysml")]
    Lint {
        /// Files to lint; `-` reads stdin; optional when
        /// SYSMLV2_MODEL_DIR is set
        files: Vec<PathBuf>,
        /// Standard-library directory (resolution context only; library
        /// elements are never linted)
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Lint config JSON; defaults to sysmlint.json beside the first
        /// input when present
        #[arg(long)]
        config: Option<PathBuf>,
        /// Override one rule's severity, e.g. unused-definition=warn
        /// (repeatable; wins over the config file)
        #[arg(long = "rule", value_name = "ID=LEVEL")]
        rule: Vec<String>,
        /// Apply available auto-fixes that do not delete model text
        #[arg(long)]
        fix: bool,
        /// With --fix: also apply fixes that DELETE model text (an
        /// unused parameter's fix removes its declaration — deliberate
        /// extra consent, deletions lose information)
        #[arg(long, requires = "fix")]
        fix_deletes: bool,
        /// Exit 1 on any error-severity finding
        #[arg(long)]
        strict: bool,
    },
    /// Check constraint/requirement bodies to verdicts
    #[cfg(feature = "solve")]
    #[command(after_help = "Evaluates every constraint, requirement, and\n\
                            invariant body that carries its own trailing\n\
                            result expression: satisfied / violated /\n\
                            undecided (with the reason — unbound features,\n\
                            unsupported constructs). Exit 1 if any\n\
                            constraint is violated.\n\n\
                            With --ranges, interval propagation narrows every\n\
                            unbound feature to a finite range and upgrades\n\
                            verdicts (satisfied/VIOLATED/unsatisfiable) with\n\
                            no external solver.\n\n\
                            With --solve, propagation runs first and Z3 (the\n\
                            `z3` binary; see --z3) then handles only what it\n\
                            left undecided: proved to hold for all values of\n\
                            the unbound features (satisfied), proved\n\
                            unsatisfiable (VIOLATED), or satisfiable with a\n\
                            witness assignment.\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 verify model.sysml\n\
                            \x20 sysmlv2 verify model.sysml --ranges\n\
                            \x20 sysmlv2 verify model.sysml --solve\n\
                            \x20 sysmlv2 verify src/*.sysml --lib spec-refs/SysML-v2-Release/sysml.library")]
    Verify {
        /// Input files (.sysml or .kerml) forming one model; `-` reads
        /// stdin; optional when SYSMLV2_MODEL_DIR is set
        files: Vec<PathBuf>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Interval-propagate undecided constraints and print narrowed
        /// feature ranges (no external solver)
        #[arg(long)]
        ranges: bool,
        /// Run Z3 over undecided constraints (witnesses, proofs); implies
        /// propagation first, so Z3 only sees what it left undecided
        #[arg(long)]
        solve: bool,
        /// Path to the z3 binary (default: `z3` on PATH)
        #[arg(long, value_name = "PATH")]
        z3: Option<PathBuf>,
    },
    /// Evaluate feature values in a model (expression evaluator)
    #[command(after_help = "Evaluates the bound value expression of each named\n\
                            feature against the resolved model: literals,\n\
                            arithmetic/logical/comparison operators, ranges,\n\
                            sequences, feature references (redefinition-aware),\n\
                            and Kernel Function Library intrinsics incl.\n\
                            collect/select/reduce lambdas. Use --all to list\n\
                            every feature with a computed value.\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 eval model.sysml Demo::car::mass\n\
                            \x20 sysmlv2 eval model.sysml --all --lib spec-refs/SysML-v2-Release/sysml.library\n\
                            \x20 sysmlv2 eval a.sysml b.sysml --all\n\
                            \x20 sysmlv2 eval model.sysml 'Pkg::totalMass' 'Pkg::cost'")]
    Eval {
        /// Input file (.sysml or .kerml), or `-` for stdin; optional when
        /// SYSMLV2_MODEL_DIR is set (a leading qualified name is then a
        /// name, not a file)
        input: Option<PathBuf>,
        /// Qualified names to evaluate (e.g. `Pkg::part::attr`); arguments
        /// ending in `.sysml`/`.kerml` are further files joining the model
        names: Vec<String>,
        /// Evaluate every feature that has a value expression
        #[arg(long)]
        all: bool,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
    /// Query a model with an ad-hoc KerML expression
    #[command(
        long_about = "Query a model with an ad-hoc KerML expression, evaluated\n\
                      against the root namespace — references resolve exactly\n\
                      as they would in a model file (qualified names, feature\n\
                      chains, select/collect/reduce lambdas, KFL intrinsics).\n\
                      \n\
                      Two extensions apply only here (never to feature values\n\
                      in model files): `istype`/`as` on a model element\n\
                      classify the declaration itself, so a miss against a\n\
                      user-defined type answers `false` instead of undecided;\n\
                      and the reflection functions `ownedMember(x)` /\n\
                      `ownedFeature(x)` (the KerML derived properties as\n\
                      functions) enumerate an element's owned members.\n\
                      \n\
                      A sequence result prints one item per line; elements\n\
                      print as qualified name and metaclass.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 query model.sysml 'ownedFeature(Vehicle)->select { in p; p istype Wheel }'\n\
                      \x20 sysmlv2 query model.sysml 'Demo::car.totalMass + 10'\n\
                      \x20 sysmlv2 query a.sysml b.sysml 'size(ownedMember(Demo))'\n\
                      \x20 cat model.sysml | sysmlv2 query - 'ownedFeature(Vehicle)'"
    )]
    Query {
        /// Input file (.sysml or .kerml), or `-` for stdin; optional when
        /// SYSMLV2_MODEL_DIR is set (the expression alone then suffices)
        input: Option<PathBuf>,
        /// The query expression; arguments ending in `.sysml`/`.kerml`
        /// are further files joining the model
        args: Vec<String>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
    /// Render a view's template over its exposed model slice (semantic mode)
    #[command(
        long_about = "Render the component template a view usage presents over the\n\
                      model elements the view exposes (semantic mode): the\n\
                      view's rendering definition owns an imported template root whose\n\
                      translated expressions evaluate over the exposed slice. Prints the\n\
                      rendered tree as JSON, or as HTML with --html. The model is not\n\
                      modified.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 render --lib sysml.library model.sysml PackagesView.sysml Site::packagesView\n\
                      \x20 sysmlv2 render --lib sysml.library --html app.sysml App::home"
    )]
    Render {
        /// Model files (.sysml/.kerml) followed by the view usage's qualified name
        args: Vec<String>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Print HTML instead of the JSON node tree
        #[arg(long)]
        html: bool,
    },
    /// Describe one element: metaclass, owner, typing, position
    #[command(
        long_about = "Describe one element of the resolved model: its metaclass,\n\
                      owner, declared type, position among its owner's members,\n\
                      and declaration site.",
        after_help = "EXAMPLES:\n\
                      \x20 sysmlv2 describe model.sysml Demo::car\n\
                      \x20 sysmlv2 describe a.sysml b.sysml Demo::car::mass\n\
                      \x20 sysmlv2 describe Demo::car          (SYSMLV2_MODEL_DIR set)"
    )]
    Describe {
        /// Input file (.sysml or .kerml), or `-` for stdin; optional when
        /// SYSMLV2_MODEL_DIR is set (a leading qualified name is then a
        /// name, not a file)
        input: Option<PathBuf>,
        /// The ::-qualified element name; arguments ending in
        /// `.sysml`/`.kerml` are further files joining the model
        args: Vec<String>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
    /// List an element's owned members
    #[command(after_help = "EXAMPLES:\n\
                            \x20 sysmlv2 members model.sysml Demo\n\
                            \x20 sysmlv2 members model.sysml Demo::car\n\
                            \x20 sysmlv2 members Demo                (SYSMLV2_MODEL_DIR set)")]
    Members {
        /// Input file (.sysml or .kerml), or `-` for stdin; optional when
        /// SYSMLV2_MODEL_DIR is set (a leading qualified name is then a
        /// name, not a file)
        input: Option<PathBuf>,
        /// The ::-qualified element name; arguments ending in
        /// `.sysml`/`.kerml` are further files joining the model
        args: Vec<String>,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
    /// Parse one file and dump diagnostics (and optionally the AST)
    #[command(after_help = "EXAMPLES:\n\
                            \x20 sysmlv2 parse model.sysml\n\
                            \x20 sysmlv2 parse model.sysml --ast\n\
                            \x20 cat model.sysml | sysmlv2 parse -")]
    Parse {
        /// Input file, or `-` for stdin; optional when SYSMLV2_MODEL_DIR
        /// is set (each discovered file parses independently)
        input: Option<PathBuf>,
        /// Pretty-print the syntax tree
        #[arg(long)]
        ast: bool,
    },
    /// Emit a PlantUML diagram
    #[cfg(feature = "viz")]
    #[command(after_help = "Renders one view of the model as PlantUML text\n\
                            (feed it to any PlantUML build to get SVG/PNG):\n\n\
                            \x20 tree             structure: packages, definitions, and\n\
                            \x20                  usages with attribute compartments, plus\n\
                            \x20                  composition/typing/specialization edges\n\
                            \x20 interconnection  parts as nested blocks with ports;\n\
                            \x20                  connections, interfaces, bindings, and\n\
                            \x20                  flows as edges between their ends\n\
                            \x20 state            state machines: states, transitions\n\
                            \x20                  (trigger [guard] / effect), entry/do/exit\n\
                            \x20 action           action flows: actions, control nodes,\n\
                            \x20                  successions, dashed flow edges\n\
                            \x20 sequence         lifelines and messages between events,\n\
                            \x20                  ordered by event successions\n\
                            \x20 case             use cases: actors, subjects, objectives,\n\
                            \x20                  «include» edges\n\
                            \x20 mixed            everything on one canvas: structure,\n\
                            \x20                  connectors, behaviors, cases, typing\n\n\
                            Comment/doc bodies attach as notes (--no-notes to\n\
                            omit); --color keys node colors on the metaclass;\n\
                            --link-template embeds [[hyperlinks]] carried into\n\
                            rendered SVG.\n\n\
                            Library elements never render as nodes; with --lib\n\
                            their names still appear in labels (attribute\n\
                            types, supertypes, definition ports).\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 viz model.sysml\n\
                            \x20 sysmlv2 viz model.sysml --view interconnection\n\
                            \x20 sysmlv2 viz model.sysml --element Pkg::Part -o part.puml\n\
                            \x20 sysmlv2 viz model.sysml --view mixed --color --link-template \"vscode://file/{file}:{line}\"\n\
                            \x20 sysmlv2 viz src/*.sysml --lib sysml.library/ | java -jar plantuml.jar -tsvg -p > model.svg")]
    Viz {
        /// Files to render; `-` reads stdin; optional when
        /// SYSMLV2_MODEL_DIR is set
        files: Vec<PathBuf>,
        /// View to render: tree, interconnection, state, action,
        /// sequence, case, or mixed. Default: tree — except when
        /// --element targets a view usage, whose own `render` member
        /// picks the style
        #[arg(long)]
        view: Option<String>,
        /// Root the diagram at this ::-qualified element
        #[arg(long)]
        element: Option<String>,
        /// Standard-library directory (names library references in labels)
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
        /// Lay the diagram out left-to-right instead of top-to-bottom
        #[arg(long)]
        horizontal: bool,
        /// Omit `= value` on attribute compartment lines
        #[arg(long)]
        no_values: bool,
        /// Omit comment/doc bodies (attached as notes by default)
        #[arg(long)]
        no_notes: bool,
        /// Hide metadata (annotation stereotypes and metadata nodes)
        #[arg(long)]
        hide_metadata: bool,
        /// Add inherited compartment lines (one explicit hop, ^-marked)
        #[arg(long)]
        show_inherited: bool,
        /// Render referenced standard-library types as marked nodes
        #[arg(long)]
        show_lib: bool,
        /// Draw «import» edges between rendered nodes
        #[arg(long)]
        show_imported: bool,
        /// Edge routing: polyline or ortho (default: PlantUML splines)
        #[arg(long)]
        line_style: Option<String>,
        /// Color nodes by metaclass family
        #[arg(long)]
        color: bool,
        /// Hyperlink template for nodes; placeholders {file} {line}
        /// {col} {qname} {id} (e.g. "vscode://file/{file}:{line}")
        #[arg(long)]
        link_template: Option<String>,
        /// Write the PlantUML text here instead of stdout
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Usage↔definition refactorings: extract / inline
    #[command(
        long_about = "Move between the usage-oriented and definition-oriented\n\
                      modeling styles:\n\
                      \n\
                      extract   a usage's inline body becomes a new definition,\n\
                      \x20         the usage retyped by it —\n\
                      \x20         `part engine : A { … }` becomes\n\
                      \x20         `part def Engine :> A { … }` + `part engine : Engine;`\n\
                      inline    a definition's body merges into its sole typed\n\
                      \x20         usage and the definition is deleted\n\
                      \n\
                      Inlining a definition just produced by extract restores the\n\
                      original text byte-for-byte. Both directions are verified\n\
                      commits: every carried reference is checked at its new home,\n\
                      newly unresolved references or body-context violations roll\n\
                      the edit back, and the touched usage's effective members\n\
                      must be structurally unchanged. Refusals name their reason\n\
                      (ineligible kind, header shape, name collision, outside\n\
                      references, …) and leave every file untouched."
    )]
    Refactor {
        #[command(subcommand)]
        op: RefactorOp,
    },
    /// Run the Language Server Protocol server over stdio
    #[cfg(feature = "lsp")]
    #[command(after_help = "Speaks LSP over stdio until the client ends the\n\
                            session — run it from an editor, not a terminal.\n\
                            Serves parse + body-context diagnostics on every\n\
                            change and whole-document formatting; position\n\
                            encoding negotiates utf-8 when offered (utf-16\n\
                            otherwise). Dialect follows the file extension\n\
                            (.kerml is KerML, everything else SysML).\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 lsp    (as an editor's configured server command)\n\
                            \x20 vim.lsp.start { cmd = { 'sysmlv2', 'lsp' } }    (Neovim config)")]
    Lsp {
        /// Standard-library directory: hover/definition/references/rename
        /// resolve standard-library names too (cached, ~0.15 s warm)
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
}

/// The two refactoring directions. Reads follow the ambient-input
/// convention; in-place writes require explicit file paths —
/// the fmt precedent for destructive verbs — and `--dry-run` prints the
/// would-be changes instead.
#[derive(Subcommand)]
enum RefactorOp {
    /// Extract a usage's inline body into a new definition
    #[command(after_help = "EXAMPLES:\n\
                            \x20 sysmlv2 refactor extract model.sysml Rig::engine\n\
                            \x20 sysmlv2 refactor extract model.sysml Rig::engine --name Motor\n\
                            \x20 sysmlv2 refactor extract Rig::engine --dry-run    (SYSMLV2_MODEL_DIR set)")]
    Extract {
        /// Input file (.sysml or .kerml); optional when SYSMLV2_MODEL_DIR
        /// is set (a leading qualified name is then a name, not a file)
        input: Option<PathBuf>,
        /// The ::-qualified usage name; arguments ending in
        /// `.sysml`/`.kerml` are further files joining the model
        args: Vec<String>,
        /// Definition name (default: UpperCamel of the usage's name)
        #[arg(long)]
        name: Option<String>,
        /// Print the would-be changes as a diff; write nothing
        #[arg(long)]
        dry_run: bool,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
    /// Inline a definition into its sole typed usage and delete it
    #[command(after_help = "Imports the deletion leaves unused are reported as\n\
                            `note:` lines, never removed.\n\n\
                            EXAMPLES:\n\
                            \x20 sysmlv2 refactor inline model.sysml Rig::Engine\n\
                            \x20 sysmlv2 refactor inline Rig::Engine --dry-run    (SYSMLV2_MODEL_DIR set)")]
    Inline {
        /// Input file (.sysml or .kerml); optional when SYSMLV2_MODEL_DIR
        /// is set (a leading qualified name is then a name, not a file)
        input: Option<PathBuf>,
        /// The ::-qualified definition name; arguments ending in
        /// `.sysml`/`.kerml` are further files joining the model
        args: Vec<String>,
        /// Print the would-be changes as a diff; write nothing
        #[arg(long)]
        dry_run: bool,
        /// Standard-library directory for reference resolution
        #[arg(long, env = "SYSMLV2_LIB_DIR")]
        lib: Option<PathBuf>,
    },
}

/// Render one query-result value: elements as `qualified::name (Metaclass)`
/// (anonymous elements keep just the metaclass), everything else through
/// the evaluator's own display.
fn render_query_value(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    v: &sysmlv2_parser::eval::Value,
) -> String {
    if let sysmlv2_parser::eval::Value::Element(e) | sysmlv2_parser::eval::Value::Unbound(e) = v {
        let ty = resolved.element_type(*e);
        return match resolved.element_qualified_name(*e) {
            Some(qn) => format!("{qn} ({ty})"),
            None => format!("<anonymous> ({ty})"),
        };
    }
    v.to_string()
}

/// `--indent` values: `tabs`, or a space count 1–16.
fn parse_indent_arg(s: &str) -> Result<Indent, String> {
    if s == "tabs" {
        return Ok(Indent::Tabs);
    }
    s.parse::<u8>()
        .ok()
        .filter(|n| (1..=16).contains(n))
        .map(Indent::Spaces)
        .ok_or_else(|| "expected `tabs` or a space count 1-16".to_string())
}

fn dialect_of(path: &Path) -> Dialect {
    if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
        Dialect::Kerml
    } else {
        Dialect::Sysml
    }
}

fn parse_file(path: &Path, src: &str) -> Parse {
    match dialect_of(path) {
        Dialect::Kerml => parse_kerml_source(src),
        Dialect::Sysml => parse_source(src),
    }
}

fn report(path: &Path, src: &str, diags: &[Diagnostic]) {
    let index = LineIndex::new(src);
    for d in diags {
        let severity = match d.severity {
            sysmlv2_parser::diag::Severity::Error => "error",
            sysmlv2_parser::diag::Severity::Warning => "warning",
        };
        let pos = index.line_col(d.span.start);
        let line = src.lines().nth(pos.line as usize - 1).unwrap_or("");
        eprintln!(
            "{severity}: {}\n  --> {}:{}:{}\n   |\n   | {}\n",
            d.message,
            path.display(),
            pos.line,
            pos.col,
            line.trim_end()
        );
    }
}

fn read(path: &Path) -> Result<String, ExitCode> {
    if path == Path::new("-") {
        let mut src = String::new();
        return std::io::Read::read_to_string(&mut std::io::stdin(), &mut src)
            .map(|_| src)
            .map_err(|e| {
                eprintln!("error: cannot read stdin: {e}");
                ExitCode::FAILURE
            });
    }
    std::fs::read_to_string(path).map_err(|e| {
        eprintln!("error: cannot read {}: {e}", path.display());
        ExitCode::FAILURE
    })
}

/// Load a delta base: a compact element array from `.json` or `.s2c`.
fn load_base_value(path: &Path) -> Result<serde_json::Value, ExitCode> {
    if path.extension().and_then(|e| e.to_str()) == Some("s2c") {
        let bytes = std::fs::read(path).map_err(|e| {
            eprintln!("error: cannot read {}: {e}", path.display());
            ExitCode::FAILURE
        })?;
        sysmlv2_cbor::from_cbor(&bytes).map_err(|e| {
            eprintln!("error: invalid base payload {}: {e}", path.display());
            ExitCode::FAILURE
        })
    } else {
        let text = read(path)?;
        serde_json::from_str(&text).map_err(|e| {
            eprintln!("error: invalid base JSON {}: {e}", path.display());
            ExitCode::FAILURE
        })
    }
}

/// The codec tables as one self-contained versioned JSON document:
/// everything a consumer needs to label s2c payload structure without
/// this toolkit — container magic, header version axes and flags, the
/// field-kind legend, both ordinal spaces (metaclass wire code =
/// array position, field ordinal = table position, both also spelled
/// explicitly), enum vocabularies, and each field's presence default
/// where the kind has one (bool, enum). Semantics live in `CBOR.md`.
fn codec_tables_doc() -> serde_json::Value {
    use sysmlv2_cbor::tables;
    let space = |set: &[(&str, &[tables::CborField])]| -> Vec<serde_json::Value> {
        set.iter()
            .enumerate()
            .map(|(code, (name, fields))| {
                let fields: Vec<serde_json::Value> = fields
                    .iter()
                    .enumerate()
                    .map(|(ordinal, (prop, kind, etbl, dflt))| {
                        let mut f = serde_json::Map::new();
                        f.insert("prop".into(), serde_json::json!(prop));
                        f.insert("ordinal".into(), serde_json::json!(ordinal));
                        f.insert("kind".into(), serde_json::json!(kind));
                        if *etbl != 255 {
                            f.insert("enum".into(), serde_json::json!(etbl));
                        }
                        match *kind {
                            tables::K_BOOL => {
                                f.insert("default".into(), serde_json::json!(*dflt == 1));
                            }
                            tables::K_ENUM => {
                                let value = if *dflt == 255 {
                                    serde_json::Value::Null
                                } else {
                                    serde_json::json!(
                                        tables::ENUM_TABLES[*etbl as usize][*dflt as usize]
                                    )
                                };
                                f.insert("default".into(), value);
                            }
                            _ => {}
                        }
                        serde_json::Value::Object(f)
                    })
                    .collect();
                serde_json::json!({ "name": name, "code": code, "fields": fields })
            })
            .collect()
    };
    let enums: Vec<serde_json::Value> = tables::ENUM_NAMES
        .iter()
        .zip(tables::ENUM_TABLES)
        .map(|(name, values)| serde_json::json!({ "name": name, "values": values }))
        .collect();
    serde_json::json!({
        "magic": sysmlv2_cbor::MAGIC
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>(),
        "versions": {
            "layout": sysmlv2_cbor::LAYOUT_VERSION,
            "tables": tables::CBOR_TABLES_VERSION,
            "scheme": sysmlv2_cbor::ID_SCHEME_VERSION,
        },
        "flags": {
            "elideIds": sysmlv2_cbor::FLAG_ELIDE_IDS,
            "fullForm": sysmlv2_cbor::FLAG_FULL_FORM,
            "delta": sysmlv2_cbor::FLAG_DELTA,
            "deltaPortable": sysmlv2_cbor::FLAG_DELTA_PORTABLE,
            "unitPaths": sysmlv2_cbor::FLAG_UNIT_PATHS,
            "impliedOwners": sysmlv2_cbor::FLAG_IMPLIED_OWNERS,
        },
        "kinds": {
            "bool": tables::K_BOOL,
            "str": tables::K_STR,
            "strList": tables::K_STR_LIST,
            "ref": tables::K_REF,
            "refList": tables::K_REF_LIST,
            "enum": tables::K_ENUM,
            "literal": tables::K_LITERAL,
            "elementId": tables::K_ELEMENT_ID,
        },
        "enums": enums,
        "metaclasses": space(tables::METACLASS_FIELDS),
        "fullMetaclasses": space(tables::FULL_METACLASS_FIELDS),
    })
}

/// A snapshot payload exactly as the file carries it: `.s2c` decodes
/// (id-elided snapshots re-derive their ids through `names` — a
/// digest-gated recovery, still payload identity), anything else
/// parses as a compact interchange element array. Never lifts — the
/// producer's ids are authoritative.
fn load_snapshot_value(
    path: &Path,
    names: &HashMap<String, String>,
) -> Result<serde_json::Value, ExitCode> {
    let value = if path.extension().and_then(|e| e.to_str()) == Some("s2c") {
        let bytes = std::fs::read(path).map_err(|e| {
            eprintln!("error: cannot read {}: {e}", path.display());
            ExitCode::FAILURE
        })?;
        decode_snapshot(&bytes, names).map_err(|e| {
            eprintln!("error: invalid snapshot payload {}: {e}", path.display());
            ExitCode::FAILURE
        })?
    } else {
        let text = read(path)?;
        serde_json::from_str(&text).map_err(|e| {
            eprintln!("error: invalid snapshot JSON {}: {e}", path.display());
            ExitCode::FAILURE
        })?
    };
    if !value.is_array() {
        eprintln!(
            "error: {}: not a snapshot (compact element array)",
            path.display()
        );
        return Err(ExitCode::FAILURE);
    }
    Ok(value)
}

/// Decode snapshot CBOR to its compact element array; id-elided
/// payloads re-derive their ids with library targets named through
/// `names`.
fn decode_snapshot(
    bytes: &[u8],
    names: &HashMap<String, String>,
) -> Result<serde_json::Value, sysmlv2_cbor::Error> {
    match sysmlv2_cbor::from_cbor(bytes) {
        Err(e) if e.to_string().contains("elided") => {
            sysmlv2_cbor::from_cbor_with(bytes, &|s| names.get(s).cloned())
        }
        other => other,
    }
}

/// State digest of a snapshot file (compact `.json` or `.s2c`) —
/// `None` when the file is not a snapshot this build decodes (a
/// delta, foreign JSON, another format entirely).
fn snapshot_file_digest(path: &Path, names: &HashMap<String, String>) -> Option<String> {
    let value = if path.extension().and_then(|e| e.to_str()) == Some("s2c") {
        decode_snapshot(&std::fs::read(path).ok()?, names).ok()?
    } else {
        serde_json::from_str(&std::fs::read_to_string(path).ok()?).ok()?
    };
    if !value.is_array() {
        return None;
    }
    Some(sysmlv2_cbor::state_digest(&value).ok()?.to_string())
}

/// Payload-looking files (`.s2c` / `.json`) under `dir`, recursively,
/// in sorted order.
fn payload_files_under(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() {
                stack.push(p);
            } else if matches!(p.extension().and_then(|e| e.to_str()), Some("s2c" | "json")) {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

/// `elementId → last qualified-name segment` for the standard
/// library at `lib` (empty without one) — the resolver id-derivation
/// surfaces (elision, elided deltas) name external targets with.
fn load_library_id_names(
    lib: Option<&Path>,
) -> Result<std::collections::HashMap<String, String>, ExitCode> {
    let Some(dir) = lib else {
        return Ok(Default::default());
    };
    let mut model = Model::new();
    match load_library(&mut model, dir) {
        Ok(cache) => {
            let names = library_name_map(&model)
                .into_iter()
                .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
                .collect();
            save_library_cache(&model, cache);
            Ok(names)
        }
        Err(e) => {
            eprintln!("error: cannot load library {}: {e}", dir.display());
            Err(ExitCode::FAILURE)
        }
    }
}

/// Re-key a unit-structure table (compact element indices → paths)
/// onto another emission of the same model, matching unit roots by
/// element id. Identity when `target` is the compact array itself.
fn remap_units(
    compact: &serde_json::Value,
    units: &[(usize, String)],
    target: &serde_json::Value,
) -> Vec<(usize, String)> {
    let id_of = |arr: &serde_json::Value, i: usize| -> Option<String> {
        arr.get(i)?.get("@id")?.as_str().map(str::to_owned)
    };
    let by_id: std::collections::HashMap<String, usize> = target
        .as_array()
        .map(|arr| {
            arr.iter()
                .enumerate()
                .filter_map(|(i, e)| {
                    e.get("@id")
                        .and_then(|v| v.as_str())
                        .map(|s| (s.to_owned(), i))
                })
                .collect()
        })
        .unwrap_or_default();
    let mut out: Vec<(usize, String)> = units
        .iter()
        .filter_map(|(i, path)| {
            by_id
                .get(&id_of(compact, *i)?)
                .map(|&ti| (ti, path.clone()))
        })
        .collect();
    out.sort_by_key(|&(i, _)| i);
    out
}

/// Write binary output (compact-form CBOR) to a file or raw stdout.
fn write_bytes(output: Option<&Path>, bytes: &[u8]) -> ExitCode {
    use std::io::Write;
    match output {
        Some(out) => {
            if let Err(e) = std::fs::write(out, bytes) {
                eprintln!("error: cannot write {}: {e}", out.display());
                return ExitCode::FAILURE;
            }
        }
        None => {
            if let Err(e) = std::io::stdout().write_all(bytes) {
                eprintln!("error: cannot write stdout: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    ExitCode::SUCCESS
}

/// Read command inputs, expanding `.kpar` project archives (KerML 10.3)
/// into their contained textual units. Checksum mismatches against the
/// archive's `.meta.json` warn but do not fail.
fn read_inputs(paths: &[PathBuf]) -> Result<Vec<(PathBuf, String)>, ExitCode> {
    let mut out = Vec::new();
    for path in paths {
        if path.extension().and_then(|e| e.to_str()) == Some("kpar") {
            let bytes = std::fs::read(path).map_err(|e| {
                eprintln!("error: cannot read {}: {e}", path.display());
                ExitCode::FAILURE
            })?;
            let archive = kpar::read(&bytes).map_err(|e| {
                eprintln!("error: {}: {e}", path.display());
                ExitCode::FAILURE
            })?;
            for name in &archive.checksum_mismatches {
                eprintln!(
                    "warning: {}: `{name}` does not match its .meta.json checksum",
                    path.display()
                );
            }
            for unit in archive.units {
                out.push((path.join(&unit.file_name), unit.source));
            }
        } else {
            out.push((path.clone(), read(path)?));
        }
    }
    Ok(out)
}

/// The ambient model context: when a verb's file
/// inputs are omitted and this variable names a directory, the
/// directory's `.sysml`/`.kerml` files form the model. Explicit inputs
/// always win — the variable only fills an absence.
const MODEL_DIR_VAR: &str = "SYSMLV2_MODEL_DIR";

/// Collect the model files under `dir`, depth-first with siblings in
/// name order, so unit order (and everything downstream of it) is
/// deterministic. Hidden entries are skipped; directory symlinks are
/// not followed (files reached through a symlinked name still count).
fn discover_model_files(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            if entry.file_name().to_string_lossy().starts_with('.') {
                continue;
            }
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                walk(&path, out)?;
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            ) {
                out.push(path);
            }
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(dir, &mut out)?;
    Ok(out)
}

/// Resolve a verb's input files: explicit paths pass through untouched;
/// an empty list falls back to the ambient model directory (with a
/// provenance note on stderr, suppressed by --quiet, so output never
/// silently depends on ambient state); with neither, the error names
/// both remedies.
fn resolve_inputs(explicit: Vec<PathBuf>, quiet: bool) -> Result<Vec<PathBuf>, ExitCode> {
    if !explicit.is_empty() {
        return Ok(explicit);
    }
    let Some(dir) = std::env::var_os(MODEL_DIR_VAR).filter(|v| !v.is_empty()) else {
        eprintln!(
            "error: no input files — provide input files, or set \
             {MODEL_DIR_VAR} to a model directory"
        );
        return Err(ExitCode::FAILURE);
    };
    let dir = PathBuf::from(dir);
    let files = discover_model_files(&dir).map_err(|e| {
        eprintln!(
            "error: cannot read {MODEL_DIR_VAR} directory {}: {e}",
            dir.display()
        );
        ExitCode::FAILURE
    })?;
    if files.is_empty() {
        eprintln!(
            "error: no .sysml/.kerml files under {} ({MODEL_DIR_VAR})",
            dir.display()
        );
        return Err(ExitCode::FAILURE);
    }
    if !quiet {
        eprintln!(
            "sysmlv2: model = {} file{} from {} ({MODEL_DIR_VAR})",
            files.len(),
            if files.len() == 1 { "" } else { "s" },
            dir.display()
        );
    }
    Ok(files)
}

/// Shared front half of the inspection verbs (describe/members): the
/// eval/query positional convention — arguments ending in a model
/// extension are files, the leading positional joins that
/// classification (an existing *file* path counts as a file — a
/// directory or case-folded match does not), exactly one
/// non-file argument remains as the qualified name — then ambient
/// fallback, library load, parse gate, and model resolution.
fn resolve_model_and_name(
    input: Option<PathBuf>,
    args: Vec<String>,
    lib: Option<&Path>,
    quiet: bool,
) -> Result<(sysmlv2_parser::json::ResolvedModel, String), ExitCode> {
    let is_file = |s: &str| s.ends_with(".sysml") || s.ends_with(".kerml") || s == "-";
    let (extra_files, mut names): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| is_file(a));
    let mut files: Vec<PathBuf> = Vec::new();
    if let Some(input) = input {
        let s = input.display().to_string();
        if is_file(&s) || input.is_file() {
            files.push(input);
        } else {
            names.insert(0, s);
        }
    }
    files.extend(extra_files.iter().map(PathBuf::from));
    let [qname] = names.as_slice() else {
        eprintln!(
            "error: expected exactly one qualified name, got {}",
            names.len()
        );
        return Err(ExitCode::FAILURE);
    };
    let qname = qname.clone();
    let files = resolve_inputs(files, quiet)?;
    let mut model = Model::new();
    let mut lib_cache_path = None;
    if let Some(lib) = lib {
        lib_cache_path = load_library(&mut model, lib).map_err(|e| {
            eprintln!("error: cannot load library {}: {e}", lib.display());
            ExitCode::FAILURE
        })?;
    }
    for path in &files {
        let src = read(path)?;
        let unit = model.add_source(path.display().to_string(), &src);
        if !unit.diagnostics.is_empty() {
            let diags = unit.diagnostics.clone();
            report(path, &src, &diags);
            return Err(ExitCode::FAILURE);
        }
    }
    let resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
    save_library_cache(&model, lib_cache_path);
    Ok((resolved, qname))
}

/// The refactor verbs' front half: the describe/members positional
/// convention (files + exactly one qualified name), the fmt write
/// discipline (ambient inputs drive `--dry-run` only; stdin never),
/// then a transform `Session` over the files with the library loaded.
fn refactor_session(
    input: Option<PathBuf>,
    args: Vec<String>,
    lib: Option<&Path>,
    dry_run: bool,
    quiet: bool,
) -> Result<(sysmlv2_transform::Session, String), ExitCode> {
    let is_file = |s: &str| s.ends_with(".sysml") || s.ends_with(".kerml") || s == "-";
    let (extra_files, mut names): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|a| is_file(a));
    let mut files: Vec<PathBuf> = Vec::new();
    if let Some(input) = input {
        let s = input.display().to_string();
        if is_file(&s) || input.is_file() {
            files.push(input);
        } else {
            names.insert(0, s);
        }
    }
    files.extend(extra_files.iter().map(PathBuf::from));
    let [qname] = names.as_slice() else {
        eprintln!(
            "error: expected exactly one qualified name, got {}",
            names.len()
        );
        return Err(ExitCode::FAILURE);
    };
    let qname = qname.clone();
    if files.iter().any(|f| f == Path::new("-")) {
        eprintln!("error: stdin (`-`) cannot be rewritten in place; pass file paths");
        return Err(ExitCode::FAILURE);
    }
    if files.is_empty() && !dry_run {
        eprintln!(
            "error: no input files — refactor rewrites files in place, so ambient \
             {MODEL_DIR_VAR} inputs apply to --dry-run only; pass explicit paths"
        );
        return Err(ExitCode::FAILURE);
    }
    let files = resolve_inputs(files, quiet)?;
    let mut sources = Vec::new();
    for path in &files {
        let src = read(path)?;
        sources.push((path.display().to_string(), src));
    }
    let mut session = match sysmlv2_transform::Session::from_sources(sources.clone()) {
        Ok(s) => s,
        Err(sysmlv2_transform::SessionError::Parse { unit, diagnostics }) => {
            match sources.iter().find(|(n, _)| *n == unit) {
                Some((_, src)) => report(Path::new(&unit), src, &diagnostics),
                None => eprintln!("error: {unit} does not parse"),
            }
            return Err(ExitCode::FAILURE);
        }
        Err(e) => {
            eprintln!("error: {e}");
            return Err(ExitCode::FAILURE);
        }
    };
    if let Some(lib) = lib {
        if let Err(e) = session.load_library(lib) {
            eprintln!("error: cannot load library {}: {e}", lib.display());
            return Err(ExitCode::FAILURE);
        }
    }
    Ok((session, qname))
}

/// Execute one refactor direction: resolve the name, run the verified
/// edit (dry runs go through the same pipeline against copies), print
/// findings as `note:` lines, then either print the would-be diff or
/// write every changed unit back in place.
fn run_refactor(op: RefactorOp, quiet: bool) -> ExitCode {
    let (input, args, name, dry_run, lib, is_extract) = match op {
        RefactorOp::Extract {
            input,
            args,
            name,
            dry_run,
            lib,
        } => (input, args, name, dry_run, lib, true),
        RefactorOp::Inline {
            input,
            args,
            dry_run,
            lib,
        } => (input, args, None, dry_run, lib, false),
    };
    let (mut session, qname) = match refactor_session(input, args, lib.as_deref(), dry_run, quiet) {
        Ok(v) => v,
        Err(code) => return code,
    };
    let Some(target) = session.resolved().resolve_qualified(&qname) else {
        eprintln!("error: cannot resolve `{qname}`");
        return ExitCode::FAILURE;
    };
    // Summary facts read before the edit — a commit advances the session.
    let summary = if is_extract {
        let def_name = match &name {
            Some(n) => n.clone(),
            None => session
                .resolved()
                .element_name(target)
                .map(sysmlv2_transform::synthesized_definition_name)
                .unwrap_or_default(),
        };
        format!(
            "extracted '{}' from `{qname}`",
            sysmlv2_transform::spell_name(&def_name)
        )
    } else {
        format!("inlined `{qname}`")
    };
    let before: Vec<(String, String)> = session
        .units()
        .map(|(_, n, s)| (n.to_string(), s.to_string()))
        .collect();
    let mut edit = session.edit();
    if is_extract {
        edit.extract_definition(target, name.as_deref());
    } else {
        edit.inline_definition(target);
    }
    let result = if dry_run { edit.check() } else { edit.commit() };
    let report = match result {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    if dry_run {
        for f in &report.findings {
            eprintln!("note: {f}");
        }
        for (unit_name, old) in &before {
            let mut spl: Vec<_> = report
                .splices
                .iter()
                .filter(|s| s.unit == *unit_name)
                .collect();
            if spl.is_empty() {
                continue;
            }
            spl.sort_by_key(|s| s.start);
            let mut new = String::with_capacity(old.len());
            let mut cursor = 0usize;
            for s in &spl {
                new.push_str(&old[cursor..s.start as usize]);
                new.push_str(&s.text);
                cursor = s.end as usize;
            }
            new.push_str(&old[cursor..]);
            print_unit_diff(unit_name, old, &new);
        }
        return ExitCode::SUCCESS;
    }
    let after: Vec<(String, String)> = session
        .units()
        .map(|(_, n, s)| (n.to_string(), s.to_string()))
        .collect();
    if before.len() != after.len()
        || before
            .iter()
            .zip(&after)
            .any(|((before_name, _), (after_name, _))| before_name != after_name)
    {
        eprintln!("error: internal refactor failure: session unit order changed");
        return ExitCode::FAILURE;
    }
    let changes: Vec<RefactorFileChange> = before
        .iter()
        .zip(&after)
        .filter(|((_, old), (_, new))| old != new)
        .map(|((unit_name, old), (_, new))| RefactorFileChange {
            path: PathBuf::from(unit_name),
            old: old.clone(),
            new: new.clone(),
        })
        .collect();
    let cleanup_warnings = match persist_refactor_changes(&changes) {
        Ok(warnings) => warnings,
        Err(e) => {
            eprintln!("error: refactor was not written: {e}");
            return ExitCode::FAILURE;
        }
    };
    for f in &report.findings {
        eprintln!("note: {f}");
    }
    for warning in cleanup_warnings {
        eprintln!("warning: {warning}");
    }
    if !quiet {
        for change in &changes {
            eprintln!("{summary} — rewrote {}", change.path.display());
        }
    }
    ExitCode::SUCCESS
}

/// One changed user unit waiting to be persisted after the transform
/// engine has committed and verified the whole model in memory.
#[derive(Debug)]
struct RefactorFileChange {
    path: PathBuf,
    old: String,
    new: String,
}

#[derive(Debug)]
struct StagedRefactorFile {
    display_path: PathBuf,
    target: PathBuf,
    new_path: PathBuf,
    backup_path: PathBuf,
}

#[derive(Debug)]
struct RefactorFileMetadata {
    permissions: Permissions,
    #[cfg(all(unix, not(target_os = "wasi")))]
    uid: u32,
    #[cfg(all(unix, not(target_os = "wasi")))]
    gid: u32,
    #[cfg(all(unix, not(target_os = "wasi")))]
    xattrs: Vec<(std::ffi::OsString, Vec<u8>)>,
}

/// Persist a verified multi-file refactor as one recoverable operation:
/// preflight every target, stage both new text and rollback copies beside
/// their files, recheck for concurrent changes, then replace. A failed
/// replacement restores unchanged earlier targets and retains a recovery
/// copy rather than knowingly overwriting a later external edit.
fn persist_refactor_changes(changes: &[RefactorFileChange]) -> Result<Vec<String>, String> {
    persist_refactor_changes_with(changes, |from, to| std::fs::rename(from, to))
}

fn persist_refactor_changes_with(
    changes: &[RefactorFileChange],
    mut replace: impl FnMut(&Path, &Path) -> std::io::Result<()>,
) -> Result<Vec<String>, String> {
    let mut prepared = Vec::with_capacity(changes.len());
    let mut write_guards = Vec::with_capacity(changes.len());
    let mut targets = HashSet::with_capacity(changes.len());
    for change in changes {
        let target = refactor_target_path(&change.path).map_err(|e| {
            format!(
                "cannot resolve {} before writing: {e}",
                change.path.display()
            )
        })?;
        if !targets.insert(target.clone()) {
            return Err(format!(
                "{} names the same file more than once",
                change.path.display()
            ));
        }
        let current = std::fs::read(&target).map_err(|e| {
            format!(
                "cannot reread {} before writing: {e}",
                change.path.display()
            )
        })?;
        if current != change.old.as_bytes() {
            return Err(format!(
                "{} changed on disk while the refactor was running",
                change.path.display()
            ));
        }
        let guard = OpenOptions::new()
            .write(true)
            .open(&target)
            .map_err(|e| format!("cannot open {} for writing: {e}", change.path.display()))?;
        let metadata = refactor_file_metadata(&guard)
            .map_err(|e| format!("cannot inspect {}: {e}", change.path.display()))?;
        prepared.push((target, metadata));
        write_guards.push(guard);
    }

    let mut staged = Vec::with_capacity(changes.len());
    for (change, (target, metadata)) in changes.iter().zip(&prepared) {
        let new_path = match write_refactor_sidecar(target, "new", &change.new, metadata) {
            Ok(path) => path,
            Err(e) => {
                cleanup_refactor_sidecars(&staged, &HashSet::new());
                return Err(format!(
                    "cannot stage {} before writing: {e}",
                    change.path.display()
                ));
            }
        };
        let backup_path = match write_refactor_sidecar(target, "old", &change.old, metadata) {
            Ok(path) => path,
            Err(e) => {
                let _ = std::fs::remove_file(&new_path);
                cleanup_refactor_sidecars(&staged, &HashSet::new());
                return Err(format!(
                    "cannot stage rollback copy for {}: {e}",
                    change.path.display()
                ));
            }
        };
        staged.push(StagedRefactorFile {
            display_path: change.path.clone(),
            target: target.clone(),
            new_path,
            backup_path,
        });
    }
    drop(write_guards);

    // Staging may take time: refuse to overwrite an editor or process
    // that changed a source after the first preflight read.
    for (change, entry) in changes.iter().zip(&staged) {
        match std::fs::read(&entry.target) {
            Ok(current) if current == change.old.as_bytes() => {}
            Ok(_) => {
                cleanup_refactor_sidecars(&staged, &HashSet::new());
                return Err(format!(
                    "{} changed on disk while the refactor was being staged",
                    entry.display_path.display()
                ));
            }
            Err(e) => {
                cleanup_refactor_sidecars(&staged, &HashSet::new());
                return Err(format!(
                    "cannot recheck {} before writing: {e}",
                    entry.display_path.display()
                ));
            }
        }
    }

    for (applied, (change, entry)) in changes.iter().zip(&staged).enumerate() {
        // Check each target again immediately before its replacement. This
        // catches an editor save that races the earlier all-file recheck;
        // previously replaced files still roll back, while the external
        // edit remains untouched.
        let write_error = match std::fs::read(&entry.target) {
            Ok(current) if current != change.old.as_bytes() => Some(format!(
                "{} changed on disk before it could be replaced",
                entry.display_path.display()
            )),
            Err(e) => Some(format!(
                "cannot recheck {} before replacement: {e}",
                entry.display_path.display()
            )),
            Ok(_) => replace(&entry.new_path, &entry.target)
                .err()
                .map(|e| format!("cannot replace {}: {e}", entry.display_path.display())),
        };
        if let Some(write_error) = write_error {
            let mut retained_backups = HashSet::new();
            let mut rollback_errors = Vec::new();
            for previous_index in (0..applied).rev() {
                let previous = &staged[previous_index];
                let rollback_error = match std::fs::read(&previous.target) {
                    Ok(current) if current != changes[previous_index].new.as_bytes() => Some(
                        "changed after the refactor replaced it; external edit was preserved"
                            .to_string(),
                    ),
                    Err(e) => Some(format!("cannot recheck before rollback: {e}")),
                    Ok(_) => replace(&previous.backup_path, &previous.target)
                        .err()
                        .map(|e| e.to_string()),
                };
                if let Some(e) = rollback_error {
                    retained_backups.insert(previous.backup_path.clone());
                    rollback_errors.push(format!(
                        "{} ({e}; recovery copy: {})",
                        previous.display_path.display(),
                        previous.backup_path.display()
                    ));
                }
            }
            cleanup_refactor_sidecars(&staged, &retained_backups);
            let mut message = write_error;
            if rollback_errors.is_empty() {
                message.push_str(&format!("; rolled back {applied} earlier file(s)"));
            } else {
                message.push_str("; rollback incomplete for ");
                message.push_str(&rollback_errors.join(", "));
            }
            return Err(message);
        }
    }

    let mut warnings = Vec::new();
    for entry in &staged {
        if let Err(e) = std::fs::remove_file(&entry.backup_path) {
            warnings.push(format!(
                "could not remove rollback copy {}: {e}",
                entry.backup_path.display()
            ));
        }
    }
    Ok(warnings)
}

#[cfg(not(target_os = "wasi"))]
fn refactor_target_path(path: &Path) -> std::io::Result<PathBuf> {
    // Follow symlinks before replacing the file so an in-place refactor
    // retains the link instead of replacing the directory entry itself.
    std::fs::canonicalize(path)
}

#[cfg(target_os = "wasi")]
fn refactor_target_path(path: &Path) -> std::io::Result<PathBuf> {
    // WASI preview1 preopen paths are already capability-resolved and
    // canonicalize is unsupported by Node's WASI filesystem adapter.
    Ok(path.to_path_buf())
}

fn write_refactor_sidecar(
    target: &Path,
    kind: &str,
    text: &str,
    metadata: &RefactorFileMetadata,
) -> std::io::Result<PathBuf> {
    let parent = target.parent().unwrap_or_else(|| Path::new("."));
    let file_name = target.file_name().ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, "target has no file name")
    })?;
    for _ in 0..16 {
        let mut sidecar_name = std::ffi::OsString::from(".");
        sidecar_name.push(file_name);
        sidecar_name.push(format!(".sysmlv2-{kind}-{}", uuid::Uuid::new_v4()));
        let path = parent.join(sidecar_name);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        match options.open(&path) {
            Ok(mut file) => {
                let result = (|| {
                    file.write_all(text.as_bytes())?;
                    set_refactor_sidecar_metadata(&file, metadata)?;
                    file.sync_all()
                })();
                if let Err(e) = result {
                    drop(file);
                    let _ = std::fs::remove_file(&path);
                    return Err(e);
                }
                return Ok(path);
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
    Err(std::io::Error::new(
        std::io::ErrorKind::AlreadyExists,
        "could not allocate a unique sidecar name",
    ))
}

fn refactor_file_metadata(file: &std::fs::File) -> std::io::Result<RefactorFileMetadata> {
    let metadata = file.metadata()?;
    #[cfg(all(unix, not(target_os = "wasi")))]
    {
        use std::os::unix::fs::MetadataExt;
        use xattr::FileExt;

        if metadata.nlink() != 1 {
            return Err(std::io::Error::other(format!(
                "has {} hard links; refusing to split linked paths during atomic replacement",
                metadata.nlink()
            )));
        }
        let mut xattrs = Vec::new();
        match file.list_xattr() {
            Ok(names) => {
                for name in names {
                    if let Some(value) = file.get_xattr(&name)? {
                        xattrs.push((name, value));
                    }
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Unsupported => {}
            Err(e) => return Err(e),
        }
        Ok(RefactorFileMetadata {
            permissions: metadata.permissions(),
            uid: metadata.uid(),
            gid: metadata.gid(),
            xattrs,
        })
    }
    #[cfg(not(all(unix, not(target_os = "wasi"))))]
    Ok(RefactorFileMetadata {
        permissions: metadata.permissions(),
    })
}

#[cfg(all(unix, not(target_os = "wasi")))]
fn set_refactor_sidecar_metadata(
    file: &std::fs::File,
    metadata: &RefactorFileMetadata,
) -> std::io::Result<()> {
    use std::os::unix::fs::fchown;
    use xattr::FileExt;

    fchown(file, Some(metadata.uid), Some(metadata.gid))?;
    for (name, value) in &metadata.xattrs {
        file.set_xattr(name, value)?;
    }
    file.set_permissions(metadata.permissions.clone())
}

#[cfg(all(not(unix), not(target_os = "wasi")))]
fn set_refactor_sidecar_metadata(
    file: &std::fs::File,
    metadata: &RefactorFileMetadata,
) -> std::io::Result<()> {
    file.set_permissions(metadata.permissions.clone())
}

#[cfg(target_os = "wasi")]
fn set_refactor_sidecar_metadata(
    _file: &std::fs::File,
    _metadata: &RefactorFileMetadata,
) -> std::io::Result<()> {
    // WASI preview1 has no chmod-equivalent. Files created through a
    // preopen inherit the host adapter's normal creation permissions.
    Ok(())
}

fn cleanup_refactor_sidecars(staged: &[StagedRefactorFile], retain: &HashSet<PathBuf>) {
    for entry in staged {
        let _ = std::fs::remove_file(&entry.new_path);
        if !retain.contains(&entry.backup_path) {
            let _ = std::fs::remove_file(&entry.backup_path);
        }
    }
}

/// One trimmed hunk per changed unit: common prefix/suffix lines are
/// elided, the middle prints as `-`/`+` lines (1-based line numbers,
/// unified-style header). Both refactor ops touch one contiguous region per
/// unit, so a single hunk is exact.
fn print_unit_diff(unit: &str, old: &str, new: &str) {
    let o: Vec<&str> = old.split_inclusive('\n').collect();
    let n: Vec<&str> = new.split_inclusive('\n').collect();
    let mut p = 0;
    while p < o.len() && p < n.len() && o[p] == n[p] {
        p += 1;
    }
    let mut s = 0;
    while s < o.len() - p && s < n.len() - p && o[o.len() - 1 - s] == n[n.len() - 1 - s] {
        s += 1;
    }
    println!("--- {unit}");
    println!(
        "@@ -{},{} +{},{} @@",
        p + 1,
        o.len() - p - s,
        p + 1,
        n.len() - p - s
    );
    for l in &o[p..o.len() - s] {
        print!("-{l}");
        if !l.ends_with('\n') {
            println!();
        }
    }
    for l in &n[p..n.len() - s] {
        print!("+{l}");
        if !l.ends_with('\n') {
            println!();
        }
    }
}

/// Help echoes the active ambient context: with
/// SYSMLV2_MODEL_DIR set, the top level and every verb that honors
/// ambient inputs get a trailing `model context:` line appended to
/// their help footer, so `--help` confirms what a bare invocation
/// would run on. Without the variable, help is untouched.
fn ambient_help(mut cmd: clap::Command) -> clap::Command {
    let Some(dir) = std::env::var_os(MODEL_DIR_VAR).filter(|v| !v.is_empty()) else {
        return cmd;
    };
    let dir = PathBuf::from(dir);
    let count = match discover_model_files(&dir) {
        Ok(files) => match files.len() {
            0 => "no model files".to_string(),
            1 => "1 model file".to_string(),
            n => format!("{n} model files"),
        },
        Err(e) => format!("unreadable: {e}"),
    };
    let note = format!(
        "model context: {} ({MODEL_DIR_VAR} — {count}); file inputs may be omitted",
        dir.display()
    );
    fn append(cmd: clap::Command, note: &str) -> clap::Command {
        let text = match cmd.get_after_help() {
            Some(existing) => format!("{existing}\n\n{note}"),
            None => note.to_string(),
        };
        cmd.after_help(text)
    }
    // Feature gates decide which verbs exist, so collect the present
    // ones rather than naming a fixed list into mut_subcommand (which
    // panics on absent names).
    let verbs: Vec<String> = cmd
        .get_subcommands()
        .map(|s| s.get_name().to_string())
        .filter(|n| {
            matches!(
                n.as_str(),
                "convert"
                    | "fmt"
                    | "check"
                    | "verify"
                    | "eval"
                    | "query"
                    | "describe"
                    | "members"
                    | "parse"
                    | "viz"
                    | "refactor"
            )
        })
        .collect();
    cmd = append(cmd, &note);
    for name in verbs {
        let note = if name == "fmt" {
            format!("{note} (--check only)")
        } else if name == "refactor" {
            format!("{note} (--dry-run only)")
        } else {
            note.clone()
        };
        cmd = cmd.mut_subcommand(name, |sub| append(sub, &note));
    }
    cmd
}

/// The tallying bucket a constraint's verdict falls in.
#[cfg(feature = "solve")]
enum VerdictCat {
    Sat,
    Vio,
    Und,
}

/// Render one constraint's combined verdict (evaluation, then propagation,
/// then Z3) into a display string and its tally bucket. Mirrors the
/// precedence in [`sysmlv2_solve::verify_constraints`]: a definitive
/// propagation conclusion pre-empts the solver, which only reports what
/// propagation left open.
#[cfg(feature = "solve")]
fn verdict_line(
    verdict: &sysmlv2_parser::check::ConstraintVerdict,
    propagate: Option<&sysmlv2_solve::PropagateOutcome>,
    solve: Option<&sysmlv2_solve::SolveOutcome>,
) -> (String, VerdictCat) {
    use sysmlv2_parser::check::ConstraintVerdict;
    use sysmlv2_solve::{PropagateOutcome, SolveOutcome};
    match verdict {
        ConstraintVerdict::Satisfied => ("satisfied".to_string(), VerdictCat::Sat),
        ConstraintVerdict::Violated => ("VIOLATED".to_string(), VerdictCat::Vio),
        ConstraintVerdict::Undecided(why) => match propagate {
            Some(PropagateOutcome::Satisfied) => (
                "satisfied (propagation: holds for all values in the narrowed ranges)".to_string(),
                VerdictCat::Sat,
            ),
            Some(PropagateOutcome::Violated) => (
                "VIOLATED (propagation: false for all values in the narrowed ranges)".to_string(),
                VerdictCat::Vio,
            ),
            Some(PropagateOutcome::Unsatisfiable) => (
                "VIOLATED (propagation: domains contract to empty — unsatisfiable)".to_string(),
                VerdictCat::Vio,
            ),
            _ => match solve {
                Some(SolveOutcome::Valid) => (
                    "satisfied (z3: holds for all values of unbound features)".to_string(),
                    VerdictCat::Sat,
                ),
                Some(SolveOutcome::Unsatisfiable) => (
                    "VIOLATED (z3: unsatisfiable — no assignment can make this hold)".to_string(),
                    VerdictCat::Vio,
                ),
                Some(SolveOutcome::Satisfiable(w)) => {
                    let vals: Vec<String> = w.iter().map(|(n, v)| format!("{n} = {v}")).collect();
                    (
                        format!(
                            "undecided ({why}) — z3: satisfiable, e.g. {}",
                            vals.join(", ")
                        ),
                        VerdictCat::Und,
                    )
                }
                Some(SolveOutcome::Unknown(m)) => {
                    (format!("undecided ({why}; z3: {m})"), VerdictCat::Und)
                }
                None => match propagate {
                    Some(PropagateOutcome::Unsupported(m)) => (
                        format!("undecided ({why}; propagation: {m})"),
                        VerdictCat::Und,
                    ),
                    _ => (format!("undecided ({why})"), VerdictCat::Und),
                },
            },
        },
    }
}

/// Append the evaluated feature values to a violated verdict line —
/// `VIOLATED (with reserveKg = 0.10)` — so the reader sees *why*
/// without re-deriving the bindings. Only bound references contribute;
/// non-violated lines pass through untouched.
#[cfg(feature = "solve")]
fn with_bindings(
    line: String,
    cat: &VerdictCat,
    bindings: &[sysmlv2_parser::check::ConstraintBinding],
) -> String {
    if !matches!(cat, VerdictCat::Vio) {
        return line;
    }
    let vals: Vec<String> = bindings
        .iter()
        .filter_map(|b| b.value.as_ref().map(|v| format!("{} = {v}", b.feature)))
        .collect();
    if vals.is_empty() {
        line
    } else {
        format!("{line} (with {})", vals.join(", "))
    }
}

/// Run the requested verification stage over `model` and print per-
/// constraint verdicts (plus narrowed ranges under `--ranges`). Returns a
/// failure exit code iff any constraint is violated.
#[cfg(feature = "solve")]
fn verify_and_report(
    model: &Model,
    boundary: usize,
    sources: &[(&PathBuf, String)],
    ranges: bool,
    solve: bool,
    z3: Option<PathBuf>,
) -> ExitCode {
    use sysmlv2_solve::{PropagateConfig, SolverConfig};
    let indexes: Vec<LineIndex> = sources.iter().map(|(_, src)| LineIndex::new(src)).collect();
    let (mut sat, mut vio, mut und) = (0usize, 0usize, 0usize);

    let mut print_one = |unit: usize,
                         start: u32,
                         name: &Option<String>,
                         etype: &str,
                         context: Option<&str>,
                         line: String,
                         cat: VerdictCat| {
        match cat {
            VerdictCat::Sat => sat += 1,
            VerdictCat::Vio => vio += 1,
            VerdictCat::Und => und += 1,
        }
        let (path, _) = &sources[unit - boundary];
        let pos = indexes[unit - boundary].line_col(start);
        let ctx = context
            .map(|c| format!(", satisfies {c}"))
            .unwrap_or_default();
        println!(
            "{}:{}:{}  {} ({}{}): {}",
            path.display(),
            pos.line,
            pos.col,
            name.as_deref().unwrap_or("<anonymous>"),
            etype,
            ctx,
            line
        );
    };

    // Ranges to print once the verdicts are out (only under --ranges).
    let mut narrowed: Vec<sysmlv2_solve::FeatureRange> = Vec::new();

    if !ranges && !solve {
        // Plain evaluation stage — no propagation, no solver.
        for c in sysmlv2_parser::check::check_constraints(model) {
            let (line, cat) = verdict_line(&c.verdict, None, None);
            let line = with_bindings(line, &cat, &c.bindings);
            print_one(
                c.unit,
                c.span.start,
                &c.name,
                c.element_type,
                c.context.as_deref(),
                line,
                cat,
            );
        }
    } else {
        let cfg = SolverConfig {
            z3_path: z3,
            ..Default::default()
        };
        let report = match sysmlv2_solve::verify_constraints(
            model,
            solve.then_some(&cfg),
            &PropagateConfig::default(),
        ) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error: {e}");
                return ExitCode::FAILURE;
            }
        };
        for c in &report.constraints {
            let (line, cat) = verdict_line(&c.verdict, c.propagate.as_ref(), c.solve.as_ref());
            let line = with_bindings(line, &cat, &c.bindings);
            print_one(
                c.unit,
                c.span.start,
                &c.name,
                c.element_type,
                None,
                line,
                cat,
            );
        }
        // Satisfaction claims expand to subject-bound verdicts at the
        // evaluation tier (propagation/solving see the unbound
        // originals above).
        let mut rm = sysmlv2_parser::json::ResolvedModel::build(model);
        for c in sysmlv2_parser::check::satisfaction_checks(model, &mut rm) {
            let (line, cat) = verdict_line(&c.verdict, None, None);
            print_one(
                c.unit,
                c.span.start,
                &c.name,
                c.element_type,
                c.context.as_deref(),
                line,
                cat,
            );
        }
        if ranges {
            narrowed = report.ranges.into_iter().filter(|r| r.narrowed).collect();
        }
    }

    println!("{sat} satisfied, {vio} violated, {und} undecided");
    if !narrowed.is_empty() {
        println!("\nnarrowed ranges:");
        for r in &narrowed {
            match &r.unit {
                Some(u) => println!("  {} ∈ {} [{u}]", r.feature, r.range),
                None => println!("  {} ∈ {}", r.feature, r.range),
            }
        }
    }
    if vio > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn main() -> ExitCode {
    use clap::{CommandFactory, FromArgMatches};
    let cmd = ambient_help(Cli::command());
    let cli = Cli::from_arg_matches(&cmd.get_matches()).unwrap_or_else(|e| e.exit());
    let quiet = cli.quiet;
    // Spelled power-product unit expansion is on by default; the flag or
    // `SYSMLV2_UNIT_SPELLINGS=off` opts out.
    if cli.no_unit_spellings
        || std::env::var("SYSMLV2_UNIT_SPELLINGS").is_ok_and(|v| v == "off" || v == "0")
    {
        sysmlv2_parser::eval::set_unit_spelling_expansion(false);
    }
    match cli.command {
        Command::Convert {
            inputs,
            to,
            output,
            lib,
            flexo,
            min_qual,
            elide_ids,
            delta_base,
            delta_portable,
            indent,
            library,
        } => {
            if library {
                if !inputs.is_empty() {
                    eprintln!(
                        "error: --library takes no inputs (the --lib directory is the input)"
                    );
                    return ExitCode::FAILURE;
                }
                if !matches!(to, Target::CompactJson | Target::CompactCbor) {
                    eprintln!("error: --library targets compact-json or compact-cbor");
                    return ExitCode::FAILURE;
                }
                if flexo || min_qual || elide_ids || delta_base.is_some() || delta_portable {
                    eprintln!("error: --library composes with no other conversion flags");
                    return ExitCode::FAILURE;
                }
                let dir = lib.as_ref().expect("--library requires --lib");
                let mut model = Model::new();
                let lib_cache_path = match load_library(&mut model, dir) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", dir.display());
                        return ExitCode::FAILURE;
                    }
                };
                save_library_cache(&model, lib_cache_path);
                let (json, units) =
                    sysmlv2_parser::json::library_to_compact_json_with_units(&model);
                if matches!(to, Target::CompactCbor) {
                    return match sysmlv2_cbor::to_compact_cbor_with_units(&json, &units) {
                        Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                        Err(e) => {
                            eprintln!("error: cannot encode CBOR: {e}");
                            ExitCode::FAILURE
                        }
                    };
                }
                let text = serde_json::to_string_pretty(&json).unwrap();
                match output {
                    Some(out) => {
                        if let Err(e) = std::fs::write(&out, text + "\n") {
                            eprintln!("error: cannot write {}: {e}", out.display());
                            return ExitCode::FAILURE;
                        }
                    }
                    None => println!("{text}"),
                }
                return ExitCode::SUCCESS;
            }
            let inputs = match resolve_inputs(inputs, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            if flexo && matches!(to, Target::CompactCbor | Target::FullCbor) {
                eprintln!(
                    "error: --flexo wraps JSON change records; CBOR carries \
                     the bare element array"
                );
                return ExitCode::FAILURE;
            }
            if elide_ids && !matches!(to, Target::CompactCbor) {
                eprintln!("error: --elide-ids applies to --to compact-cbor");
                return ExitCode::FAILURE;
            }
            if delta_portable && delta_base.is_none() {
                eprintln!("error: --delta-portable needs --delta-base");
                return ExitCode::FAILURE;
            }
            if elide_ids && delta_portable {
                eprintln!(
                    "error: --elide-ids applies to strict deltas only \
                     (portable identities are explicit ids by design)"
                );
                return ExitCode::FAILURE;
            }
            // An .s2c input decodes to the compact element array up
            // front and then flows through every JSON-input path.
            let is_s2c_path = |p: &PathBuf| p.extension().and_then(|e| e.to_str()) == Some("s2c");
            let sources: Vec<(PathBuf, String)> = if inputs.len() == 1 && is_s2c_path(&inputs[0]) {
                let bytes = match std::fs::read(&inputs[0]) {
                    Ok(b) => b,
                    Err(e) => {
                        eprintln!("error: cannot read {}: {e}", inputs[0].display());
                        return ExitCode::FAILURE;
                    }
                };
                // Id-elided payloads recompute their ids; the library
                // (when given) names the effective-name targets. Delta
                // payloads apply to --delta-base first.
                let decoded = match sysmlv2_cbor::from_cbor(&bytes) {
                    Err(e) if e.to_string().contains("delta payload") => {
                        let Some(base_path) = &delta_base else {
                            eprintln!(
                                "error: input is a delta payload; pass \
                                 --delta-base <base.json|base.s2c> to apply it"
                            );
                            return ExitCode::FAILURE;
                        };
                        let base = match load_base_value(base_path) {
                            Ok(v) => v,
                            Err(code) => return code,
                        };
                        // Id-elided deltas re-derive their created ids
                        // through the library resolver (empty is fine
                        // for hermetic models; explicit-id deltas
                        // never consult it).
                        let names = match load_library_id_names(lib.as_deref()) {
                            Ok(n) => n,
                            Err(code) => return code,
                        };
                        sysmlv2_cbor::apply_delta_cbor_with(&bytes, &base, &|s| {
                            names.get(s).cloned()
                        })
                    }
                    Err(e) if e.to_string().contains("elided") => {
                        let names = match load_library_id_names(lib.as_deref()) {
                            Ok(n) => n,
                            Err(code) => return code,
                        };
                        sysmlv2_cbor::from_cbor_with(&bytes, &|s| names.get(s).cloned())
                    }
                    other => other,
                };
                match decoded {
                    Ok(v) => vec![(inputs[0].clone(), serde_json::to_string(&v).unwrap())],
                    Err(e) => {
                        eprintln!("error: invalid CBOR payload: {e}");
                        return ExitCode::FAILURE;
                    }
                }
            } else if inputs.iter().any(is_s2c_path) {
                eprintln!("error: convert accepts one .s2c input on its own");
                return ExitCode::FAILURE;
            } else {
                match read_inputs(&inputs) {
                    Ok(s) => s,
                    Err(code) => return code,
                }
            };
            let looks_json = |p: &Path, s: &str| {
                matches!(p.extension().and_then(|e| e.to_str()), Some("json" | "s2c"))
                    || s.trim_start().starts_with('[')
            };
            let is_json_input = looks_json(&sources[0].0, &sources[0].1);
            if sources.len() > 1 && sources.iter().any(|(p, s)| looks_json(p, s)) {
                eprintln!("error: convert accepts several textual inputs or one JSON input");
                return ExitCode::FAILURE;
            }
            if min_qual && (!matches!(to, Target::Text) || !is_json_input) {
                eprintln!("error: --min-qual applies to JSON \u{2192} text conversion");
                return ExitCode::FAILURE;
            }
            match to {
                Target::Text => {
                    if !is_json_input {
                        eprintln!(
                            "error: the input is already textual notation; use \
                             `sysmlv2 fmt` to reformat it"
                        );
                        return ExitCode::FAILURE;
                    }
                    let src = &sources[0].1;
                    let mut value: serde_json::Value = match serde_json::from_str(src) {
                        Ok(v) => v,
                        Err(e) => {
                            eprintln!("error: invalid JSON: {e}");
                            return ExitCode::FAILURE;
                        }
                    };
                    if flexo {
                        value = flexo_unwrap(value);
                    }
                    // Minimal-qualification printing: lift through a
                    // transform session (same split/lift/naming path) and
                    // run the reparse-verified respelling pass over the
                    // whole document set, then write its units.
                    if min_qual {
                        let mut session =
                            match sysmlv2_transform::Session::from_interchange_json_with_library(
                                &value,
                                lib.as_deref(),
                            ) {
                                Ok(s) => s,
                                Err(e) => {
                                    eprintln!("error: cannot lift JSON: {e}");
                                    return ExitCode::FAILURE;
                                }
                            };
                        for w in session.warnings() {
                            eprintln!("warning: {w}");
                        }
                        if let Err(e) = session.minimize_qualifications() {
                            eprintln!("error: minimal-qualification pass failed: {e}");
                            return ExitCode::FAILURE;
                        }
                        let units: Vec<(String, String)> = session
                            .units()
                            .map(|(_, n, s)| (n.to_string(), s.to_string()))
                            .collect();
                        if let Some(dir) = output.as_ref().filter(|o| o.is_dir()) {
                            for (name, text) in &units {
                                let file = dir.join(name);
                                if let Err(e) = std::fs::write(&file, text) {
                                    eprintln!("error: cannot write {}: {e}", file.display());
                                    return ExitCode::FAILURE;
                                }
                                println!("{}", file.display());
                            }
                            return ExitCode::SUCCESS;
                        }
                        let text: String = units
                            .into_iter()
                            .map(|(_, t)| t)
                            .collect::<Vec<_>>()
                            .join("");
                        match output {
                            Some(out) => {
                                if let Err(e) = std::fs::write(&out, &text) {
                                    eprintln!("error: cannot write {}: {e}", out.display());
                                    return ExitCode::FAILURE;
                                }
                            }
                            None => print!("{text}"),
                        }
                        return ExitCode::SUCCESS;
                    }
                    let names = match lib {
                        Some(dir) => {
                            let mut model = Model::new();
                            let lib_cache_path = match load_library(&mut model, &dir) {
                                Ok(p) => p,
                                Err(e) => {
                                    eprintln!("error: cannot load library {}: {e}", dir.display());
                                    return ExitCode::FAILURE;
                                }
                            };
                            let names = library_name_map(&model);
                            save_library_cache(&model, lib_cache_path);
                            names
                        }
                        None => Default::default(),
                    };
                    // A multi-document element list splits into one text
                    // file per root namespace when the output is a
                    // directory (the Flexo retrieval flow). A directory
                    // always receives files — one per document, or a
                    // single document-1.sysml when no split applies.
                    let split = sysmlv2_parser::lift::split_documents(&value);
                    if let Some(dir) = output.as_ref().filter(|o| o.is_dir()) {
                        let docs = split.clone().unwrap_or_else(|| vec![(None, value.clone())]);
                        // Cross-document references print as $::-rooted
                        // qualified names via a whole-list name map.
                        let mut names = names.clone();
                        names.extend(sysmlv2_parser::lift::document_reference_name_map(&value));
                        for (i, (name, doc)) in docs.iter().enumerate() {
                            let lifted = match from_compact_json_with_names(doc, &names) {
                                Ok(l) => l,
                                Err(e) => {
                                    eprintln!("error: cannot lift document {i}: {e}");
                                    return ExitCode::FAILURE;
                                }
                            };
                            for w in &lifted.errors {
                                eprintln!("warning: {w}");
                            }
                            let file = dir.join(doc_file_name(name.as_deref(), i));
                            if let Err(e) = std::fs::write(
                                &file,
                                print_source_opts(
                                    &lifted.unit,
                                    PrintOptions {
                                        indent,
                                        reflow_doc_bodies: true,
                                        ..Default::default()
                                    },
                                ),
                            ) {
                                eprintln!("error: cannot write {}: {e}", file.display());
                                return ExitCode::FAILURE;
                            }
                            println!("{}", file.display());
                        }
                        return ExitCode::SUCCESS;
                    }
                    if split.is_some() {
                        eprintln!(
                            "note: input holds several documents — they are \
                             concatenated; pass `-o <existing dir>` to split \
                             into one file per root namespace"
                        );
                    }
                    let lifted = match from_compact_json_with_names(&value, &names) {
                        Ok(l) => l,
                        Err(e) => {
                            eprintln!("error: cannot lift JSON: {e}");
                            return ExitCode::FAILURE;
                        }
                    };
                    for w in &lifted.errors {
                        eprintln!("warning: {w}");
                    }
                    let text = print_source_opts(
                        &lifted.unit,
                        PrintOptions {
                            indent,
                            reflow_doc_bodies: true,
                            ..Default::default()
                        },
                    );
                    match output {
                        Some(out) => {
                            if let Err(e) = std::fs::write(&out, &text) {
                                eprintln!("error: cannot write {}: {e}", out.display());
                                return ExitCode::FAILURE;
                            }
                        }
                        None => print!("{text}"),
                    }
                    ExitCode::SUCCESS
                }
                Target::FullJson | Target::FullCbor | Target::CompactJson | Target::CompactCbor
                    if !is_json_input =>
                {
                    let full = matches!(to, Target::FullJson | Target::FullCbor);
                    // --elide-ids: library element names for the
                    // effective-name chains (roots-only exception maps);
                    // filled when a library is loaded below.
                    let mut elide_names: std::collections::HashMap<String, String> =
                        Default::default();
                    // One no-lib file keeps the single-unit fast path;
                    // anything else builds a model (one root namespace per
                    // file, cross-file references resolved). Binary targets
                    // also carry the unit structure: each unit root's
                    // element index paired with its source path.
                    let (json, unit_paths) = if lib.is_some() || sources.len() > 1 {
                        let mut model = Model::new();
                        let lib_cache_path = if let Some(lib) = &lib {
                            match load_library(&mut model, lib) {
                                Ok(p) => p,
                                Err(e) => {
                                    eprintln!("error: cannot load library {}: {e}", lib.display());
                                    return ExitCode::FAILURE;
                                }
                            }
                        } else {
                            None
                        };
                        for (path, src) in &sources {
                            let name = path.to_string_lossy().into_owned();
                            let unit = model.add_source(name, src);
                            if !unit.diagnostics.is_empty() {
                                let diags = unit.diagnostics.clone();
                                report(path, src, &diags);
                                return ExitCode::FAILURE;
                            }
                        }
                        if full && lib.is_none() {
                            eprintln!(
                                "note: no --lib given — implied relationships are omitted \
                                 (isImpliedIncluded: false); derived properties are included"
                            );
                        }
                        let (compact, units) = model_to_compact_json_with_units(&model);
                        let json = if full {
                            // --flexo commits must survive read-back even
                            // with unresolved references: emit recovery
                            // annotations alongside the dangling ids.
                            // Full interchange is lossless by default:
                            // unresolved textual references need recovery
                            // carriers independently of the Flexo envelope.
                            model_to_full_json_with(&model, true)
                        } else {
                            compact.clone()
                        };
                        let unit_paths = remap_units(&compact, &units, &json);
                        if elide_ids && lib.is_some() {
                            elide_names = library_name_map(&model)
                                .into_iter()
                                .filter_map(|(id, segs)| {
                                    segs.last().cloned().map(|n| (id.to_string(), n))
                                })
                                .collect();
                        }
                        save_library_cache(&model, lib_cache_path);
                        (json, unit_paths)
                    } else {
                        let (input, src) = &sources[0];
                        let parse = parse_file(input, src);
                        if !parse.diagnostics.is_empty() {
                            report(input, src, &parse.diagnostics);
                            return ExitCode::FAILURE;
                        }
                        // The builder emits each unit's root namespace
                        // first: the single unit's root is element 0 of
                        // the compact array.
                        let compact = to_compact_json(&parse.unit);
                        let units = vec![(0usize, input.to_string_lossy().into_owned())];
                        if full {
                            eprintln!(
                                "note: no --lib given — implied relationships are omitted \
                                 (isImpliedIncluded: false); derived properties are included"
                            );
                            let json = to_full_json_with(&parse.unit, true);
                            let unit_paths = remap_units(&compact, &units, &json);
                            (json, unit_paths)
                        } else {
                            (compact, units)
                        }
                    };
                    let json = if flexo {
                        let names: Vec<String> = sources
                            .iter()
                            .map(|(p, _)| {
                                p.file_name()
                                    .map(|n| n.to_string_lossy().into_owned())
                                    .unwrap_or_else(|| "model.sysml".to_string())
                            })
                            .collect();
                        flexo_payload(json, &names)
                    } else {
                        json
                    };
                    if matches!(to, Target::CompactCbor | Target::FullCbor) {
                        let encoded = if matches!(to, Target::FullCbor) {
                            sysmlv2_cbor::to_full_cbor_with_units(&json, &unit_paths)
                        } else if let Some(base_path) = delta_base
                            .as_ref()
                            .filter(|_| matches!(to, Target::CompactCbor))
                        {
                            let base = match load_base_value(base_path) {
                                Ok(v) => v,
                                Err(code) => return code,
                            };
                            // This parse derived ids afresh; the base carries
                            // whatever its producer assigned. Rebase so
                            // unchanged elements coincide by identity.
                            let json = match sysmlv2_cbor::rebase_ids(&base, &json) {
                                Ok(v) => v,
                                Err(e) => {
                                    eprintln!("error: cannot rebase onto the delta base: {e}");
                                    return ExitCode::FAILURE;
                                }
                            };
                            // Unit paths ride strict deltas;
                            // rebase preserves element order, so the
                            // snapshot-side indices stay valid.
                            let units = if delta_portable {
                                Vec::new()
                            } else {
                                unit_paths.clone()
                            };
                            if elide_ids {
                                sysmlv2_cbor::delta_compact_cbor_elided(
                                    &base,
                                    &json,
                                    &sysmlv2_cbor::DeltaOptions {
                                        units,
                                        ..Default::default()
                                    },
                                    &|s| elide_names.get(s).cloned(),
                                )
                            } else {
                                sysmlv2_cbor::delta_compact_cbor(
                                    &base,
                                    &json,
                                    &sysmlv2_cbor::DeltaOptions {
                                        portable: delta_portable,
                                        units,
                                        ..Default::default()
                                    },
                                )
                            }
                        } else if elide_ids {
                            sysmlv2_cbor::to_compact_cbor_elided_with_units(
                                &json,
                                &|s| elide_names.get(s).cloned(),
                                &unit_paths,
                            )
                        } else {
                            sysmlv2_cbor::to_compact_cbor_with_units(&json, &unit_paths)
                        };
                        return match encoded {
                            Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                            Err(e) => {
                                eprintln!("error: cannot encode CBOR: {e}");
                                ExitCode::FAILURE
                            }
                        };
                    }
                    let text = serde_json::to_string_pretty(&json).unwrap();
                    match output {
                        Some(out) => {
                            if let Err(e) = std::fs::write(&out, text + "\n") {
                                eprintln!("error: cannot write {}: {e}", out.display());
                                return ExitCode::FAILURE;
                            }
                        }
                        None => println!("{text}"),
                    }
                    ExitCode::SUCCESS
                }
                Target::Kpar => {
                    if is_json_input {
                        eprintln!(
                            "error: a .kpar packs textual units; convert the JSON \
                             to text first"
                        );
                        return ExitCode::FAILURE;
                    }
                    let Some(out) = output else {
                        eprintln!("error: --to kpar needs -o <archive.kpar>");
                        return ExitCode::FAILURE;
                    };
                    let mut units: Vec<(String, String, String)> = Vec::new();
                    for (path, src) in &sources {
                        let parse = parse_file(path, src);
                        if !parse.diagnostics.is_empty() {
                            report(path, src, &parse.diagnostics);
                            return ExitCode::FAILURE;
                        }
                        // The .meta.json index maps the unit's root
                        // namespace name to its file; an anonymous root
                        // falls back to the file stem.
                        let root = parse
                            .unit
                            .members
                            .iter()
                            .find_map(|m| match &m.kind {
                                sysmlv2_parser::ast::MemberKind::Package(pkg) => {
                                    pkg.id.name.as_ref().map(|n| n.value.clone())
                                }
                                _ => None,
                            })
                            .unwrap_or_else(|| {
                                path.file_stem().map_or_else(
                                    || "model".to_string(),
                                    |st| st.to_string_lossy().into_owned(),
                                )
                            });
                        let file_name = path.file_name().map_or_else(
                            || "model.sysml".to_string(),
                            |f| f.to_string_lossy().into_owned(),
                        );
                        units.push((file_name, src.clone(), root));
                    }
                    let name = out.file_stem().map_or_else(
                        || "project".to_string(),
                        |st| st.to_string_lossy().into_owned(),
                    );
                    let bytes = kpar::write(&name, "1.0.0", &units);
                    if let Err(e) = std::fs::write(&out, bytes) {
                        eprintln!("error: cannot write {}: {e}", out.display());
                        return ExitCode::FAILURE;
                    }
                    ExitCode::SUCCESS
                }
                Target::FullJson | Target::FullCbor => {
                    // Compact JSON → full JSON re-derivation, **in place**:
                    // every element keeps its @id (derived properties and
                    // implied relationships are functions of the compact
                    // structure), so a stored payload upgrades without
                    // breaking external references to its elements.
                    let src = &sources[0].1;
                    let mut value: serde_json::Value = match serde_json::from_str(src) {
                        Ok(v) => v,
                        Err(e) => {
                            eprintln!("error: invalid JSON: {e}");
                            return ExitCode::FAILURE;
                        }
                    };
                    if flexo {
                        value = flexo_unwrap(value);
                    }
                    let by_name = if let Some(dir) = &lib {
                        let mut model = Model::new();
                        let lib_cache_path = match load_library(&mut model, dir) {
                            Ok(p) => p,
                            Err(e) => {
                                eprintln!("error: cannot load library {}: {e}", dir.display());
                                return ExitCode::FAILURE;
                            }
                        };
                        save_library_cache(&model, lib_cache_path);
                        library_name_map(&model)
                            .into_iter()
                            .map(|(id, segments)| (segments.join("::"), id))
                            .collect()
                    } else {
                        eprintln!(
                            "note: no --lib given — implied relationships are omitted \
                             (isImpliedIncluded: false); derived properties are included"
                        );
                        Default::default()
                    };
                    let json = sysmlv2_parser::full::from_compact_value(value, &by_name, true);
                    if matches!(to, Target::FullCbor) {
                        return match sysmlv2_cbor::to_full_cbor(&json) {
                            Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                            Err(e) => {
                                eprintln!("error: cannot encode CBOR: {e}");
                                ExitCode::FAILURE
                            }
                        };
                    }
                    let json = if flexo {
                        flexo_payload(json, &[])
                    } else {
                        json
                    };
                    let text = serde_json::to_string_pretty(&json).unwrap();
                    match output {
                        Some(out) => {
                            if let Err(e) = std::fs::write(&out, text + "\n") {
                                eprintln!("error: cannot write {}: {e}", out.display());
                                return ExitCode::FAILURE;
                            }
                        }
                        None => println!("{text}"),
                    }
                    ExitCode::SUCCESS
                }
                Target::CompactJson | Target::CompactCbor => {
                    // JSON → compact JSON/CBOR: normalize (drop implied
                    // relationships / derived properties) by lifting and
                    // re-emitting.
                    let src = &sources[0].1;
                    let value: serde_json::Value = match serde_json::from_str(src) {
                        Ok(v) => v,
                        Err(e) => {
                            eprintln!("error: invalid JSON: {e}");
                            return ExitCode::FAILURE;
                        }
                    };
                    let lifted = match from_compact_json_with_names(&value, &Default::default()) {
                        Ok(l) => l,
                        Err(e) => {
                            eprintln!("error: cannot lift JSON: {e}");
                            return ExitCode::FAILURE;
                        }
                    };
                    for w in &lifted.errors {
                        eprintln!("warning: {w}");
                    }
                    let json = to_compact_json(&lifted.unit);
                    if matches!(to, Target::CompactCbor) {
                        // Hermetic normalize path: elision without a
                        // resolver is always safe — library-effective
                        // names simply ride the exception map.
                        let encoded = if let Some(base_path) = &delta_base {
                            let base = match load_base_value(base_path) {
                                Ok(v) => v,
                                Err(code) => return code,
                            };
                            // The lift + re-emit derived ids afresh; rebase
                            // so unchanged elements coincide by identity.
                            let json = match sysmlv2_cbor::rebase_ids(&base, &json) {
                                Ok(v) => v,
                                Err(e) => {
                                    eprintln!("error: cannot rebase onto the delta base: {e}");
                                    return ExitCode::FAILURE;
                                }
                            };
                            if elide_ids {
                                sysmlv2_cbor::delta_compact_cbor_elided(
                                    &base,
                                    &json,
                                    &Default::default(),
                                    &|_| None,
                                )
                            } else {
                                sysmlv2_cbor::delta_compact_cbor(
                                    &base,
                                    &json,
                                    &sysmlv2_cbor::DeltaOptions {
                                        portable: delta_portable,
                                        ..Default::default()
                                    },
                                )
                            }
                        } else if elide_ids {
                            sysmlv2_cbor::to_compact_cbor_elided(&json, &|_| None)
                        } else {
                            sysmlv2_cbor::to_compact_cbor(&json)
                        };
                        return match encoded {
                            Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                            Err(e) => {
                                eprintln!("error: cannot encode CBOR: {e}");
                                ExitCode::FAILURE
                            }
                        };
                    }
                    let json = if flexo {
                        flexo_payload(json, &[])
                    } else {
                        json
                    };
                    let text = serde_json::to_string_pretty(&json).unwrap();
                    match output {
                        Some(out) => {
                            if let Err(e) = std::fs::write(&out, text + "\n") {
                                eprintln!("error: cannot write {}: {e}", out.display());
                                return ExitCode::FAILURE;
                            }
                        }
                        None => println!("{text}"),
                    }
                    ExitCode::SUCCESS
                }
            }
        }

        Command::Payload {
            inputs,
            find_base,
            lib,
            delta_from,
            portable,
            claim_project,
            claim_commit,
            claim_service,
            apply_to,
            lenient,
            ids,
            tables,
            encode,
            output,
        } => {
            if tables {
                if !inputs.is_empty() {
                    eprintln!("error: --tables takes no payload inputs");
                    return ExitCode::FAILURE;
                }
                let text = serde_json::to_string_pretty(&codec_tables_doc()).unwrap();
                return match output {
                    Some(out) => {
                        if let Err(e) = std::fs::write(&out, text + "\n") {
                            eprintln!("error: cannot write {}: {e}", out.display());
                            return ExitCode::FAILURE;
                        }
                        ExitCode::SUCCESS
                    }
                    None => {
                        println!("{text}");
                        ExitCode::SUCCESS
                    }
                };
            }
            if inputs.is_empty() {
                eprintln!("error: no input payloads");
                return ExitCode::FAILURE;
            }
            let names = match load_library_id_names(lib.as_deref()) {
                Ok(n) => n,
                Err(code) => return code,
            };
            if let Some(base_path) = &delta_from {
                let [target_path] = inputs.as_slice() else {
                    eprintln!("error: --delta-from takes exactly one target snapshot");
                    return ExitCode::FAILURE;
                };
                let base = match load_snapshot_value(base_path, &names) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
                let target = match load_snapshot_value(target_path, &names) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
                let mut claims: Vec<(u64, sysmlv2_cbor::Claim)> = Vec::new();
                for (key, id) in [(0, &claim_project), (1, &claim_commit)] {
                    if let Some(s) = id {
                        match uuid::Uuid::try_parse(s) {
                            Ok(u) => claims.push((key, sysmlv2_cbor::Claim::Id(u))),
                            Err(_) => {
                                eprintln!("error: claim `{s}` is not a UUID");
                                return ExitCode::FAILURE;
                            }
                        }
                    }
                }
                if let Some(s) = &claim_service {
                    claims.push((2, sysmlv2_cbor::Claim::Text(s.clone())));
                }
                let opts = sysmlv2_cbor::DeltaOptions {
                    portable,
                    claims,
                    units: Vec::new(),
                };
                return match sysmlv2_cbor::delta_compact_cbor(&base, &target, &opts) {
                    Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                    Err(e) => {
                        eprintln!("error: cannot encode the delta: {e}");
                        ExitCode::FAILURE
                    }
                };
            }
            if let Some(base_path) = &apply_to {
                let [delta_path] = inputs.as_slice() else {
                    eprintln!("error: --apply-to takes exactly one delta payload");
                    return ExitCode::FAILURE;
                };
                let Some(out_path) = &output else {
                    eprintln!("error: --apply-to writes the applied snapshot to --output");
                    return ExitCode::FAILURE;
                };
                let bytes = match std::fs::read(delta_path) {
                    Ok(b) => b,
                    Err(e) => {
                        eprintln!("error: cannot read {}: {e}", delta_path.display());
                        return ExitCode::FAILURE;
                    }
                };
                let base = match load_snapshot_value(base_path, &names) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
                let applied = if lenient {
                    sysmlv2_cbor::apply_delta_cbor_lenient(&bytes, &base)
                } else {
                    sysmlv2_cbor::apply_delta_cbor_report_with(&bytes, &base, &|s| {
                        names.get(s).cloned()
                    })
                };
                let (result, report) = match applied {
                    Ok(r) => r,
                    Err(e) => {
                        eprintln!("error: cannot apply {}: {e}", delta_path.display());
                        return ExitCode::FAILURE;
                    }
                };
                let result_digest = match sysmlv2_cbor::state_digest(&result) {
                    Ok(d) => d.to_string(),
                    Err(e) => {
                        eprintln!("error: cannot digest the applied result: {e}");
                        return ExitCode::FAILURE;
                    }
                };
                let text = serde_json::to_string_pretty(&result).unwrap();
                if let Err(e) = std::fs::write(out_path, text + "\n") {
                    eprintln!("error: cannot write {}: {e}", out_path.display());
                    return ExitCode::FAILURE;
                }
                let doc = serde_json::json!({
                    "file": delta_path.display().to_string(),
                    "baseMatched": report.base_matched,
                    "noopDeletes": report.noop_deletes,
                    "upsertedUpdates": report.upserted_updates,
                    "replacedCreates": report.replaced_creates,
                    "units": report
                        .units
                        .iter()
                        .map(|(index, path)| serde_json::json!({ "index": index, "path": path }))
                        .collect::<Vec<_>>(),
                    "resultElements": result.as_array().map(Vec::len),
                    "resultDigest": result_digest,
                    "output": out_path.display().to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&doc).unwrap());
                return ExitCode::SUCCESS;
            }
            if encode {
                let [input] = inputs.as_slice() else {
                    eprintln!("error: --encode takes exactly one compact-JSON snapshot");
                    return ExitCode::FAILURE;
                };
                let value = match load_snapshot_value(input, &names) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
                return match sysmlv2_cbor::to_compact_cbor(&value) {
                    Ok(bytes) => write_bytes(output.as_deref(), &bytes),
                    Err(e) => {
                        eprintln!("error: cannot encode {}: {e}", input.display());
                        ExitCode::FAILURE
                    }
                };
            }
            if ids {
                let mut summaries = Vec::new();
                for path in &inputs {
                    let value = match load_snapshot_value(path, &names) {
                        Ok(v) => v,
                        Err(code) => return code,
                    };
                    let canon = match sysmlv2_cbor::delta_canonical(&value) {
                        Ok(c) => c,
                        Err(e) => {
                            eprintln!("error: {}: cannot canonicalize: {e}", path.display());
                            return ExitCode::FAILURE;
                        }
                    };
                    let digest = match sysmlv2_cbor::state_digest(&value) {
                        Ok(d) => d.to_string(),
                        Err(e) => {
                            eprintln!("error: {}: cannot digest: {e}", path.display());
                            return ExitCode::FAILURE;
                        }
                    };
                    let id_seq: Vec<&str> = canon
                        .as_array()
                        .unwrap()
                        .iter()
                        .filter_map(|e| e.get("@id").and_then(serde_json::Value::as_str))
                        .collect();
                    summaries.push(serde_json::json!({
                        "file": path.display().to_string(),
                        "elements": id_seq.len(),
                        "stateDigest": digest,
                        "ids": id_seq,
                    }));
                }
                let doc = if summaries.len() == 1 {
                    summaries.pop().unwrap()
                } else {
                    serde_json::Value::Array(summaries)
                };
                println!("{}", serde_json::to_string_pretty(&doc).unwrap());
                return ExitCode::SUCCESS;
            }
            // One scan shared by every delta input: digest each
            // snapshot-looking file under the directory once.
            let candidates: Option<Vec<(PathBuf, String)>> = find_base.as_ref().map(|dir| {
                payload_files_under(dir)
                    .into_iter()
                    .filter_map(|p| snapshot_file_digest(&p, &names).map(|d| (p, d)))
                    .collect()
            });
            let mut summaries = Vec::new();
            let mut saw_delta = false;
            let mut unmatched = false;
            for path in &inputs {
                let bytes = match std::fs::read(path) {
                    Ok(b) => b,
                    Err(e) => {
                        eprintln!("error: cannot read {}: {e}", path.display());
                        return ExitCode::FAILURE;
                    }
                };
                let mut summary = match sysmlv2_cbor::describe(&bytes) {
                    Ok(s) => {
                        let described = s.as_object().unwrap().clone();
                        let mut o = serde_json::Map::new();
                        o.insert("file".into(), serde_json::json!(path.display().to_string()));
                        o.insert("encoding".into(), serde_json::json!("cbor"));
                        o.extend(described);
                        serde_json::Value::Object(o)
                    }
                    // Not s2c — a compact interchange JSON snapshot
                    // still has a state digest worth printing.
                    Err(cbor_err) => match serde_json::from_slice::<serde_json::Value>(&bytes) {
                        Ok(v) if v.is_array() => {
                            let digest = match sysmlv2_cbor::state_digest(&v) {
                                Ok(d) => d.to_string(),
                                Err(e) => {
                                    eprintln!("error: {}: cannot digest: {e}", path.display());
                                    return ExitCode::FAILURE;
                                }
                            };
                            serde_json::json!({
                                "file": path.display().to_string(),
                                "encoding": "json",
                                "form": "compact",
                                "bytes": bytes.len(),
                                "elements": v.as_array().unwrap().len(),
                                "stateDigest": digest,
                            })
                        }
                        _ => {
                            eprintln!(
                                "error: {}: not an interchange payload (s2c or \
                                 compact JSON element array): {cbor_err}",
                                path.display()
                            );
                            return ExitCode::FAILURE;
                        }
                    },
                };
                if summary["form"] == "delta" {
                    saw_delta = true;
                    if let Some(cands) = &candidates {
                        let matches = |key: &str| -> Vec<serde_json::Value> {
                            cands
                                .iter()
                                .filter(|(_, d)| Some(d.as_str()) == summary["delta"][key].as_str())
                                .map(|(p, _)| serde_json::json!(p.display().to_string()))
                                .collect()
                        };
                        let base_matches = matches("baseDigest");
                        let result_matches = matches("resultDigest");
                        if base_matches.is_empty() {
                            eprintln!(
                                "note: {}: no snapshot under {} matches the delta's \
                                 base digest",
                                path.display(),
                                find_base.as_ref().unwrap().display()
                            );
                            unmatched = true;
                        }
                        let d = summary["delta"].as_object_mut().unwrap();
                        d.insert("baseMatches".into(), serde_json::json!(base_matches));
                        d.insert("resultMatches".into(), serde_json::json!(result_matches));
                    }
                } else if summary["encoding"] == "cbor"
                    && summary["form"] == "compact"
                    && summary["versions"]["supported"] == true
                {
                    // Compact snapshot s2c: the state digest requires a
                    // decode (elided payloads re-derive their ids
                    // first). Full-form payloads have no state digest —
                    // the digest space is compact-form canonical.
                    match decode_snapshot(&bytes, &names) {
                        Ok(v) => match sysmlv2_cbor::state_digest(&v) {
                            Ok(d) => {
                                summary
                                    .as_object_mut()
                                    .unwrap()
                                    .insert("stateDigest".into(), serde_json::json!(d.to_string()));
                            }
                            Err(e) => {
                                eprintln!("error: {}: cannot digest: {e}", path.display());
                                return ExitCode::FAILURE;
                            }
                        },
                        Err(e) => {
                            summary.as_object_mut().unwrap().insert(
                                "stateDigestError".into(),
                                serde_json::json!(e.to_string()),
                            );
                        }
                    }
                }
                summaries.push(summary);
            }
            if candidates.is_some() && !saw_delta {
                eprintln!("error: --find-base needs a delta payload input");
                return ExitCode::FAILURE;
            }
            let doc = if summaries.len() == 1 {
                summaries.pop().unwrap()
            } else {
                serde_json::Value::Array(summaries)
            };
            println!("{}", serde_json::to_string_pretty(&doc).unwrap());
            if unmatched {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }

        Command::Fmt {
            files,
            check,
            stdout,
            indent,
        } => {
            // Ambient inputs never drive an in-place rewrite: a whole
            // workspace reformatted because an env var happened to be
            // set is a footgun. --check is the read-only mode.
            let files = if files.is_empty() && !check {
                eprintln!(
                    "error: no input files — fmt rewrites in place, so ambient \
                     {MODEL_DIR_VAR} inputs apply to --check only; pass explicit paths"
                );
                return ExitCode::FAILURE;
            } else {
                match resolve_inputs(files, quiet) {
                    Ok(files) => files,
                    Err(code) => return code,
                }
            };
            let mut failed = false;
            for path in &files {
                if path == Path::new("-") && !stdout && !check {
                    eprintln!("error: cannot format stdin (`-`) in place; use --stdout or --check");
                    failed = true;
                    continue;
                }
                let src = match read(path) {
                    Ok(s) => s,
                    Err(_) => {
                        failed = true;
                        continue;
                    }
                };
                match format_source_with(&src, dialect_of(path), indent) {
                    Err(diags) => {
                        report(path, &src, &diags);
                        failed = true;
                    }
                    Ok(formatted) => {
                        if stdout {
                            print!("{formatted}");
                        } else if check {
                            if formatted != src {
                                eprintln!("would reformat: {}", path.display());
                                failed = true;
                            }
                        } else if formatted != src {
                            if let Err(e) = std::fs::write(path, &formatted) {
                                eprintln!("error: cannot write {}: {e}", path.display());
                                failed = true;
                            }
                        }
                    }
                }
            }
            if failed {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }

        Command::Check { files, lib, strict } => {
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let mut errors = 0usize;
            let mut warnings = 0usize;
            // `.kpar` archives expand to their contained textual units.
            let inputs = match read_inputs(&files) {
                Ok(i) => i,
                Err(code) => return code,
            };
            // (path, source) per cleanly-parsed file, for the model stage.
            let mut sources: Vec<(&PathBuf, String)> = Vec::new();
            for (path, src) in &inputs {
                let src = src.clone();
                let parse = parse_file(path, &src);
                if !parse.diagnostics.is_empty() {
                    report(path, &src, &parse.diagnostics);
                    errors += parse.diagnostics.len();
                    continue; // context checks on a broken parse would mislead
                }
                let context_diags = sysmlv2_parser::check::validate(&parse.unit);
                if !context_diags.is_empty() {
                    report(path, &src, &context_diags);
                    errors += context_diags.len();
                }
                sources.push((path, src));
            }

            // Referential and semantic checks always run over all cleanly
            // parsed files as one model. A standard library enriches
            // resolution, but basic local constraints must not disappear
            // merely because `--lib` was omitted.
            if !sources.is_empty() {
                let mut model = Model::new();
                let lib_cache_path = if let Some(lib) = &lib {
                    match load_library(&mut model, lib) {
                        Ok(p) => p,
                        Err(e) => {
                            eprintln!("error: cannot load library {}: {e}", lib.display());
                            return ExitCode::FAILURE;
                        }
                    }
                } else {
                    None
                };
                // Unit indices: libraries first, then our files in order.
                let boundary = model.units().len();
                for (path, src) in &sources {
                    model.add_source(path.display().to_string(), src);
                }
                let mut r = sysmlv2_parser::json::ResolvedModel::build(&model);
                save_library_cache(&model, lib_cache_path);
                for (unit, d) in sysmlv2_parser::check::validate_model_with(&mut r, &model)
                    .into_iter()
                    .chain(sysmlv2_parser::check::validate_semantics_with(
                        &mut r, &model,
                    ))
                {
                    let (path, src) = &sources[unit - boundary];
                    match d.severity {
                        sysmlv2_parser::diag::Severity::Error => errors += 1,
                        sysmlv2_parser::diag::Severity::Warning => warnings += 1,
                    }
                    report(path, src, &[d]);
                }
                if lib.is_some() {
                    // Unused private imports: provenance +
                    // owner-chain + textual conditions, corpus-triaged.
                    let texts: Vec<(usize, String)> = sources
                        .iter()
                        .enumerate()
                        .map(|(i, (_, src))| (boundary + i, src.clone()))
                        .collect();
                    for (unit, span) in
                        sysmlv2_transform::unused_private_imports_with(&mut r, &texts)
                    {
                        let (path, src) = &sources[unit - boundary];
                        warnings += 1;
                        report(
                            path,
                            src,
                            &[sysmlv2_parser::Diagnostic::warning(
                                span,
                                "unused private import",
                            )],
                        );
                    }
                }
            }

            if warnings > 0 {
                eprintln!("{warnings} warning(s)");
            }
            if errors > 0 {
                eprintln!("{errors} error(s)");
                ExitCode::FAILURE
            } else if strict && warnings > 0 {
                eprintln!("--strict: warnings are failures");
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }

        Command::Lint {
            files,
            lib,
            config,
            rule,
            fix,
            fix_deletes,
            strict,
        } => {
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let inputs = match read_inputs(&files) {
                Ok(i) => i,
                Err(code) => return code,
            };
            // Config: --config, else sysmlint.json beside the first input.
            let config_path = config.or_else(|| {
                let candidate = files
                    .first()
                    .and_then(|f| f.parent())
                    .map(|d| d.join("sysmlint.json"))?;
                candidate.exists().then_some(candidate)
            });
            let mut cfg = match &config_path {
                Some(p) => match std::fs::read_to_string(p)
                    .map_err(|e| e.to_string())
                    .and_then(|t| sysmlv2_lint::Config::from_json(&t))
                {
                    Ok(c) => c,
                    Err(e) => {
                        eprintln!("error: cannot read lint config {}: {e}", p.display());
                        return ExitCode::FAILURE;
                    }
                },
                None => sysmlv2_lint::Config::default(),
            };
            for r in &rule {
                let Some((id, level)) = r.split_once('=') else {
                    eprintln!("error: --rule wants ID=LEVEL, got `{r}`");
                    return ExitCode::FAILURE;
                };
                let level = match level {
                    "off" => sysmlv2_lint::Severity::Off,
                    "hint" => sysmlv2_lint::Severity::Hint,
                    "info" => sysmlv2_lint::Severity::Info,
                    "warn" => sysmlv2_lint::Severity::Warn,
                    "error" => sysmlv2_lint::Severity::Error,
                    other => {
                        eprintln!(
                            "error: --rule level must be off|hint|info|warn|error, got `{other}`"
                        );
                        return ExitCode::FAILURE;
                    }
                };
                cfg.set(id, level);
            }

            // The model stage wants cleanly-parsed sources only.
            let mut errors = 0usize;
            let mut warnings = 0usize;
            let mut sources: Vec<(&PathBuf, String)> = Vec::new();
            for (path, src) in &inputs {
                let parse = parse_file(path, src);
                if !parse.diagnostics.is_empty() {
                    report(path, src, &parse.diagnostics);
                    errors += parse.diagnostics.len();
                    continue;
                }
                sources.push((path, src.clone()));
            }
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(lib) = &lib {
                lib_cache_path = match load_library(&mut model, lib) {
                    Ok(p) => Some(p),
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", lib.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            // Without `--lib`, the ambient libraries still load so
            // ordinary content + sidecar invocations resolve their
            // provenance record types (with `--lib` they came along).
            if lib.is_none() {
                sysmlv2_parser::ambient::add_to(&mut model);
            }
            let boundary = model.units().len();
            for (path, src) in &sources {
                model.add_source(path.display().to_string(), src);
            }
            let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
            if let Some(p) = lib_cache_path {
                save_library_cache(&model, p);
            }
            // The textual tier (`indentation`) reads the units' source
            // text; unit indexes start past the library units. Names
            // ride along (AA7g): the generated-provenance rules audit
            // the sidecar placement contract, which is spelled in unit
            // names — with lint_with_sources they were silent in CI.
            let names: Vec<String> = sources
                .iter()
                .map(|(path, _)| path.display().to_string())
                .collect();
            let texts: Vec<(usize, &str, &str)> = sources
                .iter()
                .enumerate()
                .map(|(i, (_, src))| (boundary + i, names[i].as_str(), src.as_str()))
                .collect();
            let findings = sysmlv2_lint::lint_units(&mut resolved, &cfg, &texts);

            for f in &findings {
                match (f.unit, f.span) {
                    (Some(unit), Some(span)) => {
                        let (path, src) = &sources[unit - boundary];
                        let message = format!("{} [{}]", f.message, f.rule);
                        let diag = match f.severity {
                            sysmlv2_lint::Severity::Error => {
                                errors += 1;
                                sysmlv2_parser::Diagnostic::error(span, message)
                            }
                            _ => {
                                warnings += 1;
                                sysmlv2_parser::Diagnostic::warning(span, message)
                            }
                        };
                        report(path, src, &[diag]);
                    }
                    _ => {
                        warnings += 1;
                        eprintln!("warning: {} [{}]", f.message, f.rule);
                    }
                }
            }

            // Fix application: safe fixes under --fix; fixes that delete
            // model text additionally need --fix-deletes. Whole-line
            // deletions swallow their now-blank line; every rewritten
            // source must reparse cleanly before it is written back.
            if fix {
                let mut skipped_deletes = 0usize;
                let mut edits_by_unit: HashMap<usize, Vec<(Span, String)>> = HashMap::new();
                for f in &findings {
                    let Some(fx) = &f.fix else { continue };
                    if fx.deletes && !fix_deletes {
                        skipped_deletes += 1;
                        continue;
                    }
                    for e in &fx.edits {
                        edits_by_unit
                            .entry(e.unit)
                            .or_default()
                            .push((Span::new(e.span.start, e.span.end), e.replacement.clone()));
                    }
                }
                let mut units: Vec<_> = edits_by_unit.into_iter().collect();
                units.sort_by_key(|(u, _)| *u);
                for (unit, mut edits) in units {
                    let (path, src) = &sources[unit - boundary];
                    // Two findings can carry the same edit (each
                    // import-adding fix restates the insert so it works
                    // standalone) or overlapping ones (two rules
                    // rewriting one span) — identical edits collapse,
                    // and of an overlapping pair only the first
                    // survives.
                    edits.sort_by(|a, b| {
                        (a.0.start, a.0.end, &a.1).cmp(&(b.0.start, b.0.end, &b.1))
                    });
                    edits.dedup();
                    let mut kept: Vec<(Span, String)> = Vec::new();
                    for e in edits {
                        let overlaps = kept.last().is_some_and(|(prev, _)| e.0.start < prev.end);
                        if !overlaps {
                            kept.push(e);
                        }
                    }
                    let mut edits = kept;
                    edits.sort_by_key(|(s, _)| std::cmp::Reverse(s.start));
                    let mut text = src.clone();
                    for (span, replacement) in edits {
                        let (mut start, mut end) = (span.start as usize, span.end as usize);
                        if replacement.is_empty() {
                            // Swallow the whole line when deleting leaves
                            // it blank.
                            let line_start = text[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
                            let line_end = text[end..]
                                .find('\n')
                                .map(|i| end + i + 1)
                                .unwrap_or(text.len());
                            let blank = |s: &str| s.chars().all(char::is_whitespace);
                            if blank(&text[line_start..start])
                                && blank(text[end..line_end.min(text.len())].trim_end_matches('\n'))
                            {
                                start = line_start;
                                end = line_end;
                            }
                        }
                        text.replace_range(start..end, &replacement);
                    }
                    let reparse = parse_file(path, &text);
                    if !reparse.diagnostics.is_empty() {
                        eprintln!("error: fixes would break {} — not written", path.display());
                        errors += 1;
                        continue;
                    }
                    if !path.exists() {
                        eprintln!(
                            "note: {} is not a plain file (stdin or archive) — fixed text \
                             not written",
                            path.display()
                        );
                        continue;
                    }
                    if let Err(e) = std::fs::write(path, &text) {
                        eprintln!("error: cannot write {}: {e}", path.display());
                        errors += 1;
                        continue;
                    }
                    if !quiet {
                        eprintln!("fixed: {}", path.display());
                    }
                }
                if skipped_deletes > 0 {
                    eprintln!(
                        "{skipped_deletes} deletion fix(es) available but not applied — \
                         deleting model text needs --fix --fix-deletes"
                    );
                }
            }

            if warnings > 0 {
                eprintln!("{warnings} warning(s)");
            }
            if errors > 0 {
                eprintln!("{errors} error(s)");
                ExitCode::FAILURE
            } else if strict && warnings > 0 {
                eprintln!("--strict: warnings are failures");
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }

        #[cfg(feature = "solve")]
        Command::Verify {
            files,
            lib,
            ranges,
            solve,
            z3,
        } => {
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(lib) = &lib {
                lib_cache_path = match load_library(&mut model, lib) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", lib.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            // Unit indices: libraries first, then our files in order.
            let boundary = model.units().len();
            let mut sources: Vec<(&PathBuf, String)> = Vec::new();
            for path in &files {
                let src = match read(path) {
                    Ok(s) => s,
                    Err(code) => return code,
                };
                let unit = model.add_source(path.display().to_string(), &src);
                if !unit.diagnostics.is_empty() {
                    let diags = unit.diagnostics.clone();
                    report(path, &src, &diags);
                    return ExitCode::FAILURE;
                }
                sources.push((path, src));
            }
            let code = verify_and_report(&model, boundary, &sources, ranges, solve, z3);
            save_library_cache(&model, lib_cache_path);
            code
        }

        Command::Eval {
            input,
            names,
            all,
            lib,
        } => {
            // Positional arguments ending in a model extension are further
            // files joining the model; the rest are names to evaluate. The
            // leading positional joins the classification (an existing file
            // path counts even without a model extension), so with an
            // ambient model dir `sysmlv2 eval Demo::mass` is all names.
            let is_file = |s: &str| s.ends_with(".sysml") || s.ends_with(".kerml") || s == "-";
            let (extra_files, mut names): (Vec<String>, Vec<String>) =
                names.into_iter().partition(|n| is_file(n));
            let mut files: Vec<PathBuf> = Vec::new();
            if let Some(input) = input {
                let s = input.display().to_string();
                if is_file(&s) || input.is_file() {
                    files.push(input);
                } else {
                    names.insert(0, s);
                }
            }
            files.extend(extra_files.iter().map(PathBuf::from));
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(lib) = &lib {
                lib_cache_path = match load_library(&mut model, lib) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", lib.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            for path in &files {
                let src = match read(path) {
                    Ok(s) => s,
                    Err(code) => return code,
                };
                let unit = model.add_source(path.display().to_string(), &src);
                if !unit.diagnostics.is_empty() {
                    let diags = unit.diagnostics.clone();
                    report(path, &src, &diags);
                    return ExitCode::FAILURE;
                }
            }
            let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
            save_library_cache(&model, lib_cache_path);
            let mut failed = false;
            if all {
                for e in resolved.features_with_values() {
                    let label = resolved
                        .element_name(e)
                        .unwrap_or("<anonymous>")
                        .to_string();
                    match resolved.evaluate(e) {
                        Ok(v) => println!("{label} = {v}"),
                        Err(err) => println!("{label}: {err}"),
                    }
                }
            }
            for name in &names {
                if resolved.resolve_qualified(name).is_none() {
                    eprintln!("error: cannot resolve `{name}`");
                    failed = true;
                    continue;
                }
                // Chain-step semantics: the path prefix establishes the
                // featuring context, so `Pkg::part::attr` computes the
                // same value as `part.attr`.
                match resolved.evaluate_qualified(name) {
                    Ok(v) => println!("{name} = {v}"),
                    Err(err) => {
                        eprintln!("error: {name}: {err}");
                        failed = true;
                    }
                }
            }
            if failed {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }

        Command::Render { args, lib, html } => {
            let is_file = |s: &str| s.ends_with(".sysml") || s.ends_with(".kerml");
            let (files, names): (Vec<String>, Vec<String>) =
                args.into_iter().partition(|a| is_file(a));
            let [view_name] = names.as_slice() else {
                eprintln!(
                    "error: expected exactly one view usage name, got {}",
                    names.len()
                );
                return ExitCode::FAILURE;
            };
            let files = match resolve_inputs(files.into_iter().map(PathBuf::from).collect(), quiet)
            {
                Ok(files) => files,
                Err(code) => return code,
            };
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(lib) = &lib {
                lib_cache_path = match load_library(&mut model, lib) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", lib.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            for path in &files {
                let src = match read(path) {
                    Ok(s) => s,
                    Err(code) => return code,
                };
                let unit = model.add_source(path.display().to_string(), &src);
                if !unit.diagnostics.is_empty() {
                    let diags = unit.diagnostics.clone();
                    report(path, &src, &diags);
                    return ExitCode::FAILURE;
                }
            }
            let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
            save_library_cache(&model, lib_cache_path);
            let Some(view) = resolved.resolve_qualified(view_name) else {
                eprintln!("error: element not found: {view_name}");
                return ExitCode::FAILURE;
            };
            match resolved.render_view(view) {
                Ok(nodes) => {
                    if html {
                        println!("{}", sysmlv2_parser::render::to_html(&nodes));
                    } else {
                        let json =
                            serde_json::Value::Array(nodes.iter().map(|n| n.to_json()).collect());
                        println!("{}", serde_json::to_string_pretty(&json).unwrap());
                    }
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    ExitCode::FAILURE
                }
            }
        }
        Command::Query { input, args, lib } => {
            // Positional arguments ending in a model extension are further
            // files joining the model; exactly one remaining argument is
            // the query expression. The leading positional joins the
            // classification (an existing file path counts even without a
            // model extension), so with an ambient model dir
            // `sysmlv2 query '<expr>'` is just the expression.
            let is_file = |s: &str| s.ends_with(".sysml") || s.ends_with(".kerml") || s == "-";
            let (extra_files, mut exprs): (Vec<String>, Vec<String>) =
                args.into_iter().partition(|a| is_file(a));
            let mut files: Vec<PathBuf> = Vec::new();
            if let Some(input) = input {
                let s = input.display().to_string();
                if is_file(&s) || input.is_file() {
                    files.push(input);
                } else {
                    exprs.insert(0, s);
                }
            }
            files.extend(extra_files.iter().map(PathBuf::from));
            let [expr_src] = exprs.as_slice() else {
                eprintln!(
                    "error: expected exactly one query expression, got {}",
                    exprs.len()
                );
                return ExitCode::FAILURE;
            };
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let parsed = sysmlv2_parser::parser::parse_expression(expr_src);
            if !parsed.diagnostics.is_empty() {
                report(Path::new("<query>"), expr_src, &parsed.diagnostics);
                return ExitCode::FAILURE;
            }
            let Some(expr) = parsed.expr else {
                eprintln!("error: the query is not an expression");
                return ExitCode::FAILURE;
            };
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(lib) = &lib {
                lib_cache_path = match load_library(&mut model, lib) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", lib.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            for path in &files {
                let src = match read(path) {
                    Ok(s) => s,
                    Err(code) => return code,
                };
                let unit = model.add_source(path.display().to_string(), &src);
                if !unit.diagnostics.is_empty() {
                    let diags = unit.diagnostics.clone();
                    report(path, &src, &diags);
                    return ExitCode::FAILURE;
                }
            }
            let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
            save_library_cache(&model, lib_cache_path);
            let root = resolved.root_scope();
            match resolved.query(root, &expr) {
                Ok(sysmlv2_parser::eval::Value::Sequence(items)) => {
                    for item in items {
                        println!("{}", render_query_value(&mut resolved, &item));
                    }
                    ExitCode::SUCCESS
                }
                Ok(v) => {
                    println!("{}", render_query_value(&mut resolved, &v));
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    ExitCode::FAILURE
                }
            }
        }

        Command::Describe { input, args, lib } => {
            let (mut resolved, qname) =
                match resolve_model_and_name(input, args, lib.as_deref(), quiet) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
            let Some(e) = resolved.resolve_qualified(&qname) else {
                eprintln!("error: cannot resolve `{qname}`");
                return ExitCode::FAILURE;
            };
            println!("{qname}");
            println!("  metaclass  {}", resolved.element_type(e));
            let owner = resolved.owner(e);
            if let Some(owner) = owner {
                if let Some(oq) = resolved.element_qualified_name(owner) {
                    println!("  owner      {oq}");
                }
            }
            if let Some(t) = resolved.typings(e).first().copied() {
                let label = resolved
                    .element_qualified_name(t)
                    .or_else(|| resolved.element_name(t).map(str::to_string));
                if let Some(label) = label {
                    println!("  type       {label}");
                }
            }
            if let Some(owner) = owner {
                let members = resolved.owned_members(owner);
                if let Some(idx) = members.iter().position(|m| *m == e) {
                    println!("  position   {} of {}", idx + 1, members.len());
                }
            }
            if let Some((file, line, col)) = resolved.declaration_position(e) {
                println!("  location   {file}:{line}:{col}");
            }
            ExitCode::SUCCESS
        }

        Command::Members { input, args, lib } => {
            let (mut resolved, qname) =
                match resolve_model_and_name(input, args, lib.as_deref(), quiet) {
                    Ok(v) => v,
                    Err(code) => return code,
                };
            let Some(e) = resolved.resolve_qualified(&qname) else {
                eprintln!("error: cannot resolve `{qname}`");
                return ExitCode::FAILURE;
            };
            for m in resolved.owned_members(e) {
                let name = resolved
                    .element_name(m)
                    .unwrap_or("(anonymous)")
                    .to_string();
                println!("{name:<28} {}", resolved.element_type(m));
            }
            ExitCode::SUCCESS
        }

        Command::Refactor { op } => run_refactor(op, quiet),
        Command::Parse { input, ast } => {
            // Ambient inputs make this a per-file loop: each file parses
            // (and reports) independently, any diagnostic fails the run.
            let files = match resolve_inputs(input.into_iter().collect(), quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let mut failed = false;
            for input in &files {
                let src = match read(input) {
                    Ok(s) => s,
                    Err(code) => return code,
                };
                let parse = parse_file(input, &src);
                report(input, &src, &parse.diagnostics);
                if ast {
                    println!("{:#?}", parse.unit);
                } else {
                    println!(
                        "{}: {} top-level member(s), {} diagnostic(s)",
                        input.display(),
                        parse.unit.members.len(),
                        parse.diagnostics.len()
                    );
                }
                failed |= !parse.diagnostics.is_empty();
            }
            if failed {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }
        #[cfg(feature = "viz")]
        Command::Viz {
            files,
            view,
            element,
            lib,
            horizontal,
            no_values,
            no_notes,
            hide_metadata,
            show_inherited,
            show_lib,
            show_imported,
            line_style,
            color,
            link_template,
            output,
        } => {
            let view = match view.as_deref() {
                None => None,
                Some("tree") => Some(sysmlv2_viz::View::Tree),
                Some("interconnection" | "ic") => Some(sysmlv2_viz::View::Interconnection),
                Some("state") => Some(sysmlv2_viz::View::State),
                Some("action") => Some(sysmlv2_viz::View::Action),
                Some("sequence" | "seq") => Some(sysmlv2_viz::View::Sequence),
                Some("case") => Some(sysmlv2_viz::View::Case),
                Some("mixed") => Some(sysmlv2_viz::View::Mixed),
                Some(other) => {
                    eprintln!(
                        "error: unknown view `{other}` (expected tree, interconnection, state, action, sequence, case, or mixed)"
                    );
                    return ExitCode::FAILURE;
                }
            };
            let line_style = match line_style.as_deref() {
                None => sysmlv2_viz::LineStyle::Default,
                Some("polyline") => sysmlv2_viz::LineStyle::Polyline,
                Some("ortho") => sysmlv2_viz::LineStyle::Ortho,
                Some(other) => {
                    eprintln!("error: unknown line style `{other}` (expected polyline or ortho)");
                    return ExitCode::FAILURE;
                }
            };
            let files = match resolve_inputs(files, quiet) {
                Ok(files) => files,
                Err(code) => return code,
            };
            let inputs = match read_inputs(&files) {
                Ok(i) => i,
                Err(code) => return code,
            };
            let mut model = Model::new();
            let mut lib_cache_path = None;
            if let Some(dir) = &lib {
                lib_cache_path = match load_library(&mut model, dir) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("error: cannot load library {}: {e}", dir.display());
                        return ExitCode::FAILURE;
                    }
                };
            }
            let mut parse_errors = false;
            for (path, src) in &inputs {
                let unit = model.add_source(path.display().to_string(), src);
                if !unit.diagnostics.is_empty() {
                    let diags = unit.diagnostics.clone();
                    report(path, src, &diags);
                    parse_errors = true;
                }
            }
            if parse_errors {
                return ExitCode::FAILURE;
            }
            let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
            save_library_cache(&model, lib_cache_path);
            let root = match &element {
                Some(name) => match resolved.resolve_qualified(name) {
                    Some(e) => Some(e),
                    None => {
                        eprintln!("error: element not found: {name}");
                        return ExitCode::FAILURE;
                    }
                },
                None => None,
            };
            // A view usage directs its own rendering: the diagram's
            // elements are what the view exposes (filter conditions
            // applied), and its `render` member picks the style unless
            // --view was given explicitly.
            let (root, view, roots) = match root {
                Some(e) => match sysmlv2_viz::view_directed(&mut resolved, e) {
                    Some((style, exposed)) => (None, view.or(style), Some(exposed)),
                    None => (Some(e), view, None),
                },
                None => (None, view, None),
            };
            let view = view.unwrap_or(sysmlv2_viz::View::Tree);
            let opts = sysmlv2_viz::VizOptions {
                direction: if horizontal {
                    sysmlv2_viz::Direction::LeftToRight
                } else {
                    sysmlv2_viz::Direction::TopToBottom
                },
                show_values: !no_values,
                view,
                show_notes: !no_notes,
                show_metadata: !hide_metadata,
                show_inherited,
                show_lib,
                show_imported,
                line_style,
                std_color: color,
                link_template,
                roots,
            };
            let text = sysmlv2_viz::plantuml(&mut resolved, root, &opts);
            match &output {
                Some(path) => {
                    if let Err(e) = std::fs::write(path, &text) {
                        eprintln!("error: cannot write {}: {e}", path.display());
                        return ExitCode::FAILURE;
                    }
                }
                None => print!("{text}"),
            }
            ExitCode::SUCCESS
        }

        #[cfg(feature = "lsp")]
        Command::Lsp { lib } => match sysmlv2_lsp::run_stdio(lib) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("error: {e}");
                ExitCode::FAILURE
            }
        },
    }
}

#[cfg(test)]
mod refactor_persistence_tests {
    use super::*;

    struct TestDir(PathBuf);

    impl TestDir {
        fn new() -> Self {
            let path = std::env::temp_dir()
                .join(format!("sysmlv2-cli-persist-test-{}", uuid::Uuid::new_v4()));
            std::fs::create_dir(&path).expect("create test directory");
            Self(path)
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn a_later_replace_failure_rolls_back_earlier_files() {
        let dir = TestDir::new();
        let a = dir.0.join("a.sysml");
        let b = dir.0.join("b.sysml");
        std::fs::write(&a, "old a\n").unwrap();
        std::fs::write(&b, "old b\n").unwrap();
        let changes = vec![
            RefactorFileChange {
                path: a.clone(),
                old: "old a\n".into(),
                new: "new a\n".into(),
            },
            RefactorFileChange {
                path: b.clone(),
                old: "old b\n".into(),
                new: "new b\n".into(),
            },
        ];
        let mut promotions = 0;
        let error = persist_refactor_changes_with(&changes, |from, to| {
            if from
                .file_name()
                .is_some_and(|n| n.to_string_lossy().contains(".sysmlv2-new-"))
            {
                promotions += 1;
                if promotions == 2 {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::PermissionDenied,
                        "simulated second replacement failure",
                    ));
                }
            }
            std::fs::rename(from, to)
        })
        .expect_err("second replacement must fail");

        assert!(error.contains("simulated second replacement failure"));
        assert!(error.contains("rolled back 1 earlier file(s)"));
        assert_eq!(std::fs::read_to_string(a).unwrap(), "old a\n");
        assert_eq!(std::fs::read_to_string(b).unwrap(), "old b\n");
        let leftovers: Vec<_> = std::fs::read_dir(&dir.0)
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n.to_string_lossy().contains(".sysmlv2-"))
            .collect();
        assert!(leftovers.is_empty(), "leftover sidecars: {leftovers:?}");
    }

    #[test]
    fn a_concurrent_later_edit_is_preserved_while_earlier_files_roll_back() {
        let dir = TestDir::new();
        let a = dir.0.join("a.sysml");
        let b = dir.0.join("b.sysml");
        std::fs::write(&a, "old a\n").unwrap();
        std::fs::write(&b, "old b\n").unwrap();
        let changes = vec![
            RefactorFileChange {
                path: a.clone(),
                old: "old a\n".into(),
                new: "new a\n".into(),
            },
            RefactorFileChange {
                path: b.clone(),
                old: "old b\n".into(),
                new: "new b\n".into(),
            },
        ];
        let mut promotions = 0;
        let error = persist_refactor_changes_with(&changes, |from, to| {
            let is_promotion = from
                .file_name()
                .is_some_and(|n| n.to_string_lossy().contains(".sysmlv2-new-"));
            let result = std::fs::rename(from, to);
            if is_promotion {
                promotions += 1;
                if promotions == 1 {
                    std::fs::write(&b, "external b\n").unwrap();
                }
            }
            result
        })
        .expect_err("concurrent second-file edit must refuse");

        assert!(error.contains("changed on disk before it could be replaced"));
        assert!(error.contains("rolled back 1 earlier file(s)"));
        assert_eq!(std::fs::read_to_string(a).unwrap(), "old a\n");
        assert_eq!(std::fs::read_to_string(b).unwrap(), "external b\n");
    }

    #[test]
    fn a_concurrent_edit_to_an_applied_file_is_not_overwritten_by_rollback() {
        let dir = TestDir::new();
        let a = dir.0.join("a.sysml");
        let b = dir.0.join("b.sysml");
        std::fs::write(&a, "old a\n").unwrap();
        std::fs::write(&b, "old b\n").unwrap();
        let changes = vec![
            RefactorFileChange {
                path: a.clone(),
                old: "old a\n".into(),
                new: "new a\n".into(),
            },
            RefactorFileChange {
                path: b.clone(),
                old: "old b\n".into(),
                new: "new b\n".into(),
            },
        ];
        let mut promotions = 0;
        let error = persist_refactor_changes_with(&changes, |from, to| {
            let is_promotion = from
                .file_name()
                .is_some_and(|n| n.to_string_lossy().contains(".sysmlv2-new-"));
            if is_promotion {
                promotions += 1;
                if promotions == 2 {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::PermissionDenied,
                        "simulated second replacement failure",
                    ));
                }
            }
            let result = std::fs::rename(from, to);
            if is_promotion && promotions == 1 {
                std::fs::write(&a, "external a\n").unwrap();
            }
            result
        })
        .expect_err("second replacement must fail");

        assert!(error.contains("rollback incomplete"), "{error}");
        assert!(error.contains("external edit was preserved"), "{error}");
        assert!(error.contains("recovery copy:"), "{error}");
        assert_eq!(std::fs::read_to_string(&a).unwrap(), "external a\n");
        assert_eq!(std::fs::read_to_string(&b).unwrap(), "old b\n");
        let leftovers: Vec<_> = std::fs::read_dir(&dir.0)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| {
                p.file_name()
                    .is_some_and(|n| n.to_string_lossy().contains(".sysmlv2-"))
            })
            .collect();
        assert_eq!(leftovers.len(), 1, "retained recovery copy: {leftovers:?}");
        assert_eq!(std::fs::read_to_string(&leftovers[0]).unwrap(), "old a\n");
    }

    #[cfg(all(unix, not(target_os = "wasi")))]
    #[test]
    fn a_hard_linked_target_is_refused_without_splitting_the_links() {
        let dir = TestDir::new();
        let path = dir.0.join("model.sysml");
        let alias = dir.0.join("alias.sysml");
        std::fs::write(&path, "old\n").unwrap();
        std::fs::hard_link(&path, &alias).unwrap();
        let changes = [RefactorFileChange {
            path: path.clone(),
            old: "old\n".into(),
            new: "new\n".into(),
        }];

        let error = persist_refactor_changes(&changes).expect_err("hard link must refuse");

        assert!(error.contains("has 2 hard links"), "{error}");
        assert_eq!(std::fs::read_to_string(path).unwrap(), "old\n");
        assert_eq!(std::fs::read_to_string(alias).unwrap(), "old\n");
    }

    #[cfg(all(unix, not(target_os = "wasi")))]
    #[test]
    fn a_successful_replacement_preserves_unix_file_metadata() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        let dir = TestDir::new();
        let path = dir.0.join("model.sysml");
        std::fs::write(&path, "old\n").unwrap();
        std::fs::set_permissions(&path, Permissions::from_mode(0o640)).unwrap();
        let xattr_name = if cfg!(target_os = "macos") {
            "com.openmbee.sysmlv2-test"
        } else {
            "user.sysmlv2-test"
        };
        xattr::set(&path, xattr_name, b"retained").unwrap();
        let original_metadata = std::fs::metadata(&path).unwrap();
        let changes = [RefactorFileChange {
            path: path.clone(),
            old: "old\n".into(),
            new: "new\n".into(),
        }];

        persist_refactor_changes(&changes).expect("replacement succeeds");

        assert_eq!(std::fs::read_to_string(&path).unwrap(), "new\n");
        let replaced_metadata = std::fs::metadata(&path).unwrap();
        assert_eq!(replaced_metadata.permissions().mode() & 0o777, 0o640);
        assert_eq!(replaced_metadata.uid(), original_metadata.uid());
        assert_eq!(replaced_metadata.gid(), original_metadata.gid());
        assert_eq!(
            xattr::get(path, xattr_name).unwrap().as_deref(),
            Some(b"retained".as_slice())
        );
    }
}
