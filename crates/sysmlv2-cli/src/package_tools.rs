//! Textual model checks for project packaging.

use super::{ReportFormat, Reporter, Sink, check_inputs, load_library, new_model, write_json};
use std::collections::{BTreeMap, HashSet};
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use sysmlv2_parser::check::{member_identification, validate_model_with};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::ParsedSource;

/// Refuse a file that is not textual SysML or KerML. One project may
/// hold both: a `.kerml` file is a model of the SysML metamodel too, and
/// the archive writer and `check` take the two together.
fn check_language(path: &Path) -> Result<(), String> {
    if super::is_model_source(path) {
        Ok(())
    } else {
        Err(format!(
            "{}: expected a .sysml or .kerml file",
            path.display()
        ))
    }
}

/// Add one file's entries to a project index: every top-level name and
/// short name maps to the file's path in the archive. This is the one
/// rule for the index, whether `kpar-index` prints it or `convert --to
/// kpar` writes it into `.meta.json`. A name two files declare is
/// refused, since an index holds one path per name.
pub(super) fn add_to_index(
    index: &mut BTreeMap<String, String>,
    unit: &sysmlv2_parser::ast::SourceUnit,
    archive_path: &str,
) -> Result<(), String> {
    for id in unit
        .members
        .iter()
        .filter_map(|member| member_identification(&member.kind))
    {
        for name in [id.name.as_ref(), id.short_name.as_ref()]
            .into_iter()
            .flatten()
        {
            if let Some(previous) = index
                .insert(name.value.clone(), archive_path.to_string())
                .filter(|previous| previous != archive_path)
            {
                return Err(format!(
                    "{} is declared in both {previous} and {archive_path}",
                    name.value
                ));
            }
        }
    }
    Ok(())
}

fn index(root: &Path, files: Vec<PathBuf>) -> Result<BTreeMap<String, String>, String> {
    let root = root
        .canonicalize()
        .map_err(|e| format!("{}: {e}", root.display()))?;
    let mut index = BTreeMap::new();
    for input in files {
        let path = root.join(input);
        check_language(&path)?;
        let path = path
            .canonicalize()
            .map_err(|e| format!("{}: {e}", path.display()))?;
        let relative = path
            .strip_prefix(&root)
            .map_err(|_| format!("{} is outside the project root", path.display()))?;
        let archive_path = relative
            .components()
            .map(|part| match part {
                Component::Normal(part) => part.to_str(),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| format!("{}: invalid archive path", path.display()))?
            .join("/");
        let source =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let parsed = ParsedSource::new(path.display().to_string(), &source);
        if !parsed.diagnostics().is_empty() {
            let mut reporter = Reporter::new(&path, &source);
            for diagnostic in parsed.diagnostics() {
                reporter.report(diagnostic);
            }
            return Err(format!(
                "{}: cannot index a model with parse errors",
                path.display()
            ));
        }
        add_to_index(&mut index, parsed.unit(), &archive_path)?;
    }
    Ok(index)
}

pub(super) fn run_index(root: &Path, files: Vec<PathBuf>) -> ExitCode {
    match index(root, files) {
        Ok(index) => match write_json(None, &serde_json::json!(index)) {
            Ok(()) => ExitCode::SUCCESS,
            Err(code) => code,
        },
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::FAILURE
        }
    }
}

pub(super) fn run_project_check(
    project: Vec<PathBuf>,
    direct: Vec<PathBuf>,
    transitive: Vec<PathBuf>,
    lib: Option<&Path>,
    direct_only: bool,
    strict: bool,
    format: ReportFormat,
) -> ExitCode {
    let project_count = project.len();
    let direct_count = project_count + direct.len();
    let mut inputs = Vec::new();
    let mut seen = HashSet::new();
    let result = (|| {
        for files in [project, direct, transitive] {
            for file in files {
                check_language(&file)?;
                let path = file
                    .canonicalize()
                    .map_err(|e| format!("{}: {e}", file.display()))?;
                if !seen.insert(path.clone()) {
                    return Err(format!("{} is listed more than once", file.display()));
                }
                let source = std::fs::read_to_string(&path)
                    .map_err(|e| format!("{}: {e}", file.display()))?;
                inputs.push((file, source));
            }
        }
        Ok(())
    })();
    if let Err(message) = result {
        eprintln!("error: {message}");
        return ExitCode::FAILURE;
    }
    let scopes = direct_only.then_some((project_count, direct_count));
    check_inputs(&inputs, lib, strict, format, scopes)
}

/// The referential findings of the whole model: input index, span and
/// message.
pub(super) type Reported = HashSet<(usize, sysmlv2_parser::span::Span, String)>;

/// Resolve the project's files again with only the direct dependencies
/// beside them, and report what no longer resolves. A finding the whole
/// model already has (in `reported`) is not caused by the missing files
/// and is left out. Runs only after the whole model passed without
/// errors, so every input parsed.
pub(super) fn direct_diagnostics(
    inputs: &[(PathBuf, String)],
    lib: Option<&Path>,
    (project_count, direct_count): (usize, usize),
    reported: &Reported,
    sink: &mut Sink<'_>,
) -> Result<usize, ExitCode> {
    if direct_count == inputs.len() {
        return Ok(0);
    }
    let mut model = new_model();
    if let Some(lib) = lib {
        load_library(&mut model, lib).map_err(|e| {
            eprintln!("error: cannot load library {}: {e}", lib.display());
            ExitCode::FAILURE
        })?;
    }
    let boundary = model.unit_count();
    for (path, source) in &inputs[..direct_count] {
        model.add_parsed_source(ParsedSource::new(path.display().to_string(), source));
    }
    let mut resolved = ResolvedModel::build(&model);
    let mut errors = 0;
    for (unit, diagnostic) in validate_model_with(&mut resolved, &model) {
        let Some(input) = unit
            .checked_sub(boundary)
            .filter(|&input| input < project_count)
        else {
            continue;
        };
        let key = (input, diagnostic.span, diagnostic.message);
        if reported.contains(&key) {
            continue;
        }
        let (_, span, message) = key;
        let finding = sysmlv2_parser::Diagnostic::error(
            span,
            format!(
                "{message} among the direct dependencies: it resolves only through a \
                 transitive dependency, which the project must declare directly"
            ),
        )
        .with_code("direct-dependency");
        // A referential finding like any other; the rule tells it apart.
        sink.diagnostic("referential", input, &finding);
        errors += 1;
    }
    Ok(errors)
}
