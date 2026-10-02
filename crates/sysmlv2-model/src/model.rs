//! Multi-file model container.
//!
//! A [`Model`] holds any number of parsed source units — user model files
//! plus (optionally) the standard library — forming one resolution context:
//! every unit's top-level members are visible in the shared global root
//! namespace, so cross-file references (e.g. `ScalarValues::Real`) resolve.
//!
//! The compact-JSON emitter consumes a model via
//! [`crate::json::model_to_compact_json`], which serializes the non-library
//! units' elements with references into library units resolved to element
//! IDs.

use std::io;
use std::path::Path;
use sysmlv2_syntax::ast::{Dialect, SourceUnit};
use sysmlv2_syntax::diag::Diagnostic;
use sysmlv2_syntax::parser::{Parse, parse_kerml_source, parse_source};
use sysmlv2_syntax::span::LineIndex;

/// One parsed file within a model.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct ModelUnit {
    /// Display name (usually the file name); also salts element IDs.
    pub name: String,
    /// Parsed syntax shared by prepared-library models. Clone the Arc for
    /// sharing, or use `unit.as_ref().clone()` for an independent syntax tree.
    pub unit: std::sync::Arc<SourceUnit>,
    pub diagnostics: Vec<Diagnostic>,
    /// Library units provide resolution targets but are not serialized.
    pub is_library: bool,
    /// Line-start index of the source text — line/column reporting for
    /// spans recorded against this unit.
    pub lines: LineIndex,
}

/// A parsed user source whose name, syntax and line index travel together.
///
/// Inspect diagnostics or validate the syntax, then transfer this value into
/// a model with [`Model::add_parsed_source`] without parsing the text again.
/// The original source text is not retained.
pub struct ParsedSource {
    name: String,
    parse: Parse,
    lines: LineIndex,
}

impl ParsedSource {
    /// Parse using the name's case-insensitive extension: `.kerml` selects
    /// KerML; other names select SysML, as with [`Model::add_source`].
    #[must_use]
    pub fn new(name: impl Into<String>, src: &str) -> Self {
        let name = name.into();
        let parse = match Model::dialect_for(&name) {
            Dialect::Kerml => parse_kerml_source(src),
            Dialect::Sysml => parse_source(src),
        };
        Self {
            name,
            parse,
            lines: LineIndex::new(src),
        }
    }

    /// Display name and element-ID seed of this source.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Parsed syntax, including recovered members when diagnostics exist.
    #[must_use]
    pub fn unit(&self) -> &SourceUnit {
        &self.parse.unit
    }

    /// Parse diagnostics; context and model validation are separate stages.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.parse.diagnostics
    }

    /// Line index for positions in this source's syntax and diagnostics.
    #[must_use]
    pub fn lines(&self) -> &LineIndex {
        &self.lines
    }
}

/// Original owned Boolean inputs from one structurally paired payload row.
/// This is source provenance, not inferred semantic state.
#[derive(Clone)]
pub(crate) struct PayloadOwnedFlags {
    pub(crate) metaclass: &'static str,
    pub(crate) flags: crate::properties::Properties,
}

// Retain the original syntax allocation so an edited or replaced source cannot
// reuse payload values merely by occupying the same ordinal and lowering path.
struct PayloadSource {
    name: String,
    syntax: std::sync::Arc<SourceUnit>,
    flags: std::collections::HashMap<String, PayloadOwnedFlags>,
}

pub(crate) const PAYLOAD_USAGE_FLAGS: &[&str] =
    &["isConstant", "isEnd", "isComposite", "isPortion"];

pub(crate) fn is_payload_usage_flag(metaclass: &str, name: &str) -> bool {
    PAYLOAD_USAGE_FLAGS.contains(&name)
        && crate::metaclass::conforms(metaclass, "Usage")
        && crate::semantic_catalog::property(metaclass, name)
            .and_then(|(_, effective)| effective)
            .is_some_and(|p| !p.derived && p.target == "Boolean")
}

/// Authored graph/identity contract. Existing constructors retain the legacy shape.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum GraphFormat {
    #[default]
    LegacyV2,
    /// Conditional operands own expression-reference wrappers; constructor
    /// arguments are owned by an explicit result Feature. Textual end constancy
    /// uses checked variability evidence.
    CanonicalV3,
}
impl GraphFormat {
    /// Version carried by graph-aware caches and binary interchange.
    pub const fn version(self) -> u8 {
        match self {
            Self::LegacyV2 => 2,
            Self::CanonicalV3 => 3,
        }
    }
}

/// A set of parsed source units sharing one global root namespace.
#[derive(Default)]
pub struct Model {
    graph_format: GraphFormat,
    units: Vec<ModelUnit>,
    // Original text is retained only for library snapshots. Public ModelUnit
    // continues to expose the exact, shared syntax tree.
    sources: Vec<std::sync::Arc<str>>,
    library: Option<std::sync::Arc<crate::prepared::LibraryUnits>>,
    all_units: std::sync::OnceLock<Vec<ModelUnit>>,
    pub(crate) prepared: Option<std::sync::Arc<crate::prepared::PreparedLibrary>>,
    /// Standard-library resolution cache state (see [`crate::libcache`]).
    /// Interior mutability: the builder consumes hints / deposits a
    /// recording through `&Model`.
    lib_cache: std::cell::RefCell<LibCacheSlot>,
    // Original unit ordinal + lowering path identify immutable input syntax
    // before graph-effective IDs are assigned. Empty entries still mark a
    // lifted payload unit, which must not acquire text-only defaults.
    payload_sources: std::collections::HashMap<usize, PayloadSource>,
    /// The outcomes the next build starts from, and the outcomes a build
    /// settled on (see [`crate::json::settled`]). Interior mutability: the
    /// builder takes the one and deposits the other through `&Model`.
    settled: std::cell::RefCell<SettledSlot>,
}

/// The settled-outcomes state carried by a [`Model`].
#[derive(Default)]
pub(crate) struct SettledSlot {
    /// Whether a build keeps the outcomes it settles on.
    keep: bool,
    /// The outcomes the next build starts from.
    start: Option<std::sync::Arc<crate::json::settled::SettledOutcomes>>,
    /// The outcomes the last build settled on, when kept.
    kept: Option<std::sync::Arc<crate::json::settled::SettledOutcomes>>,
}

/// Library-cache state carried by a [`Model`].
#[derive(Default)]
pub(crate) enum LibCacheSlot {
    /// No caching (the default; also the post-consumption state).
    #[default]
    Off,
    /// Replay these outcomes on the next build. Shared: a build reads
    /// the recorded ids in place and the slot survives repeated builds.
    Use(std::sync::Arc<crate::libcache::LibraryCache>),
    /// Record outcomes during the next build.
    Record,
    /// Outcomes recorded by a build, awaiting [`Model::take_recorded_library_cache`].
    Recorded(crate::libcache::LibraryCache),
    /// A recording held back, read only if a build cannot reuse the prepared
    /// graph. Prepared builds never pay for loading it.
    Lazy(LazyRecording),
}

/// Where a held-back recording comes from: a cache file, or the encoded
/// bytes a host already holds (a browser fetched them beside the prepared
/// snapshot), decoded only when a build needs them.
pub(crate) enum LazyRecording {
    File(std::path::PathBuf),
    Bytes(std::sync::Arc<[u8]>),
}

impl LazyRecording {
    fn load(&self) -> Option<crate::libcache::LibraryCache> {
        match self {
            Self::File(path) => crate::libcache::LibraryCache::load(path),
            Self::Bytes(bytes) => crate::libcache::LibraryCache::from_bytes(bytes),
        }
    }
}

impl Model {
    /// Choose the authored graph format before loading sources or prepared libraries.
    pub fn with_graph_format(graph_format: GraphFormat) -> Self {
        Self {
            graph_format,
            ..Self::default()
        }
    }

    pub fn graph_format(&self) -> GraphFormat {
        self.graph_format
    }

    pub(crate) fn add_payload_source(&mut self, name: impl Into<String>, text: &str) -> &ModelUnit {
        let index = self.unit_count();
        let unit = self.add_source(name, text);
        let origin = PayloadSource {
            name: unit.name.clone(),
            syntax: unit.unit.clone(),
            flags: std::collections::HashMap::new(),
        };
        self.payload_sources.insert(index, origin);
        self.unit(index)
    }

    pub(crate) fn payload_source_flags(
        &self,
        unit: usize,
    ) -> Option<&std::collections::HashMap<String, PayloadOwnedFlags>> {
        let origin = self.payload_sources.get(&unit)?;
        if unit >= self.unit_count() {
            return None;
        }
        let current = self.unit(unit);
        (!current.is_library
            && current.name == origin.name
            && std::sync::Arc::ptr_eq(&current.unit, &origin.syntax))
        .then_some(&origin.flags)
    }

    pub(crate) fn retain_payload_flags(
        &mut self,
        unit: usize,
        path: String,
        input: PayloadOwnedFlags,
    ) {
        if self.payload_source_flags(unit).is_some() {
            self.payload_sources
                .get_mut(&unit)
                .unwrap()
                .flags
                .insert(path, input);
        }
    }

    pub(crate) fn install_prepared(
        &mut self,
        library: std::sync::Arc<crate::prepared::PreparedLibrary>,
    ) -> io::Result<()> {
        if self.unit_count() != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "install a prepared library before adding source units",
            ));
        }
        if library.graph_format() != self.graph_format {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "prepared library graph format differs from the model",
            ));
        }
        self.library = Some(library.units.clone());
        // A library decoded from a snapshot keeps no recording, but it may hold
        // the encoded one for the build that must resolve it jointly after all.
        if library.recording.is_none() {
            if let Some(bytes) = &library.lazy_recording {
                let mut slot = self.lib_cache.borrow_mut();
                if matches!(*slot, LibCacheSlot::Off) {
                    *slot = LibCacheSlot::Lazy(LazyRecording::Bytes(std::sync::Arc::clone(bytes)));
                }
            }
        }
        self.prepared = Some(library);
        Ok(())
    }

    /// Arm the recording the installed prepared library keeps, for a build
    /// that cannot reuse its prepared graph: such a build then replays the
    /// recording instead of resolving the whole library afresh. A slot the
    /// caller set (a recording in progress, a snapshot, a lazy cache file)
    /// stays in place.
    pub(crate) fn arm_prepared_recording(&self) {
        let Some(recording) = self
            .prepared
            .as_ref()
            .and_then(|library| library.recording.as_ref())
        else {
            return;
        };
        let mut slot = self.lib_cache.borrow_mut();
        if matches!(*slot, LibCacheSlot::Off) {
            *slot = LibCacheSlot::Use(std::sync::Arc::clone(recording));
        }
    }

    /// Prepare and retain this library-only model for subsequent user builds.
    pub fn prepare_library(
        &mut self,
    ) -> io::Result<std::sync::Arc<crate::prepared::PreparedLibrary>> {
        let library = std::sync::Arc::new(crate::prepared::PreparedLibrary::build(self)?);
        self.prepared = Some(library.clone());
        Ok(library)
    }

    #[must_use]
    pub fn new() -> Self {
        Model::default()
    }

    /// The dialect a unit name spells. The extension is read without
    /// case, so `Model.KerML` is KerML like `model.kerml` — the file
    /// systems these names come from do not distinguish the two.
    pub(crate) fn dialect_for(name: &str) -> Dialect {
        let kerml = Path::new(name)
            .extension()
            .is_some_and(|e| e.eq_ignore_ascii_case("kerml"));
        if kerml {
            Dialect::Kerml
        } else {
            Dialect::Sysml
        }
    }

    fn add_parsed(&mut self, parsed: ParsedSource, source: Option<&str>) -> &ModelUnit {
        self.all_units.take();
        let is_library = source.is_some();
        if is_library {
            self.prepared = None;
        }
        self.sources.push(source.unwrap_or("").into());
        self.units.push(ModelUnit {
            name: parsed.name,
            unit: std::sync::Arc::new(parsed.parse.unit),
            diagnostics: parsed.parse.diagnostics,
            is_library,
            lines: parsed.lines,
        });
        self.units.last().unwrap()
    }

    /// Add an already parsed user source without reparsing or cloning its tree.
    /// Like [`Self::add_source`], this retains partial syntax and diagnostics;
    /// callers requiring clean syntax must check them before building a model.
    pub fn add_parsed_source(&mut self, parsed: ParsedSource) -> &ModelUnit {
        self.add_parsed(parsed, None)
    }

    /// Parse and add a user source. The dialect is chosen by the name's
    /// extension, read without case (`.kerml` → KerML, anything else →
    /// SysML).
    ///
    /// The name also seeds the source document's root identity and therefore
    /// its derived user-element IDs. Give distinct documents distinct stable
    /// names, such as project-relative paths; a basename alone is insufficient
    /// when files in different directories share it. Names are not deduplicated
    /// or normalized by this method. Reusing a name can produce duplicate IDs;
    /// changing it changes the freshly derived identities for that document.
    pub fn add_source(&mut self, name: impl Into<String>, src: &str) -> &ModelUnit {
        self.add_parsed_source(ParsedSource::new(name, src))
    }

    /// Parse and add a library source: it participates in name resolution
    /// but its elements are not included in serialized output.
    pub fn add_library_source(&mut self, name: impl Into<String>, src: &str) -> &ModelUnit {
        self.add_parsed(ParsedSource::new(name, src), Some(src))
    }

    /// Recursively load every `.sysml` / `.kerml` file under `dir` as
    /// library content (e.g. the vendored `sysml.library`). Returns the
    /// number of files loaded.
    pub fn load_library_dir(&mut self, dir: &Path) -> io::Result<usize> {
        let files = library_dir_files(dir)?;
        let count = files.len();
        for path in files {
            let src = std::fs::read_to_string(&path)?;
            let name = path
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default();
            self.add_library_source(name, &src);
        }
        Ok(count)
    }

    /// All parsed units. A disk-loaded library reconstructs syntax on first
    /// access; validation and unit metadata queries do not require this work.
    pub fn units(&self) -> &[ModelUnit] {
        if let Some(library) = &self.library {
            self.all_units.get_or_init(|| {
                (0..library.len())
                    .map(|i| library.unit(i).clone())
                    .chain(self.units.iter().cloned())
                    .collect()
            })
        } else {
            &self.units
        }
    }

    /// Number of units, without materializing library syntax.
    pub fn unit_count(&self) -> usize {
        self.library.as_ref().map_or(0, |l| l.len()) + self.units.len()
    }

    /// Access one parsed unit, reconstructing only that library file if needed.
    ///
    /// # Panics
    ///
    /// When `index` is not a unit of this model — it must be below
    /// [`Self::unit_count`].
    pub fn unit(&self, index: usize) -> &ModelUnit {
        let boundary = self.library.as_ref().map_or(0, |l| l.len());
        if index < boundary {
            self.library.as_ref().unwrap().unit(index)
        } else {
            &self.units[index - boundary]
        }
    }

    /// Library units whose syntax tree is currently in memory. A prepared
    /// library starts at zero and grows only through [`Self::units`] or
    /// [`Self::unit`]; source-loaded libraries always count every unit.
    /// Diagnostic for callers that must stay on the metadata-only paths.
    pub fn loaded_library_unit_count(&self) -> usize {
        self.library.as_ref().map_or(0, |l| l.loaded())
            + self.units.iter().filter(|u| u.is_library).count()
    }

    /// Whether a unit supplies library definitions, without loading its syntax.
    pub fn is_library_unit(&self, index: usize) -> bool {
        let boundary = self.library.as_ref().map_or(0, |l| l.len());
        index < boundary || self.units[index - boundary].is_library
    }

    pub(crate) fn unit_meta(&self, index: usize) -> (&str, &LineIndex) {
        let boundary = self.library.as_ref().map_or(0, |l| l.len());
        if index < boundary {
            self.library.as_ref().unwrap().meta(index)
        } else {
            let unit = &self.units[index - boundary];
            (&unit.name, &unit.lines)
        }
    }

    pub(crate) fn user_units(&self) -> impl Iterator<Item = (usize, &ModelUnit)> {
        let boundary = self.library.as_ref().map_or(0, |l| l.len());
        self.units
            .iter()
            .enumerate()
            .filter(|(_, u)| !u.is_library)
            .map(move |(i, u)| (boundary + i, u))
    }

    pub(crate) fn library_sources(&self) -> Vec<crate::prepared::LibrarySource> {
        let mut sources = self
            .library
            .as_ref()
            .map_or_else(Vec::new, |l| l.sources.clone());
        sources.extend(
            self.units
                .iter()
                .zip(&self.sources)
                .map(|(unit, source)| crate::prepared::LibrarySource::new(unit, source.clone())),
        );
        sources
    }

    /// Keep the outcomes the next build settles on, for
    /// [`Self::settled_outcomes`].
    pub fn keep_settled_outcomes(&mut self) {
        self.settled.get_mut().keep = true;
    }

    /// Start the next build, on a prepared library, from `outcomes`, the
    /// outcomes a previous build settled on (see [`crate::json::settled`]):
    /// a unit lowered to the references it was lowered to then starts from
    /// their outcomes, and is confirmed in one pass when it resolves as it
    /// did; any other unit starts unresolved. The outcomes the build
    /// settles on are kept in turn.
    pub fn start_from_settled(
        &mut self,
        outcomes: std::sync::Arc<crate::json::settled::SettledOutcomes>,
    ) {
        let slot = self.settled.get_mut();
        slot.start = Some(outcomes);
        slot.keep = true;
    }

    /// The outcomes the last build settled on, when kept; `None` when it
    /// did not settle.
    pub fn settled_outcomes(
        &self,
    ) -> Option<std::sync::Arc<crate::json::settled::SettledOutcomes>> {
        self.settled.borrow().kept.clone()
    }

    pub(crate) fn take_settled(
        &self,
    ) -> Option<std::sync::Arc<crate::json::settled::SettledOutcomes>> {
        self.settled.borrow_mut().start.take()
    }

    pub(crate) fn keeps_settled(&self) -> bool {
        self.settled.borrow().keep
    }

    pub(crate) fn deposit_settled(
        &self,
        outcomes: std::sync::Arc<crate::json::settled::SettledOutcomes>,
    ) {
        self.settled.borrow_mut().kept = Some(outcomes);
    }

    /// Replay `cache` on the next build of this model (library units must
    /// match the content the cache was recorded from — key by
    /// [`crate::libcache::hash_library_dir`]).
    pub fn set_library_cache(&mut self, cache: crate::libcache::LibraryCache) {
        self.prepared = None;
        *self.lib_cache.borrow_mut() = LibCacheSlot::Use(std::sync::Arc::new(cache));
    }

    /// Record library resolution outcomes during the next build; collect
    /// them with [`Model::take_recorded_library_cache`].
    pub fn record_library_cache(&mut self) {
        self.prepared = None;
        *self.lib_cache.borrow_mut() = LibCacheSlot::Record;
    }

    /// The outcomes recorded by the first build after
    /// [`Model::record_library_cache`], if any.
    pub fn take_recorded_library_cache(&self) -> Option<crate::libcache::LibraryCache> {
        let mut slot = self.lib_cache.borrow_mut();
        match std::mem::take(&mut *slot) {
            LibCacheSlot::Recorded(c) => Some(c),
            other => {
                *slot = other;
                None
            }
        }
    }

    pub(crate) fn take_lib_cache_for_build(&self) -> LibCacheSlot {
        let mut slot = self.lib_cache.borrow_mut();
        match &*slot {
            // Replay survives repeated builds of the same model (a CLI
            // invocation may build more than once).
            LibCacheSlot::Use(c) => LibCacheSlot::Use(std::sync::Arc::clone(c)),
            LibCacheSlot::Record => std::mem::take(&mut *slot),
            LibCacheSlot::Lazy(source) => match source.load() {
                Some(cache) => {
                    let cache = std::sync::Arc::new(cache);
                    *slot = LibCacheSlot::Use(std::sync::Arc::clone(&cache));
                    LibCacheSlot::Use(cache)
                }
                None => {
                    *slot = LibCacheSlot::Off;
                    LibCacheSlot::Off
                }
            },
            _ => LibCacheSlot::Off,
        }
    }

    /// The resolution recording the last library build replayed or made.
    pub(crate) fn library_recording(
        &self,
    ) -> Option<std::sync::Arc<crate::libcache::LibraryCache>> {
        match &*self.lib_cache.borrow() {
            LibCacheSlot::Use(cache) => Some(std::sync::Arc::clone(cache)),
            LibCacheSlot::Recorded(cache) => Some(std::sync::Arc::new(cache.clone())),
            _ => None,
        }
    }

    /// Keep a recording available for builds that fall back from the
    /// prepared graph, without reading it up front or disabling that graph.
    pub(crate) fn set_lazy_library_cache(&self, path: std::path::PathBuf) {
        *self.lib_cache.borrow_mut() = LibCacheSlot::Lazy(LazyRecording::File(path));
    }

    #[cfg(test)]
    pub(crate) fn lib_cache_kind(&self) -> &'static str {
        match &*self.lib_cache.borrow() {
            LibCacheSlot::Off => "off",
            LibCacheSlot::Use(_) => "use",
            LibCacheSlot::Record => "record",
            LibCacheSlot::Recorded(_) => "recorded",
            LibCacheSlot::Lazy(_) => "lazy",
        }
    }

    pub(crate) fn deposit_recorded(&self, cache: crate::libcache::LibraryCache) {
        *self.lib_cache.borrow_mut() = LibCacheSlot::Recorded(cache);
    }

    /// Snapshot validation failed: flip the slot to Record so the rebuild
    /// records fresh state and the caller's save overwrites the stale file.
    pub(crate) fn rerecord_library_cache(&self) {
        *self.lib_cache.borrow_mut() = LibCacheSlot::Record;
    }

    /// Diagnostics from non-library units.
    pub fn has_errors(&self) -> bool {
        self.units
            .iter()
            .filter(|u| !u.is_library)
            .any(|u| !u.diagnostics.is_empty())
    }
}

/// The model files under `dir` in the deterministic (sorted) order
/// [`Model::load_library_dir`] adds them — index `i` here is library
/// unit `i` of a model loaded from the same directory.
pub fn library_dir_files(dir: &Path) -> io::Result<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();
    collect_model_files(dir, &mut files)?;
    files.sort();
    Ok(files)
}

pub(crate) fn collect_model_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) -> io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_model_files(&path, out)?;
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("sysml" | "kerml")
        ) {
            out.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod dialect_tests {
    use super::Model;
    use sysmlv2_syntax::ast::Dialect;

    #[test]
    fn the_extension_names_the_dialect_without_case() {
        for name in ["m.kerml", "m.KerML", "m.KERML", "dir.sysml/m.kerml"] {
            assert_eq!(Model::dialect_for(name), Dialect::Kerml, "{name}");
        }
        for name in ["m.sysml", "m.SysML", "m", "kerml", "m.kerml.bak"] {
            assert_eq!(Model::dialect_for(name), Dialect::Sysml, "{name}");
        }
    }

    #[test]
    fn a_unit_named_in_upper_case_parses_as_kerml() {
        let mut model = Model::new();
        // `class` is KerML's; a SysML parse of the same text fails.
        let unit = model.add_source("M.KERML", "package P { class A; }");
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    }
}

#[cfg(test)]
mod payload_source_tests {
    use super::*;

    fn model() -> Model {
        let mut m = Model::new();
        m.add_payload_source("input.sysml", "part def P { end part p; }");
        m.add_payload_source("second.sysml", "part def Q { end part p; }");
        assert!(m.payload_source_flags(0).is_some());
        m
    }

    #[test]
    fn payload_origin_refuses_replacement_edit_reinsert_reorder_and_role_changes() {
        let mut m = model();
        let find = |resolved: &crate::json::ResolvedModel| {
            resolved
                .user_elements()
                .find(|&e| {
                    resolved
                        .element_properties(e)
                        .get("declaredName")
                        .and_then(serde_json::Value::as_str)
                        == Some("p")
                })
                .unwrap()
        };
        let initial = crate::json::ResolvedModel::build(&m);
        let (_, path) = initial.payload_owned_flag_anchor(find(&initial)).unwrap();
        let mut flags = crate::properties::Properties::new();
        flags.insert_payload_flag("isConstant", serde_json::json!("original payload"));
        m.retain_payload_flags(
            0,
            path,
            PayloadOwnedFlags {
                metaclass: "PartUsage",
                flags,
            },
        );
        let retained = crate::json::ResolvedModel::build(&m);
        assert_eq!(
            retained.element_properties(find(&retained))["isConstant"],
            serde_json::json!("original payload")
        );
        let mut replacement = Model::new();
        assert!(
            replacement
                .add_source("input.sysml", "part def P { constant end part p; }")
                .diagnostics
                .is_empty()
        );
        m.units[0] = replacement.units.remove(0);
        assert!(m.payload_source_flags(0).is_none());
        let rebuilt = crate::json::ResolvedModel::build(&m);
        assert_eq!(
            rebuilt.element_properties(find(&rebuilt))["isConstant"],
            serde_json::json!(true)
        );
        let mut m = model();
        std::sync::Arc::make_mut(&mut m.units[0].unit)
            .members
            .clear();
        assert!(m.payload_source_flags(0).is_none());
        let mut m = model();
        m.units.remove(0);
        m.add_source("input.sysml", "part def P { end part p; }");
        assert!(m.payload_source_flags(0).is_none());
        assert!(m.payload_source_flags(1).is_none());
        let mut m = model();
        m.units.swap(0, 1);
        assert!(m.payload_source_flags(0).is_none());
        assert!(m.payload_source_flags(1).is_none());
        let mut m = model();
        m.units[0].is_library = true;
        assert!(m.payload_source_flags(0).is_none());
        let mut m = model();
        m.units[0].name = "renamed.sysml".into();
        assert!(m.payload_source_flags(0).is_none());
    }
}
