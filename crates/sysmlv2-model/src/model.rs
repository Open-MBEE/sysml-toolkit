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

/// A set of parsed source units sharing one global root namespace.
#[derive(Default)]
pub struct Model {
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
    /// A recording on disk, read only if a build cannot reuse the prepared
    /// graph. Prepared builds never pay for loading it.
    Lazy(std::path::PathBuf),
}

impl Model {
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
        self.library = Some(library.units.clone());
        self.prepared = Some(library);
        Ok(())
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
            LibCacheSlot::Lazy(path) => match crate::libcache::LibraryCache::load(path) {
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

    /// Keep a recording available for builds that fall back from the
    /// prepared graph, without reading it up front or disabling that graph.
    pub(crate) fn set_lazy_library_cache(&self, path: std::path::PathBuf) {
        *self.lib_cache.borrow_mut() = LibCacheSlot::Lazy(path);
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
