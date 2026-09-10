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
use sysmlv2_syntax::parser::{parse_kerml_source, parse_source};
use sysmlv2_syntax::span::LineIndex;

/// One parsed file within a model.
pub struct ModelUnit {
    /// Display name (usually the file name); also salts element IDs.
    pub name: String,
    pub unit: SourceUnit,
    pub diagnostics: Vec<Diagnostic>,
    /// Library units provide resolution targets but are not serialized.
    pub is_library: bool,
    /// Line-start index of the source text — line/column reporting for
    /// spans recorded against this unit.
    pub lines: LineIndex,
}

/// A set of parsed source units sharing one global root namespace.
#[derive(Default)]
pub struct Model {
    units: Vec<ModelUnit>,
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
    /// Replay these outcomes on the next build.
    Use(crate::libcache::LibraryCache),
    /// Record outcomes during the next build.
    Record,
    /// Outcomes recorded by a build, awaiting [`Model::take_recorded_library_cache`].
    Recorded(crate::libcache::LibraryCache),
}

impl Model {
    pub fn new() -> Self {
        Model::default()
    }

    fn dialect_for(name: &str) -> Dialect {
        if name.ends_with(".kerml") {
            Dialect::Kerml
        } else {
            Dialect::Sysml
        }
    }

    fn add(&mut self, name: String, src: &str, is_library: bool) -> &ModelUnit {
        let parse = match Self::dialect_for(&name) {
            Dialect::Kerml => parse_kerml_source(src),
            Dialect::Sysml => parse_source(src),
        };
        self.units.push(ModelUnit {
            name,
            unit: parse.unit,
            diagnostics: parse.diagnostics,
            is_library,
            lines: LineIndex::new(src),
        });
        self.units.last().unwrap()
    }

    /// Parse and add a user source. The dialect is chosen by the name's
    /// extension (`.kerml` → KerML, anything else → SysML).
    pub fn add_source(&mut self, name: impl Into<String>, src: &str) -> &ModelUnit {
        self.add(name.into(), src, false)
    }

    /// Parse and add a library source: it participates in name resolution
    /// but its elements are not included in serialized output.
    pub fn add_library_source(&mut self, name: impl Into<String>, src: &str) -> &ModelUnit {
        self.add(name.into(), src, true)
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

    pub fn units(&self) -> &[ModelUnit] {
        &self.units
    }

    /// Replay `cache` on the next build of this model (library units must
    /// match the content the cache was recorded from — key by
    /// [`crate::libcache::hash_library_dir`]).
    pub fn set_library_cache(&mut self, cache: crate::libcache::LibraryCache) {
        *self.lib_cache.borrow_mut() = LibCacheSlot::Use(cache);
    }

    /// Record library resolution outcomes during the next build; collect
    /// them with [`Model::take_recorded_library_cache`].
    pub fn record_library_cache(&mut self) {
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
            LibCacheSlot::Use(c) => LibCacheSlot::Use(c.clone()),
            LibCacheSlot::Record => std::mem::take(&mut *slot),
            _ => LibCacheSlot::Off,
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
