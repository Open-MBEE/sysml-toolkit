//! Prepared-library persistence. The cache is private to one toolkit build;
//! its source text, resolved graph and analysis facts are never interchange.
use crate::{
    json::Builder,
    libcache::MAX_BYTES,
    model::{Model, ModelUnit},
};
use serde::{Deserialize, Deserializer, Serialize};
use std::{io, path::Path, sync::Arc};
use sysmlv2_syntax::ast::QualifiedName;

type Specialization = (usize, &'static str, usize, QualifiedName);

pub(crate) fn specializations<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<crate::layered::LayeredVec<Specialization>, D::Error> {
    Vec::<(usize, String, usize, QualifiedName)>::deserialize(d)?
        .into_iter()
        .map(|(e, n, s, q)| {
            Ok((
                e,
                crate::metaclass::canonical_name(&n)
                    .ok_or_else(|| serde::de::Error::custom("unknown specialization metaclass"))?,
                s,
                q,
            ))
        })
        .collect()
}
pub(crate) fn implied_ends<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<Vec<(&'static str, usize, usize)>, D::Error> {
    Vec::<(String, usize, usize)>::deserialize(d)?
        .into_iter()
        .map(|(n, e, s)| {
            let name = match n.as_str() {
                "source" => "source",
                "target" => "target",
                _ => return Err(serde::de::Error::custom("invalid implicit end")),
            };
            Ok((name, e, s))
        })
        .collect()
}

/// Sources are valid UTF-8 checked by the snapshot decoder. The ordinary,
/// error-tolerant parser recreates the original AST on demand, including spans
/// and recovery nodes. No deferred binary decoding can fail after installation.
#[derive(Serialize, Deserialize)]
pub(crate) struct LibraryUnits {
    pub(crate) sources: Vec<LibrarySource>,
}
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct LibrarySource {
    name: String,
    source: Arc<str>,
    dialect: sysmlv2_syntax::ast::Dialect,
    diagnostics: Vec<sysmlv2_syntax::diag::Diagnostic>,
    is_library: bool,
    lines: sysmlv2_syntax::span::LineIndex,
    #[serde(skip)]
    parsed: Arc<std::sync::OnceLock<ModelUnit>>,
}
impl LibrarySource {
    pub(crate) fn new(unit: &ModelUnit, source: Arc<str>) -> Self {
        Self {
            name: unit.name.clone(),
            source,
            dialect: unit.unit.dialect,
            diagnostics: unit.diagnostics.clone(),
            is_library: unit.is_library,
            lines: unit.lines.clone(),
            parsed: Arc::new(std::sync::OnceLock::from(unit.clone())),
        }
    }
}
impl LibraryUnits {
    pub(crate) fn len(&self) -> usize {
        self.sources.len()
    }
    pub(crate) fn loaded(&self) -> usize {
        self.sources
            .iter()
            .filter(|s| s.parsed.get().is_some())
            .count()
    }
    pub(crate) fn meta(&self, i: usize) -> (&str, &sysmlv2_syntax::span::LineIndex) {
        (&self.sources[i].name, &self.sources[i].lines)
    }
    pub(crate) fn unit(&self, i: usize) -> &ModelUnit {
        let source = &self.sources[i];
        source.parsed.get_or_init(|| {
            use sysmlv2_syntax::{
                ast::Dialect,
                parser::{parse_kerml_source, parse_source},
            };
            let parse = match source.dialect {
                Dialect::Kerml => parse_kerml_source(&source.source),
                Dialect::Sysml => parse_source(&source.source),
            };
            ModelUnit {
                name: source.name.clone(),
                unit: Arc::new(parse.unit),
                diagnostics: source.diagnostics.clone(),
                is_library: source.is_library,
                lines: source.lines.clone(),
            }
        })
    }
}

// 7: scopes carry their implied bases separately from the written ones.
// 8: the integrity trailer is the same fixed hash the resolution cache
// uses, so a snapshot outlives a change of the standard library's
// hasher.
const MAGIC: &[u8] = b"SYSML-PREPARED-8\n";
/// A resolved library with source text and static-analysis facts. Loaded syntax
/// trees are reconstructed on demand. Models share immutable element and scope
/// prefixes; user additions and resolver caches remain private.
#[derive(Serialize)]
pub struct PreparedLibrary {
    pub(crate) units: Arc<LibraryUnits>,
    pub(crate) builder: Builder,
    facts: Arc<crate::check::facts::Facts>,
    pub(crate) root_names: std::collections::HashSet<String>,
}
impl PreparedLibrary {
    /// Original unit names and text in library order, without loading syntax trees.
    pub fn sources(&self) -> impl ExactSizeIterator<Item = (&str, &str)> {
        self.units
            .sources
            .iter()
            .map(|s| (s.name.as_str(), s.source.as_ref()))
    }

    /// A library unit's original name and text, without loading its syntax tree.
    pub fn source(&self, unit: usize) -> Option<(&str, &str)> {
        self.units
            .sources
            .get(unit)
            .map(|s| (s.name.as_str(), s.source.as_ref()))
    }

    /// Prepare a library-only model. User units are refused.
    pub fn build(model: &Model) -> io::Result<Self> {
        if (0..model.unit_count()).any(|i| !model.is_library_unit(i)) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "prepared library contains user units",
            ));
        }
        let mut builder = Builder::default();
        builder.build_model(model);
        let mut resolved = crate::json::ResolvedModel::from_builder(builder, model);
        resolved.prepare_quantity_memo();
        let mut builder = resolved.b;
        let mut facts = builder.prepare_facts();
        facts.freeze();
        let facts = Arc::new(facts);
        builder.library_facts = Some(facts.clone());
        builder.freeze_library();
        Ok(Self {
            units: Arc::new(LibraryUnits {
                sources: model.library_sources(),
            }),
            builder,
            facts,
            root_names: crate::json::top_level_names(model.units().iter()),
        })
    }
    /// Attach this library to an empty model, without parsing or graph lowering.
    pub fn install(self: Arc<Self>, model: &mut Model) -> io::Result<()> {
        model.install_prepared(self)
    }
    /// Decode a content- and build-identified snapshot. Stale, truncated or
    /// corrupt caches are misses and may be rebuilt from source.
    pub fn load(path: &Path, key: u64) -> Option<Self> {
        Self::from_bytes(&crate::libcache::read_capped(path)?, key)
    }
    pub fn from_bytes(bytes: &[u8], key: u64) -> Option<Self> {
        if bytes.len() as u64 > MAX_BYTES {
            return None;
        }
        let bytes = bytes.strip_prefix(MAGIC)?;
        let build = crate::libcache::TOOLKIT_BUILD.as_bytes();
        let bytes = bytes.strip_prefix(build)?.strip_prefix(b"\n")?;
        let saved_key = u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?);
        let sum = u64::from_le_bytes(bytes.get(8..16)?.try_into().ok()?);
        let payload = bytes.get(16..)?;
        if saved_key != key || checksum(payload) != sum {
            return None;
        }
        #[derive(Deserialize)]
        struct Wire {
            units: Arc<LibraryUnits>,
            builder: Builder,
            facts: Arc<crate::check::facts::Facts>,
            root_names: std::collections::HashSet<String>,
        }
        let wire: Wire = crate::cache_codec::decode(payload).ok()?;
        let mut result = Self {
            units: wire.units,
            builder: wire.builder,
            facts: wire.facts,
            root_names: wire.root_names,
        };
        result.builder.reset_lookup_caches();
        if result.units.sources.iter().any(|u| !u.is_library)
            || !result.builder.valid_library(result.units.len())
            || !result.facts.valid(result.builder.elements.len())
        {
            return None;
        }
        Arc::make_mut(&mut result.facts).freeze();
        result.builder.library_facts = Some(result.facts.clone());
        result.builder.freeze_library();
        Some(result)
    }
    pub fn to_bytes(&self, key: u64) -> io::Result<Vec<u8>> {
        let payload = crate::cache_codec::encode(self).map_err(io::Error::other)?;
        let mut out = MAGIC.to_vec();
        out.extend_from_slice(crate::libcache::TOOLKIT_BUILD.as_bytes());
        out.push(b'\n');
        out.extend_from_slice(&key.to_le_bytes());
        out.extend_from_slice(&checksum(&payload).to_le_bytes());
        out.extend_from_slice(&payload);
        if out.len() as u64 > MAX_BYTES {
            return Err(io::Error::other(
                "prepared library exceeds cache size limit",
            ));
        }
        Ok(out)
    }
    pub fn save(&self, path: &Path, key: u64) -> io::Result<()> {
        crate::libcache::write_atomically(path, &self.to_bytes(key)?)
    }
}
fn unsaved_warning(path: &Path, error: &io::Error) -> String {
    format!(
        "could not save the library cache at {}: {error}; every run will prepare the library from source",
        path.display()
    )
}
/// Integrity trailer over a snapshot's payload. Deliberately the fixed,
/// dependency-free hash the resolution cache writes rather than the
/// standard library's default hasher, whose results are documented as
/// free to change between releases: a changed hash would silently
/// invalidate every snapshot on disk, one rebuild at a time, with no
/// version to explain it.
fn checksum(bytes: &[u8]) -> u64 {
    let mut hash = crate::libcache::Fnv::new();
    hash.update(bytes);
    hash.finish()
}

/// What loading a directory library leaves for its caller.
///
/// Non-exhaustive: callers read what they act on, so leaving something
/// further for them is not a breaking change. Build one with
/// [`Default`].
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct LibraryLoad {
    /// Where to save a legacy resolution recording after building the
    /// model, when one is wanted; `None` when the complete snapshot
    /// already covers the library or caching is off.
    pub recording_path: Option<std::path::PathBuf>,
    /// Conditions the caller should report but need not act on. Cache
    /// persistence is an optimization, never a prerequisite, so a cache
    /// that cannot be written is a warning — but a silent one would
    /// repeat the full preparation on every run unexplained. The message
    /// is the caller's to place: an interactive process has standard
    /// error, a language server has its log, a browser has neither.
    pub warnings: Vec<String>,
}

/// Load a directory library with ambient sources. Prepared snapshots serve new
/// models; the resolution-only cache remains available when appending libraries
/// to an existing model. `SYSMLV2_LIB_CACHE=off` disables both paths.
///
/// Complete snapshots are saved during preparation; see [`LibraryLoad`] for
/// what the caller does with the result.
pub fn load_library_with_cache(model: &mut Model, dir: &Path) -> io::Result<LibraryLoad> {
    use crate::{ambient, libcache};
    let enabled = !std::env::var_os("SYSMLV2_LIB_CACHE").is_some_and(|v| v == "off");
    let key = enabled
        .then(|| libcache::hash_library_dir(dir).map(ambient::mix_key))
        .transpose()?;
    let cache = key.and_then(|key| Some((key, libcache::default_cache_path(key)?)));
    load_library_with_cache_at(model, dir, cache)
}

/// [`load_library_with_cache`] with an explicit content key and resolution
/// cache path. The complete snapshot lives beside that path under the
/// `prepared` extension. A prepared model also keeps the resolution recording
/// reachable, unread, for builds that must resolve jointly after all: those
/// replay it instead of resolving the whole library cold. A snapshot miss
/// records that recording while preparing.
pub(crate) fn load_library_with_cache_at(
    model: &mut Model,
    dir: &Path,
    cache: Option<(u64, std::path::PathBuf)>,
) -> io::Result<LibraryLoad> {
    use crate::{ambient, libcache};
    use std::{
        collections::HashMap,
        sync::{Mutex, OnceLock, Weak},
    };
    static SHARED: OnceLock<Mutex<HashMap<u64, Weak<PreparedLibrary>>>> = OnceLock::new();
    let mut warnings = Vec::new();
    if model.unit_count() == 0 {
        if let Some((key, path)) = cache {
            let shared = SHARED.get_or_init(Mutex::default);
            let cached = {
                let mut entries = shared.lock().unwrap_or_else(|e| e.into_inner());
                entries.retain(|_, value| value.strong_count() > 0);
                entries.get(&key).and_then(Weak::upgrade)
            };
            if let Some(library) = cached {
                library.install(model)?;
                model.set_lazy_library_cache(path);
                return Ok(LibraryLoad::default());
            }
            let snapshot = path.with_extension("prepared");
            let library = if let Some(library) = PreparedLibrary::load(&snapshot, key) {
                let library = Arc::new(library);
                library.clone().install(model)?;
                library
            } else {
                model.load_library_dir(dir)?;
                ambient::add_to(model);
                model.record_library_cache();
                let library = model.prepare_library()?;
                if let Some(recording) = model.take_recorded_library_cache() {
                    if let Err(error) = recording.save(&path) {
                        warnings.push(unsaved_warning(&path, &error));
                    }
                }
                if let Err(error) = library.save(&snapshot, key) {
                    warnings.push(unsaved_warning(&snapshot, &error));
                }
                library
            };
            model.set_lazy_library_cache(path);
            shared
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(key, Arc::downgrade(&library));
            return Ok(LibraryLoad {
                recording_path: None,
                warnings,
            });
        }
    }
    model.load_library_dir(dir)?;
    ambient::add_to(model);
    let path = cache.map(|(_, path)| path);
    if let Some(path) = path.as_ref() {
        match libcache::LibraryCache::load(path) {
            Some(cache) => model.set_library_cache(cache),
            None => model.record_library_cache(),
        }
    }
    Ok(LibraryLoad {
        recording_path: path,
        warnings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json::ResolvedModel;
    #[test]
    fn disk_syntax_is_lazy_exact_and_shared_without_changing_unit_indices() {
        let sources = [
            (
                "library.kerml",
                "// note\npackage L { datatype Number; feature n : Number = 2; }",
            ),
            (
                "library.sysml",
                "package K { /* documentation */ attribute x = 3; }",
            ),
        ];
        let mut base = Model::new();
        for (name, source) in sources {
            base.add_library_source(name, source);
        }
        let bytes = base.prepare_library().unwrap().to_bytes(7).unwrap();
        let library = Arc::new(PreparedLibrary::from_bytes(&bytes, 7).unwrap());
        let loaded = || {
            library
                .units
                .sources
                .iter()
                .filter(|s| s.parsed.get().is_some())
                .count()
        };
        let mut model = Model::new();
        library.clone().install(&mut model).unwrap();
        assert_eq!(model.unit_count(), 2);
        model.add_source(
            "user.kerml",
            "package U { feature n : L::Number = L::n + 1; }",
        );
        assert_eq!(model.unit_count(), 3);
        assert_eq!(model.unit(2).name, "user.kerml");
        assert!(!model.is_library_unit(2));
        let mut resolved = ResolvedModel::build(&model);
        crate::check::validate_model_with(&mut resolved, &model);
        crate::check::validate_semantics_with(&mut resolved, &model);
        assert!(resolved.b.library_facts.is_some());
        assert_eq!(
            resolved.evaluate_qualified("U::n").unwrap(),
            crate::eval::Value::Integer(3)
        );
        // Reflection and both user/library graph exports need resolved data,
        // but must not force reconstruction of unused source trees.
        crate::json::model_to_compact_json(&model);
        crate::json::library_to_compact_json(&model);
        assert_eq!(loaded(), 0);
        assert_eq!(*model.unit(1).unit, *base.unit(1).unit);
        assert_eq!(loaded(), 1, "one-file access reconstructs only that file");
        let mut second = Model::new();
        library.clone().install(&mut second).unwrap();
        assert!(Arc::ptr_eq(&model.unit(1).unit, &second.unit(1).unit));
        for (a, b) in model.units()[..2].iter().zip(base.units()) {
            assert_eq!(
                serde_json::to_value(a).unwrap(),
                serde_json::to_value(b).unwrap()
            );
        }
        assert_eq!(loaded(), 2);
        model.add_source("next.kerml", "package Next;");
        assert_eq!(
            model.units().len(),
            4,
            "adding source invalidates the combined view"
        );
        assert_eq!(model.unit(3).name, "next.kerml");
        assert_eq!(second.unit_count(), 2);
        // Snapshot serialization itself must not reconstruct syntax either.
        let fresh = PreparedLibrary::from_bytes(&bytes, 7).unwrap();
        assert!(PreparedLibrary::from_bytes(&fresh.to_bytes(7).unwrap(), 7).is_some());
        assert!(fresh.units.sources.iter().all(|s| s.parsed.get().is_none()));
    }

    #[test]
    fn disk_syntax_reconstructs_for_joint_resolution_and_extra_library_sources() {
        let mut base = Model::new();
        base.add_library_source("l.kerml", "package L { class A :> Later; }");
        let bytes = base.prepare_library().unwrap().to_bytes(1).unwrap();
        let library = Arc::new(PreparedLibrary::from_bytes(&bytes, 1).unwrap());
        let mut model = Model::new();
        library.clone().install(&mut model).unwrap();
        model.add_source("u.kerml", "class Later; package U { feature a : L::A; }");
        assert!(ResolvedModel::build(&model).b.library_facts.is_none());
        assert!(library.units.sources[0].parsed.get().is_some());
        base.add_source("u.kerml", "class Later; package U { feature a : L::A; }");
        assert_eq!(
            crate::json::model_to_compact_json(&model),
            crate::json::model_to_compact_json(&base)
        );
        // Clearing prepared resolution must retain the deferred sources.
        let mut extra = Model::new();
        library.install(&mut extra).unwrap();
        extra.add_library_source("later.kerml", "class Later;");
        assert_eq!(extra.units().len(), 2);
        let recompiled = extra.prepare_library().unwrap();
        let saved = recompiled.to_bytes(2).unwrap();
        assert!(PreparedLibrary::from_bytes(&saved, 2).is_some());
    }

    #[test]
    fn ast_sharing_and_library_semantic_invalidation_are_isolated() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.kerml",
            "package Quantities { datatype MeasurementUnit; } package L { datatype A; datatype B; feature f : A; }",
        );
        let prepared = base.prepare_library().unwrap();
        assert!(prepared.builder.semantic_memo.types.iter().next().is_some());
        let mut model = Model::new();
        prepared.clone().install(&mut model).unwrap();
        assert!(Arc::ptr_eq(&base.units()[0].unit, &model.units()[0].unit));
        // Preparing an already installed snapshot is supported as well.
        model.prepare_library().unwrap();
        let ordinary = ResolvedModel::build(&model);
        assert!(ordinary.b.semantic_memo.types.iter().next().is_some());
        model.add_source("user.kerml", "package U { typing L::f : L::B; }");
        let changed = ResolvedModel::build(&model);
        assert!(
            changed.b.library_facts.is_some(),
            "user package still shares the library graph"
        );
        assert!(
            changed.b.semantic_memo.types.iter().next().is_none(),
            "user typing invalidates derived library semantics"
        );
        assert!(
            prepared.builder.semantic_memo.types.iter().next().is_some(),
            "the shared snapshot remains unchanged"
        );
    }
    #[test]
    fn root_imports_and_named_root_relationships_keep_the_prepared_path() {
        fn same_graphs(library: &[(&str, &str)], user: (&str, &str), prepared_path: bool) {
            let mut base = Model::new();
            for (name, source) in library {
                base.add_library_source(*name, source);
            }
            let prepared = base.prepare_library().unwrap();
            let mut cold = Model::new();
            for (name, source) in library {
                cold.add_library_source(*name, source);
            }
            cold.add_source(user.0, user.1);
            let mut warm = Model::new();
            prepared.install(&mut warm).unwrap();
            warm.add_source(user.0, user.1);
            let r = ResolvedModel::build(&warm);
            assert_eq!(r.b.library_facts.is_some(), prepared_path, "{}", user.1);
            assert_eq!(
                crate::json::model_to_compact_json(&cold),
                crate::json::model_to_compact_json(&warm),
                "{}",
                user.1
            );
            assert_eq!(
                crate::json::library_to_compact_json(&cold),
                crate::json::library_to_compact_json(&warm),
                "{}",
                user.1
            );
        }
        // Only names this library looked up at root and missed can complete
        // it: here the implicit-base and quantity probes. Root imports,
        // inferred root names and named root relationships that add other
        // names keep the prepared graph.
        let complete = [("lib.sysml", "package L { part def A; part def B :> A; }")];
        let mut base = Model::new();
        base.add_library_source(complete[0].0, complete[0].1);
        let misses = base.prepare_library().unwrap().builder.root_misses.clone();
        assert!(misses.contains("Parts"), "{misses:?}");
        assert!(!misses.contains("A") && !misses.contains("B"), "{misses:?}");
        for source in [
            "private import L::*; package U { part a : A; part b : B; }",
            "import L::*; package U { part a : A; }",
            "package U { part a : L::A; } dependency D from U to L;",
            "package U { part b : L::B; } private import U::*; part x : b;",
            "package Q { part def Y; part def Parts; } private import Q::Y; package U { part a : L::A; }",
            "package Q { part def Y { part def Parts; } } private import Q::*; package U { part a : L::A; }",
        ] {
            same_graphs(&complete, ("user.sysml", source), true);
        }
        for source in [
            // A user namespace re-exporting through its own import, an
            // alias target, and a recursive import reaching a probed name.
            "package Q { public import L::*; } private import Q::*; package U { part a : A; }",
            "alias Q for L; private import Q::*; package U { part a : A; }",
            "package Q { part def Y { part def Parts; } } private import Q::**; package U { part a : L::A; }",
            "package Q { part def Parts; } private import Q::*; package U { part a : L::A; }",
        ] {
            same_graphs(&complete, ("user.sysml", source), false);
        }
        same_graphs(
            &[("lib.kerml", "package L { class A; }")],
            (
                "user.kerml",
                "package P { feature x : L::A; } feature :>> P::x;",
            ),
            true,
        );
        // A root filter can constrain library root imports: joint resolution.
        same_graphs(
            &complete,
            ("user.sysml", "package U { part a : L::A; } filter true;"),
            false,
        );
        // A library with an unresolved root name can be completed through a
        // root import, an inferred root name, or a matching declaration.
        let incomplete = [(
            "lib.sysml",
            "package Other { part def X; } package L { part def A :> X; }",
        )];
        let mut base = Model::new();
        base.add_library_source(incomplete[0].0, incomplete[0].1);
        assert!(
            base.prepare_library()
                .unwrap()
                .builder
                .root_misses
                .contains("X")
        );
        for source in [
            "private import Other::*; package U { part a : L::A; }",
            "package U { part a : L::A; part def X; } private import U::*;",
            "part def X; package U { part a : L::A; }",
            "package U { part a : L::A; } dependency X from U to L;",
        ] {
            same_graphs(&incomplete, ("user.sysml", source), false);
        }
        same_graphs(
            &[("lib.kerml", "package L { feature f :> x; }")],
            ("user.kerml", "package P { feature x; } feature :>> P::x;"),
            false,
        );
    }
    /// A cache that cannot be written is handed back to the caller
    /// rather than printed: the library runs inside hosts with no
    /// standard error to print to, and the load itself still succeeds —
    /// the cache is an optimization, never a prerequisite.
    #[test]
    fn an_unwritable_cache_is_reported_to_the_caller() {
        let root = std::env::temp_dir().join(format!(
            "sysml-prepared-unwritable-{}",
            uuid::Uuid::new_v4()
        ));
        let dir = root.join("library");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("Lib.sysml"), "package L { part def A; }").unwrap();
        // The cache directory's place is taken by a file, so neither the
        // recording nor the snapshot can be created there.
        let blocked = root.join("cache");
        std::fs::write(&blocked, b"not a directory").unwrap();

        let mut model = Model::new();
        let load = load_library_with_cache_at(
            &mut model,
            &dir,
            Some((7, blocked.join("stdlib.libcache"))),
        )
        .unwrap();
        assert!(model.unit_count() > 0, "the library still loaded");
        assert_eq!(load.warnings.len(), 2, "{:?}", load.warnings);
        for warning in &load.warnings {
            assert!(
                warning.contains("could not save the library cache at"),
                "{warning}"
            );
        }
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn fallback_builds_replay_the_recorded_resolution_cache() {
        let root =
            std::env::temp_dir().join(format!("sysml-prepared-replay-{}", uuid::Uuid::new_v4()));
        let dir = root.join("library");
        std::fs::create_dir_all(&dir).unwrap();
        let library = "package Other { part def X; } package L { part def A :> X; }";
        std::fs::write(dir.join("Lib.sysml"), library).unwrap();
        let recording = root.join("cache").join("stdlib.libcache");
        let cache = || Some((5, recording.clone()));
        let mut cold = Model::new();
        let load = load_library_with_cache_at(&mut cold, &dir, cache()).unwrap();
        assert!(load.recording_path.is_none());
        assert!(
            load.warnings.is_empty(),
            "a writable cache directory produces no warning: {:?}",
            load.warnings
        );
        assert!(
            recording.exists(),
            "a snapshot miss records the resolution cache"
        );
        assert!(recording.with_extension("prepared").exists());
        assert_eq!(cold.lib_cache_kind(), "lazy");
        drop(cold);
        let mut warm = Model::new();
        load_library_with_cache_at(&mut warm, &dir, cache()).unwrap();
        assert_eq!(warm.loaded_library_unit_count(), 0);
        assert_eq!(warm.lib_cache_kind(), "lazy");
        // Completing the missed root name forces joint resolution.
        let user = "private import Other::*; package U { part a : L::A; }";
        warm.add_source("user.sysml", user);
        let resolved = ResolvedModel::build(&warm);
        assert!(resolved.b.library_facts.is_none());
        assert_eq!(
            warm.lib_cache_kind(),
            "use",
            "the fallback replays the recording"
        );
        let mut plain = Model::new();
        plain.add_library_source("Lib.sysml", library);
        crate::ambient::add_to(&mut plain);
        plain.add_source("user.sysml", user);
        assert_eq!(
            crate::json::model_to_compact_json(&plain),
            crate::json::model_to_compact_json(&warm)
        );
        assert_eq!(
            crate::json::library_to_compact_json(&plain),
            crate::json::library_to_compact_json(&warm)
        );
        // A prepared build never reads the recording.
        let mut fast = Model::new();
        load_library_with_cache_at(&mut fast, &dir, cache()).unwrap();
        fast.add_source("user.sysml", "package U { part a : L::A; }");
        assert!(ResolvedModel::build(&fast).b.library_facts.is_some());
        assert_eq!(fast.lib_cache_kind(), "lazy");
        // A stale recording is ignored rather than trusted.
        std::fs::write(&recording, b"damaged").unwrap();
        let mut stale = Model::new();
        load_library_with_cache_at(&mut stale, &dir, cache()).unwrap();
        stale.add_source("user.sysml", user);
        assert_eq!(
            crate::json::model_to_compact_json(&plain),
            crate::json::model_to_compact_json(&stale)
        );
        assert_eq!(stale.lib_cache_kind(), "off");
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn prepared_builds_use_shared_prefixes_and_fall_back_for_root_dependencies() {
        let mut base = Model::new();
        base.add_library_source("lib.kerml", "package L { class A; }");
        let prepared = base.prepare_library().unwrap();
        let mut model = Model::new();
        prepared.clone().install(&mut model).unwrap();
        model.add_source("user.kerml", "package U { feature a : L::A; }");
        let r = ResolvedModel::build(&model);
        assert!(
            r.b.library_facts.is_some(),
            "ordinary models must take the prepared path"
        );
        assert!(r.b.elements.shares_prefix(&prepared.builder.elements));
        let mut collision = Model::new();
        prepared.install(&mut collision).unwrap();
        collision.add_source("user.kerml", "package L { class A; }");
        assert!(ResolvedModel::build(&collision).b.library_facts.is_none());
        let mut base = Model::new();
        base.add_library_source("lib.kerml", "package L { class A :> Later; }");
        let prepared = base.prepare_library().unwrap();
        let mut model = Model::new();
        prepared.install(&mut model).unwrap();
        model.add_source("user.kerml", "class Later;");
        assert!(ResolvedModel::build(&model).b.library_facts.is_none());
    }
}
