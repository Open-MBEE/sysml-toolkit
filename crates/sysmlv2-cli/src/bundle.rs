//! Library bundles: a standard library given as one JSON file of
//! `[{name, text}]` units, the shape the wasm package ships, instead of a
//! directory. The units load in array order under their bundle names, as
//! the wasm binding takes a bundle, and the library is keyed by their
//! content, as the binding keys it: the prepared snapshot generated with
//! the bundle (`sysml-library.json` → `sysml-library.prepared`, beside
//! it) serves the run, so a host that already holds the two files never
//! prepares the library from source.
//!
//! A bundle is loaded exactly as it is: it carries the ambient libraries
//! when it was generated with them, and none are added to it, so
//! `SYSMLV2_AMBIENT` does not change what a bundle loads.

use std::io;
use std::path::Path;
use std::sync::{Arc, Mutex};

use sysmlv2_parser::libcache;
use sysmlv2_parser::model::{GraphFormat, Model};
use sysmlv2_parser::prepared::PreparedLibrary;

/// A bundle's library as a run takes it.
pub(crate) enum Bundle {
    /// The library prepared: decoded from a snapshot that fits the
    /// bundle, or prepared from its units and saved to the cache.
    Prepared(Arc<PreparedLibrary>),
    /// The units as they are, built with the model: library caching is
    /// off, or no snapshot fits and there is no cache to prepare into.
    Sources(Vec<(String, String)>),
}

/// What loading a bundle leaves for its caller: the library, and the
/// conditions to report but not act on (a cache that could not be
/// written, or none to write).
pub(crate) struct BundleLoad {
    pub(crate) bundle: Bundle,
    pub(crate) warnings: Vec<String>,
}

/// Whether `--lib` names a bundle rather than a library directory: any
/// file is read as one.
pub(crate) fn is_bundle(path: &Path) -> bool {
    path.is_file()
}

/// Load the bundle at `path` for a model of `format`. The library is
/// read from the first of these whose snapshot fits — made by this
/// toolkit build, for `format`, from exactly the bundle's units in its
/// order — and prepared from the units otherwise:
///
/// 1. the cache's own snapshot of the bundle, `stdlib-<key>.prepared`
///    under the cache directory;
/// 2. the snapshot beside the bundle, `<stem>.prepared`, read in place;
/// 3. none: the library is prepared from the units and its snapshot and
///    resolution recording are written to the cache, for the next run.
///
/// A resolution recording beside the snapshot that served (`<stem>.libcache`,
/// or the cache's `stdlib-<key>.libcache`) is kept with the library, for
/// the builds that must resolve the library together with the model.
/// `SYSMLV2_LIB_CACHE=off` reads and writes no snapshot.
pub(crate) fn load(path: &Path, format: GraphFormat) -> io::Result<BundleLoad> {
    let units = read_units(path)?;
    let mut warnings = Vec::new();
    if std::env::var_os("SYSMLV2_LIB_CACHE").is_some_and(|v| v == "off") {
        return Ok(BundleLoad {
            bundle: Bundle::Sources(units),
            warnings,
        });
    }
    let key = libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
    if let Some(library) = held(key, format) {
        return Ok(BundleLoad {
            bundle: Bundle::Prepared(library),
            warnings,
        });
    }
    // The cache names a library's recording; its snapshot is the
    // `prepared` sibling, as for a directory library.
    let cache = libcache::default_cache_path(key).map(|recording| match format {
        GraphFormat::LegacyV2 => recording,
        _ => recording.with_extension("v3.cache"),
    });
    let fits = |library: &PreparedLibrary| library.graph_format() == format;
    let own = cache.as_ref().and_then(|recording| {
        let library =
            PreparedLibrary::load_cache(&recording.with_extension("prepared"), key).filter(fits)?;
        Some((library, recording.clone()))
    });
    let found = own.or_else(|| {
        let library = PreparedLibrary::load(&path.with_extension("prepared"), key).filter(fits)?;
        Some((library, path.with_extension("libcache")))
    });
    let library = match (found, cache) {
        (Some((library, recording)), _) => {
            let library = match std::fs::read(&recording) {
                Ok(bytes) => library.with_lazy_recording(bytes),
                Err(_) => library,
            };
            let library = Arc::new(library);
            // The plans a build asks for first are read back on a thread
            // while the model is lowered and resolved.
            library.start_plans();
            library
        }
        (None, Some(recording)) => prepare(&units, key, format, &recording, &mut warnings)?,
        (None, None) => {
            warnings.push(
                "no cache directory for the standard library: none of SYSMLV2_CACHE_DIR, \
                 XDG_CACHE_HOME or HOME is set (on Windows, LOCALAPPDATA or USERPROFILE), and \
                 no snapshot beside the bundle fits it, so the library is prepared from source \
                 on every run"
                    .to_string(),
            );
            return Ok(BundleLoad {
                bundle: Bundle::Sources(units),
                warnings,
            });
        }
    };
    hold(key, format, &library);
    Ok(BundleLoad {
        bundle: Bundle::Prepared(library),
        warnings,
    })
}

/// The bundle's units, in array order. Each is an object with a string
/// `name` and `text`; an empty name is refused, as the binding refuses
/// it, since a unit's name is its identity downstream. A file that is not
/// JSON is said to be neither a library directory nor a bundle.
fn read_units(path: &Path) -> io::Result<Vec<(String, String)>> {
    let invalid = |why: String| io::Error::new(io::ErrorKind::InvalidData, why);
    let units: Vec<serde_json::Value> = {
        let bytes = std::fs::read(path)?;
        serde_json::from_slice(&bytes).map_err(|e| {
            invalid(format!(
                "--lib takes a library directory or a bundle file, JSON [{{name, text}}]: {e}"
            ))
        })?
    };
    // The texts are moved out of the parsed document, not copied: the
    // file's bytes are gone by now, so the units are held once.
    units
        .into_iter()
        .enumerate()
        .map(|(i, unit)| {
            let mut unit = match unit {
                serde_json::Value::Object(unit) => unit,
                _ => serde_json::Map::new(),
            };
            let mut field = |key: &str| match unit.remove(key) {
                Some(serde_json::Value::String(value)) => Some(value),
                _ => None,
            };
            match (field("name"), field("text")) {
                (Some(name), _) if name.is_empty() => Err(invalid(format!(
                    "a library bundle is JSON [{{name, text}}]: unit {i} has an empty name"
                ))),
                (Some(name), Some(text)) => Ok((name, text)),
                _ => Err(invalid(format!(
                    "a library bundle is JSON [{{name, text}}]: unit {i} has no string name \
                     and text"
                ))),
            }
        })
        .collect()
}

/// Prepare the bundle's units as one library, as a directory library is
/// prepared on a cold run, and write its snapshot (under `key`) and its
/// resolution recording to the cache, named by `recording`. A cache that
/// cannot be written is a warning: the run goes on with the library.
fn prepare(
    units: &[(String, String)],
    key: u64,
    format: GraphFormat,
    recording: &Path,
    warnings: &mut Vec<String>,
) -> io::Result<Arc<PreparedLibrary>> {
    let mut model = Model::with_graph_format(format);
    for (name, text) in units {
        model.add_library_source(name.clone(), text);
    }
    model.record_library_cache();
    let library = model.prepare_library()?;
    // The plans are made now, so the snapshot carries them and no later
    // run plans the library again.
    library.make_plans();
    let snapshot = recording.with_extension("prepared");
    let unsaved = |path: &Path, error: io::Error| {
        format!(
            "could not save the library cache at {}: {error}; every run will prepare the \
             library from source",
            path.display()
        )
    };
    if let Some(recorded) = model.take_recorded_library_cache() {
        if let Err(error) = recorded.save(recording) {
            warnings.push(unsaved(recording, error));
        }
    }
    if let Err(error) = library.save(&snapshot, key) {
        warnings.push(unsaved(&snapshot, error));
    }
    Ok(library)
}

/// The bundle library this process loaded last, by key and graph format,
/// kept after the model that loaded it is gone: a verb that loads the
/// library twice (to name library ids, then to build the model) decodes it
/// once. Directory libraries are kept the same way by the loader;
/// `SYSMLV2_LIB_RETAIN=off` keeps neither.
type Held = Mutex<Option<(u64, GraphFormat, Arc<PreparedLibrary>)>>;
static HELD: Held = Mutex::new(None);

fn held(key: u64, format: GraphFormat) -> Option<Arc<PreparedLibrary>> {
    let held = HELD.lock().unwrap_or_else(|e| e.into_inner());
    match &*held {
        Some((k, f, library)) if *k == key && *f == format => Some(Arc::clone(library)),
        _ => None,
    }
}

fn hold(key: u64, format: GraphFormat, library: &Arc<PreparedLibrary>) {
    let kept = !std::env::var_os("SYSMLV2_LIB_RETAIN").is_some_and(|v| v == "off" || v == "0");
    *HELD.lock().unwrap_or_else(|e| e.into_inner()) =
        kept.then(|| (key, format, Arc::clone(library)));
}
