//! Prepared-library persistence. The cache is private to one toolkit build;
//! its source text, resolved graph and analysis facts are never interchange.
use crate::{
    json::Builder,
    libcache::MAX_BYTES,
    model::{Model, ModelUnit},
};
use serde::{Deserialize, Deserializer, Serialize};
use std::{io, path::Path, sync::Arc};
use sysmlv2_syntax::ast::{QualifiedName, UsageKind};

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
/// A scope's recorded implied end names, admitted only when
/// [`crate::json::binary_end_names`] knows them (one usage kind per row of
/// that table stands for the kinds sharing the row), so a snapshot holds
/// the `&'static str` the builder would have registered.
pub(crate) fn implied_ends<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<Vec<(&'static str, usize, usize)>, D::Error> {
    Vec::<(String, usize, usize)>::deserialize(d)?
        .into_iter()
        .map(|(n, e, s)| {
            let name = [
                UsageKind::Connection,
                UsageKind::Succession,
                UsageKind::Binding,
            ]
            .into_iter()
            .filter_map(crate::json::binary_end_names)
            .flatten()
            .find(|&name| name == n)
            .ok_or_else(|| serde::de::Error::custom("invalid implicit end"))?;
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
// 9: aliases retain their Membership relationship and lookup outcomes carry
// the selected alias Membership through re-exports.
// 10: preserve nonconvergent recorded-lookup qualification.
// 12: calculations no longer keep their declared input names apart.
// 13: scopes carry the spellings of every redefinition their owner writes.
// 14: retain those complete QualifiedNames, including qualification and source spans.
// 15: memoized unit expansions carry the features they read.
// 19: the tables are columns; the frozen rows' kept lookup graph is carried.
// 20: the records are parts — each with its length and checksum in the
// header — so that a reader decodes them side by side.
// 21: a last part carries what hosts derive from the library and ship
// with it (see [`PreparedLibrary::carry_host_part`]).
const MAGIC: &[u8] = b"SYSML-PREPARED-21\n";

/// The parts a snapshot's payload is written as — the string table, then
/// the records of [`Wire`] in order, with the builder's element rows and
/// scope rows as parts of their own right after its record — each with
/// its length and checksum in the header. The three builder parts are
/// most of the payload; apart, they decode side by side.
const PARTS: usize = 11;
/// The two parts a load reads apart from the load itself (see [`Snapshot`]):
/// the facts, which only the checks read, and the plans, which only a
/// build that plans reads.
const FACTS_PART: usize = 5;
const PLANS_PART: usize = 7;
/// The part carrying the hosts' parts (see [`HostParts`]).
const HOSTS_PART: usize = 10;

/// What hosts derive from a library and ship in its snapshot beside the
/// library's own records (see [`PreparedLibrary::carry_host_part`]): each
/// host's value encoded on its own — its own string table, then its bytes —
/// under the tag the host names, so that the library's decode leaves it as
/// it is and the host decodes it when it first needs it. A decode keeps the
/// part only when asked to (see [`PreparedLibrary::from_bytes_with`]):
/// otherwise it verifies the part and lets it go. Written in tag
/// order, each value as a run of chunks no longer than [`HOST_CHUNK`], so
/// that a snapshot fed in chunks never widens its window to a value's
/// length.
#[derive(Default)]
struct HostParts(std::collections::BTreeMap<String, Vec<u8>>);

/// The longest run of a host's bytes a snapshot writes as one item.
const HOST_CHUNK: usize = 32 * 1024;

impl Serialize for HostParts {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        /// One run of bytes, written as bytes.
        struct Run<'a>(&'a [u8]);
        impl Serialize for Run<'_> {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_bytes(self.0)
            }
        }
        /// A value's bytes, as its runs.
        struct Runs<'a>(&'a [u8]);
        impl Serialize for Runs<'_> {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.collect_seq(self.0.chunks(HOST_CHUNK).map(Run))
            }
        }
        s.collect_seq(self.0.iter().map(|(tag, bytes)| (tag, Runs(bytes))))
    }
}

impl<'de> Deserialize<'de> for HostParts {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let parts = Vec::<(String, Joined)>::deserialize(d)?;
        Ok(Self(
            parts
                .into_iter()
                .map(|(tag, bytes)| (tag, bytes.0))
                .collect(),
        ))
    }
}

/// A host's bytes, joined from the runs a snapshot writes them as (see
/// [`HostParts`]).
struct Joined(Vec<u8>);

impl<'de> Deserialize<'de> for Joined {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(JoinedVisitor)
    }
}

struct JoinedVisitor;

impl<'de> serde::de::Visitor<'de> for JoinedVisitor {
    type Value = Joined;
    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("a host's bytes")
    }
    fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut seq: A) -> Result<Joined, A::Error> {
        // Room for the runs the part says it holds, so the value is not
        // copied as it grows; no more than a few megabytes up front, which
        // a corrupt count cannot then make a large allocation of.
        let runs = seq.size_hint().unwrap_or(0).min(256);
        let mut bytes = Vec::with_capacity(runs * HOST_CHUNK);
        while seq.next_element_seed(Append(&mut bytes))?.is_some() {}
        Ok(Joined(bytes))
    }
}

/// A run of a host's bytes, appended to those read before it.
struct Append<'a>(&'a mut Vec<u8>);

impl<'de> serde::de::DeserializeSeed<'de> for Append<'_> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_bytes(self)
    }
}

impl<'de> serde::de::Visitor<'de> for Append<'_> {
    type Value = ();
    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("a run of a host's bytes")
    }
    fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<(), E> {
        self.0.extend_from_slice(v);
        Ok(())
    }
}

/// A part's extent and checksum, as the header carries them.
#[derive(Clone, Copy)]
struct Part {
    len: usize,
    sum: u64,
}

/// The records a snapshot carries, in order.
struct Wire {
    units: Arc<LibraryUnits>,
    builder: Builder,
    facts: FactsWire,
    root_names: std::collections::HashSet<String>,
    /// The library's own plans, when the writer had made them.
    plans: Carried,
    /// The frozen rows' structural scan and its projections.
    prefix: Option<crate::json::PrefixWire>,
    /// The frozen rows' kept lookup graph.
    lookup: Option<crate::json::GraphWire>,
    /// What hosts derive from the library and ship with it.
    hosts: HostParts,
}
/// A resolved library with source text and static-analysis facts. Loaded syntax
/// trees are reconstructed on demand. Models share immutable element and scope
/// prefixes; user additions and resolver caches remain private.
pub struct PreparedLibrary {
    pub(crate) units: Arc<LibraryUnits>,
    pub(crate) builder: Builder,
    facts: Arc<LibraryFacts>,
    pub(crate) root_names: std::collections::HashSet<String>,
    /// The resolution recording the library was prepared with, replayed by
    /// builds that must resolve the library together with user units. Kept
    /// in memory only; a decoded snapshot has none.
    pub(crate) recording: Option<Arc<crate::libcache::LibraryCache>>,
    /// The encoded recording a decoded handle keeps for joint builds, which
    /// decode it on first need; installing arms the model's lazy slot with it.
    pub(crate) lazy_recording: Option<Arc<[u8]>>,
    /// The implied-specialization and positional plans of the library's own
    /// rows, for every build on it to extend with its own rows (see
    /// [`Self::library_plans`]).
    plans: Plans,
    /// The library's enumeration and variation definitions, made on first
    /// read (see [`crate::json::ResolvedModel::enum_types`]).
    enum_types: std::sync::OnceLock<crate::json::LibraryEnumTypes>,
    /// The owner of each of the library's relationships and its
    /// specialization rows by owner, made on first read: a build that left
    /// the library's rows as they are tables only its own over them.
    rel_owners: std::sync::OnceLock<Arc<Vec<Option<usize>>>>,
    spec_index: std::sync::OnceLock<Arc<crate::layered::IdMap<usize, Vec<usize>>>>,
    /// Each of the library's rows' declared name and short name, hashed as
    /// the inherited-member reducer groups rows by name (see
    /// [`crate::json::name_keys_of`]), made on first read: a build on the
    /// library hashes only its own rows.
    name_keys: std::sync::OnceLock<Arc<Vec<[u64; 2]>>>,
    /// The library's multiplicities whose bounds are expressions, with
    /// the features and scopes holding them (see
    /// [`crate::check::multiplicity_domains::ExpressionBounds`]), made on
    /// first read.
    expression_bounds:
        std::sync::OnceLock<Arc<crate::check::multiplicity_domains::ExpressionBounds>>,
    /// The library's valued chain redefinitions by owning type (see
    /// [`crate::json::Builder::chain_redefinitions`]), made on first read.
    chain_redefinitions: std::sync::OnceLock<ChainIndex>,
    /// The library's multiplicity rows by the element whose own
    /// multiplicity each declares, and by the range each constrains.
    declared_multiplicities: std::sync::OnceLock<RowIndex>,
    multiplicity_ranges: std::sync::OnceLock<RowIndex>,
    /// What hosts derive from the library and keep with it, one value per
    /// type (see [`Self::derived`]).
    derived: std::sync::Mutex<Vec<Arc<dyn std::any::Any + Send + Sync>>>,
    /// What hosts derive from the library and ship in its snapshot, encoded,
    /// by tag (see [`Self::carry_host_part`]).
    hosts: std::sync::Mutex<HostParts>,
}

/// Rows of a library table by element.
type RowIndex = Arc<crate::layered::IdMap<usize, usize>>;

/// Valued chain redefinitions by owning type: (redefining feature, links).
pub(crate) type ChainIndex = Arc<crate::layered::IdMap<usize, Vec<(usize, Vec<usize>)>>>;
impl PreparedLibrary {
    /// The value of type `T` derived from this library: made by `make` the
    /// first time anything holding the library asks for one, and kept with
    /// the library after, so that a host deriving a table of its own from
    /// the library (a language server's symbol table) makes it once per
    /// library rather than once per server. `make` runs without a lock
    /// held; two threads asking at once may both make the value, and the
    /// first one kept is the one both get.
    ///
    /// The value is found by its type alone: name a type private to the
    /// crate asking, so that no other caller's value of the same type is
    /// taken for it.
    #[doc(hidden)]
    pub fn derived<T: std::any::Any + Send + Sync>(&self, make: impl FnOnce() -> T) -> Arc<T> {
        let kept = |slot: &[Arc<dyn std::any::Any + Send + Sync>]| {
            slot.iter()
                .find_map(|value| Arc::clone(value).downcast::<T>().ok())
        };
        let lock = || {
            self.derived
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
        };
        if let Some(value) = kept(&lock()) {
            return value;
        }
        let made = Arc::new(make());
        let mut slot = lock();
        if let Some(value) = kept(&slot) {
            return value;
        }
        slot.push(Arc::clone(&made) as Arc<dyn std::any::Any + Send + Sync>);
        made
    }

    /// Ship `value` in the snapshots written from this handle, under `tag`:
    /// a table a host derives from the library — a language server's symbol
    /// table — which a host decoding the snapshot with its hosts' parts kept
    /// ([`Self::from_bytes_with`], [`Self::from_chunks_with`],
    /// [`Self::load_with`]) then reads back with [`Self::take_host_part`]
    /// instead of deriving it again. A value
    /// carried under the tag already is replaced. The value is encoded here,
    /// on its own, with the snapshot's codec: like the rest of the snapshot it
    /// is private to one toolkit build, and a host whose value depends on
    /// more than the library and this build stamps it with what else.
    #[doc(hidden)]
    pub fn carry_host_part<T: Serialize>(&self, tag: &str, value: &T) -> io::Result<()> {
        let bytes = crate::cache_codec::encode(value).map_err(io::Error::other)?;
        self.hosts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .0
            .insert(tag.to_string(), bytes);
        Ok(())
    }

    /// The value the snapshot carried under `tag` (see
    /// [`Self::carry_host_part`]), decoded, and its bytes released: a second
    /// call answers `None`, as does a tag the snapshot did not carry, a
    /// handle decoded without keeping its hosts' parts, or a value that does
    /// not decode as a `T`. The host keeps what it read (see
    /// [`Self::derived`]); a snapshot written from this handle afterwards no
    /// longer carries it.
    #[doc(hidden)]
    pub fn take_host_part<T: serde::de::DeserializeOwned>(&self, tag: &str) -> Option<T> {
        let bytes = self
            .hosts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .0
            .remove(tag)?;
        crate::cache_codec::decode(&bytes).ok()
    }

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

    /// Authored graph contract captured by this prepared library.
    pub fn graph_format(&self) -> crate::model::GraphFormat {
        self.builder.graph_format
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
        // Keep logical semantic readiness for warming, but never freeze a
        // published semantic suffix into the source-only prepared prefix.
        resolved.b.suppress_semantic_publication();
        resolved.prepare_quantity_memo();
        // The library's own implied relationships and owned results, made
        // once here and kept as the last rows of the prefix, so that no
        // build on the library makes them again.
        resolved.materialize_prefix_semantics();
        let mut builder = resolved.b;
        let mut facts = builder.prepare_facts();
        facts.freeze();
        let facts = Arc::new(LibraryFacts::made(Arc::new(facts)));
        builder.library_facts = Some(Arc::clone(&facts));
        builder.freeze_library();
        Ok(Self {
            units: Arc::new(LibraryUnits {
                sources: model.library_sources(),
            }),
            builder,
            facts,
            root_names: crate::json::top_level_names(model.units().iter()),
            recording: model.library_recording(),
            lazy_recording: None,
            plans: Plans::default(),
            enum_types: std::sync::OnceLock::new(),
            rel_owners: std::sync::OnceLock::new(),
            spec_index: std::sync::OnceLock::new(),
            name_keys: std::sync::OnceLock::new(),
            expression_bounds: std::sync::OnceLock::new(),
            chain_redefinitions: std::sync::OnceLock::new(),
            declared_multiplicities: std::sync::OnceLock::new(),
            multiplicity_ranges: std::sync::OnceLock::new(),
            derived: std::sync::Mutex::default(),
            hosts: std::sync::Mutex::default(),
        })
    }

    /// The library's enumeration and variation definitions, made on first call.
    pub(crate) fn library_enum_types(&self) -> &crate::json::LibraryEnumTypes {
        self.enum_types
            .get_or_init(|| crate::json::LibraryEnumTypes::of(&self.builder))
    }

    /// The owning element of each of the library's relationships, made on
    /// first call.
    pub(crate) fn library_rel_owners(&self) -> &Arc<Vec<Option<usize>>> {
        self.rel_owners.get_or_init(|| {
            self.assert_frozen_rows();
            Arc::new(crate::json::relationship_owners(&self.builder))
        })
    }

    /// The name keys of each of the library's rows, made on first call.
    pub(crate) fn library_name_keys(&self) -> &Arc<Vec<[u64; 2]>> {
        self.name_keys.get_or_init(|| {
            self.assert_frozen_rows();
            Arc::new(crate::json::name_keys_of(&self.builder))
        })
    }

    /// The library's rows are its frozen base, unwritten and with nothing
    /// appended: the tables made over them are read by index under a
    /// build's own rows, so they must describe the base a build lays its
    /// rows over, row for row.
    fn assert_frozen_rows(&self) {
        debug_assert!(
            self.builder.elements.base_untouched()
                && self.builder.elements.base_len() == self.builder.elements.len(),
            "a prepared library's rows are its frozen base"
        );
    }

    /// The library's frozen specialization rows by owner (see
    /// [`crate::json::Builder::spec_index`]), made on first call.
    pub(crate) fn library_spec_index(&self) -> &Arc<crate::layered::IdMap<usize, Vec<usize>>> {
        self.spec_index.get_or_init(|| {
            let mut index = crate::layered::LayeredMap::default();
            self.builder
                .index_spec_rows(0..self.builder.spec_targets.base_len(), &mut index);
            index.freeze();
            Arc::clone(index.base_arc())
        })
    }

    /// The library's valued chain redefinitions by owning type, made on
    /// first call, on a copy of the library's build.
    pub(crate) fn library_chain_redefinitions(&self) -> &ChainIndex {
        self.chain_redefinitions.get_or_init(|| {
            let mut b = self.builder.clone();
            let features = b.values.iter().map(|(&f, _)| f).collect();
            let mut index = crate::layered::LayeredMap::default();
            b.index_chain_redefinitions(features, &mut index);
            index.freeze();
            Arc::clone(index.base_arc())
        })
    }

    /// The library's frozen multiplicity rows by the element whose own
    /// multiplicity each declares, made on first call.
    pub(crate) fn library_declared_multiplicities(&self) -> &RowIndex {
        self.declared_multiplicities.get_or_init(|| {
            let mut index = crate::layered::LayeredMap::default();
            self.builder.index_declared_multiplicities(
                0..self.builder.multiplicities.base_len(),
                &mut index,
            );
            index.freeze();
            Arc::clone(index.base_arc())
        })
    }

    /// The library's frozen multiplicity rows by the range each
    /// constrains, made on first call.
    /// The library's multiplicities whose bounds are expressions, made on
    /// first read over the frozen rows.
    pub(crate) fn library_expression_bounds(
        &self,
    ) -> &Arc<crate::check::multiplicity_domains::ExpressionBounds> {
        self.expression_bounds.get_or_init(|| {
            let rows =
                crate::layered::LayeredMap::over(Arc::clone(self.library_multiplicity_ranges()));
            let index = self.library_spec_index();
            let b = &self.builder;
            let targets = |owner: usize| -> Vec<usize> {
                index
                    .get(&owner)
                    .into_iter()
                    .flatten()
                    .filter(|&&i| matches!(b.spec_targets[i].1, "Subsetting" | "Redefinition"))
                    .filter_map(|&i| b.spec_resolved.get(i).copied().flatten())
                    .collect()
            };
            Arc::new(crate::check::multiplicity_domains::ExpressionBounds::over(
                b,
                &rows,
                0..b.elements.len(),
                None,
                &targets,
            ))
        })
    }

    pub(crate) fn library_multiplicity_ranges(&self) -> &RowIndex {
        self.multiplicity_ranges.get_or_init(|| {
            let mut index = crate::layered::LayeredMap::default();
            self.builder
                .index_multiplicity_ranges(0..self.builder.multiplicities.base_len(), &mut index);
            index.freeze();
            Arc::clone(index.base_arc())
        })
    }

    /// The plans of the library's own rows that builds on it extend (see
    /// [`crate::json::LibraryPlans`]): read back from the snapshot when it
    /// carried them, made on first call otherwise (`None` when they cannot
    /// be made).
    pub(crate) fn library_plans(self: &Arc<Self>) -> Option<Arc<crate::json::LibraryPlans>> {
        // Plans started on another thread are taken from it first; a thread
        // that ended early leaves them to be made here.
        self.plans.settle();
        self.plans
            .made
            .get_or_init(|| self.make_library_plans())
            .clone()
    }

    /// The plans read back from what the snapshot carried, else made.
    fn make_library_plans(self: &Arc<Self>) -> Option<Arc<crate::json::LibraryPlans>> {
        let carried = self.plans.take_carried();
        carried
            .and_then(|wire| crate::json::LibraryPlans::from_wire(self, wire))
            .or_else(|| crate::json::LibraryPlans::plan(self))
            .map(Arc::new)
    }

    /// Start making the library's plans on a thread of their own, so that
    /// the first build asking for them (`library_plans`) finds them
    /// made, or nearly, instead of making them in line: reading them back
    /// from a snapshot's columns costs about a tenth of a small model's
    /// warm check, and the build's own lowering and resolution run
    /// meanwhile. Nothing changes in what the plans are. Where no thread
    /// can be had — a target without threads, one core, a run asked for
    /// one thread, a host that refuses one — the first build makes them as
    /// before.
    pub fn start_plans(self: &Arc<Self>) {
        #[cfg(not(target_family = "wasm"))]
        {
            if !crate::par::enabled() || self.plans.made.get().is_some() {
                return;
            }
            let mut started = self.plans.started.lock().unwrap_or_else(|e| e.into_inner());
            if started.is_some() {
                return;
            }
            let library = Arc::clone(self);
            if let Ok(handle) = std::thread::Builder::new()
                .name("sysmlv2-library-plans".into())
                .stack_size(crate::par::STACK_BYTES)
                .spawn(move || library.make_library_plans())
            {
                *started = Some(handle);
            }
            // The tables every build on the library reads once per process
            // — its relationships' owners, its specialization rows by
            // owner — made meanwhile on a thread of their own, so the
            // first build finds them made; a build asking first makes
            // them itself, as before.
            let library = Arc::clone(self);
            let _ = std::thread::Builder::new()
                .name("sysmlv2-library-tables".into())
                .stack_size(crate::par::STACK_BYTES)
                .spawn(move || {
                    let _ = library.library_rel_owners();
                    let _ = library.library_spec_index();
                    let _ = library.library_expression_bounds();
                    let _ = library.library_name_keys();
                });
        }
    }

    /// Make the library's plans now, so that a snapshot written from this
    /// handle afterwards carries them and no process reading it plans the
    /// library again.
    pub fn make_plans(self: &Arc<Self>) {
        let _ = self.library_plans();
        self.plans
            .written
            .store(true, std::sync::atomic::Ordering::Release);
    }

    /// Whether the snapshot this handle was decoded from carried the
    /// library's plans and they have not been read back yet.
    #[cfg(test)]
    pub(crate) fn carries_plans(&self) -> bool {
        self.plans
            .carried
            .lock()
            .is_ok_and(|carried| carried.carries())
    }

    /// Make this handle carry `plans` as if its snapshot had, for the tests
    /// of what a read-back refuses.
    #[cfg(test)]
    pub(crate) fn set_decoded_plans(&self, plans: Option<crate::json::LibraryPlansWire>) {
        *self.plans.carried.lock().unwrap() = Carried::from_wire(plans);
    }

    /// Whether either cell still holds the snapshot for a part to read.
    #[cfg(test)]
    fn holds_snapshot(&self) -> bool {
        self.facts.holds_snapshot()
            || self
                .plans
                .carried
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .holds_snapshot()
    }

    /// The resolution recording a source-prepared handle keeps, encoded
    /// ([`crate::libcache::LibraryCache::to_bytes`]); `None` for a decoded handle.
    #[must_use]
    pub fn recording_bytes(&self) -> Option<Vec<u8>> {
        self.recording
            .as_ref()
            .map(|recording| recording.to_bytes())
    }

    /// Keep an encoded resolution recording ([`crate::libcache::LibraryCache::to_bytes`])
    /// for the builds that cannot reuse the prepared graph; a handle that
    /// already holds a decoded recording ignores it. Nothing is decoded here.
    #[must_use]
    pub fn with_lazy_recording(mut self, bytes: Vec<u8>) -> Self {
        if self.recording.is_none() {
            self.lazy_recording = Some(Arc::from(bytes));
        }
        self
    }
    /// Attach this library to an empty model, without parsing or graph lowering.
    pub fn install(self: Arc<Self>, model: &mut Model) -> io::Result<()> {
        model.install_prepared(self)
    }
    /// Decode a content- and build-identified snapshot file. Stale,
    /// truncated or corrupt caches are misses and may be rebuilt from
    /// source. The file is mapped and its facts and plans left in it, read
    /// apart from the load (the snapshot stays mapped for them): the load decodes the rows,
    /// the scopes and the rest, which every build reads. What hosts shipped
    /// with the library is verified and left behind (see
    /// [`Self::load_with`]).
    pub fn load(path: &Path, key: u64) -> Option<Self> {
        Self::load_file(path, key, None, false)
    }

    /// [`Self::load`], keeping what hosts shipped with the library for them
    /// to read back ([`Self::take_host_part`]) when `keep_host_parts`: a
    /// handle no such host reads drops it, and never holds its bytes.
    pub fn load_with(path: &Path, key: u64, keep_host_parts: bool) -> Option<Self> {
        Self::load_file(path, key, None, keep_host_parts)
    }

    /// [`Self::load`] of the cache's own file: a facts or plans part of it
    /// that turns out not to verify or decode removes the file, so that
    /// the next run prepares the library afresh and writes a sound one
    /// instead of every run working around the part. A snapshot shipped
    /// beside the toolkit is read with [`Self::load`] and left where it
    /// lies.
    pub fn load_cache(path: &Path, key: u64) -> Option<Self> {
        Self::load_file(path, key, Some(path.to_path_buf()), false)
    }

    fn load_file(
        path: &Path,
        key: u64,
        cache_file: Option<std::path::PathBuf>,
        keep_host_parts: bool,
    ) -> Option<Self> {
        let bytes = crate::libcache::map_capped(path)?;
        let snapshot = Arc::new(Snapshot::new(bytes, key, cache_file)?);
        Self::from_wire(decode_wire_apart(&snapshot, keep_host_parts)?)
    }

    /// Decode a snapshot held whole. What hosts shipped with the library is
    /// verified and left behind (see [`Self::from_bytes_with`]).
    pub fn from_bytes(bytes: &[u8], key: u64) -> Option<Self> {
        Self::from_bytes_with(bytes, key, false)
    }

    /// [`Self::from_bytes`], keeping what hosts shipped with the library for
    /// them to read back ([`Self::take_host_part`]) when `keep_host_parts`.
    /// Dropped, a host's part is still verified against its checksum, so a
    /// damaged one refuses the snapshot either way, but it is never decoded
    /// or copied: a handle no such host reads holds none of its bytes.
    pub fn from_bytes_with(bytes: &[u8], key: u64, keep_host_parts: bool) -> Option<Self> {
        if bytes.len() as u64 > MAX_BYTES {
            return None;
        }
        Self::from_wire(decode_wire(bytes, key, keep_host_parts)?)
    }

    /// [`Self::from_bytes`] over a snapshot the caller feeds in chunks: `fill`
    /// copies the next bytes of the `len`-byte snapshot into the buffer it
    /// is given and answers how many (0 once exhausted). Only a window of the
    /// snapshot is ever held here, so a host that already holds the bytes
    /// elsewhere (a browser's heap) pays no second copy of them. The parts
    /// are read one after the other, each verified against its checksum once
    /// its bytes have passed, so a corrupt part costs its own decode before
    /// the snapshot is refused; a stale or truncated one is refused the same
    /// as from `from_bytes`. What hosts shipped with the library is verified
    /// and left behind (see [`Self::from_chunks_with`]).
    pub fn from_chunks<F: FnMut(&mut [u8]) -> usize>(
        len: usize,
        fill: F,
        key: u64,
    ) -> Option<Self> {
        Self::from_chunks_with(len, fill, key, false)
    }

    /// [`Self::from_chunks`], keeping what hosts shipped with the library for
    /// them to read back ([`Self::take_host_part`]) when `keep_host_parts`.
    /// Dropped, a host's part passes through the window and is verified
    /// against its checksum, but none of it is kept.
    pub fn from_chunks_with<F: FnMut(&mut [u8]) -> usize>(
        len: usize,
        fill: F,
        key: u64,
        keep_host_parts: bool,
    ) -> Option<Self> {
        use crate::cache_codec::{Chunked, Limited, Source, StringTable, decode_part};
        if len as u64 > MAX_BYTES {
            return None;
        }
        let build = crate::libcache::TOOLKIT_BUILD.as_bytes();
        let mut src = Chunked::new(len, 64 * 1024, fill);
        if src.take(MAGIC.len()).ok()? != MAGIC
            || src.take(build.len()).ok()? != build
            || src.take(1).ok()? != b"\n"
        {
            return None;
        }
        let mut word =
            || -> Option<u64> { Some(u64::from_le_bytes(src.take(8).ok()?.try_into().ok()?)) };
        if word()? != key {
            return None;
        }
        let mut parts = [Part { len: 0, sum: 0 }; PARTS];
        for part in &mut parts {
            part.len = usize::try_from(word()?).ok()?;
            part.sum = word()?;
        }
        let total = parts
            .iter()
            .try_fold(0usize, |total, part| total.checked_add(part.len))?;
        if total != src.remaining() {
            return None;
        }
        /// The next part, read through a window of its own length and
        /// verified against its checksum once its bytes have passed.
        fn next<T: serde::de::DeserializeOwned, F: FnMut(&mut [u8]) -> usize>(
            src: &mut Chunked<F>,
            strings: &[&str],
            part: Part,
        ) -> Option<T> {
            src.reset_checksum();
            let value = decode_part(strings, Limited::new(src, part.len).ok()?).ok()?;
            (src.checksum() == part.sum).then_some(value)
        }
        src.reset_checksum();
        let table = StringTable::decode(Limited::new(&mut src, parts[0].len).ok()?).ok()?;
        if src.checksum() != parts[0].sum {
            return None;
        }
        let strings = table.strings();
        let units = next(&mut src, &strings, parts[1])?;
        let mut builder: Builder = next(&mut src, &strings, parts[2])?;
        let elements: crate::json::ElementRowsOwned = next(&mut src, &strings, parts[3])?;
        let scopes: crate::json::ScopeRowsOwned = next(&mut src, &strings, parts[4])?;
        builder.attach_rows(elements, scopes);
        let facts = FactsWire::Decoded(Box::new(next(&mut src, &strings, parts[FACTS_PART])?));
        let root_names = next(&mut src, &strings, parts[6])?;
        let plans = Carried::from_wire(next(&mut src, &strings, parts[PLANS_PART])?);
        let prefix = next(&mut src, &strings, parts[8])?;
        let lookup = next(&mut src, &strings, parts[9])?;
        let hosts = if keep_host_parts {
            next(&mut src, &strings, parts[HOSTS_PART])?
        } else {
            // Through the window a run at a time, verified, and let go.
            src.reset_checksum();
            let mut left = parts[HOSTS_PART].len;
            while left > 0 {
                let n = left.min(HOST_CHUNK);
                src.take(n).ok()?;
                left -= n;
            }
            if src.checksum() != parts[HOSTS_PART].sum {
                return None;
            }
            HostParts::default()
        };
        if src.remaining() != 0 {
            return None;
        }
        Self::from_wire(Wire {
            units,
            builder,
            facts,
            root_names,
            plans,
            prefix,
            lookup,
            hosts,
        })
    }

    /// The decoded records into a handle, validated and frozen. Facts held
    /// whole are validated here with the rest; facts left to be read apart
    /// are validated when they are (see [`LibraryFacts`]).
    fn from_wire(wire: Wire) -> Option<Self> {
        let rows = wire.builder.elements.len();
        let facts = Arc::new(match wire.facts {
            FactsWire::Decoded(facts) => {
                let mut facts = *facts;
                if !facts.valid(rows) {
                    return None;
                }
                facts.freeze();
                LibraryFacts::made(Arc::new(facts))
            }
            FactsWire::Pending(pending) => LibraryFacts::pending(rows, pending),
        });
        let mut result = Self {
            units: wire.units,
            builder: wire.builder,
            facts: Arc::clone(&facts),
            root_names: wire.root_names,
            recording: None,
            lazy_recording: None,
            plans: Plans::carried(wire.plans),
            enum_types: std::sync::OnceLock::new(),
            rel_owners: std::sync::OnceLock::new(),
            spec_index: std::sync::OnceLock::new(),
            name_keys: std::sync::OnceLock::new(),
            expression_bounds: std::sync::OnceLock::new(),
            chain_redefinitions: std::sync::OnceLock::new(),
            declared_multiplicities: std::sync::OnceLock::new(),
            multiplicity_ranges: std::sync::OnceLock::new(),
            derived: std::sync::Mutex::default(),
            hosts: std::sync::Mutex::new(wire.hosts),
        };
        result.builder.reset_lookup_caches();
        result.builder.prefix_carried = wire.prefix;
        result.builder.lookup_carried = wire.lookup;
        if result.units.sources.iter().any(|u| !u.is_library)
            || !result.builder.valid_library(result.units.len())
        {
            return None;
        }
        result.builder.library_facts = Some(facts);
        result.builder.freeze_library();
        Some(result)
    }
    pub fn to_bytes(&self, key: u64) -> io::Result<Vec<u8>> {
        let [mut header, table, body] = self.encoded(key)?;
        header.extend_from_slice(&table);
        header.extend_from_slice(&body);
        Ok(header)
    }

    /// The snapshot in three pieces — the header (magic, build, key, and
    /// the part table: each part's length and checksum), the payload's
    /// string table, and its body, the records one after the other — so
    /// that a writer need not join them: the body is as large as the
    /// library.
    fn encoded(&self, key: u64) -> io::Result<[Vec<u8>; 3]> {
        // About what the standard library's rows encode to: the buffer
        // grows past it once for a larger library and is not copied up to
        // it; never more than a snapshot may hold.
        let capacity = self
            .builder
            .elements
            .len()
            .saturating_mul(280)
            .min(usize::try_from(MAX_BYTES).unwrap_or(usize::MAX));
        // The records in the order the decoder reads them: the frozen rows'
        // structural scan is written from the builder's, with the
        // projections it has made, and their kept lookup graph likewise.
        let prefix = self
            .builder
            .prefix_structure
            .as_ref()
            .map(|prefix| prefix.to_wire());
        let lookup = self.builder.lookup_wire();
        let mut parts = crate::cache_codec::Parts::with_capacity(capacity);
        let failed = io::Error::other;
        parts.part(&self.units).map_err(failed)?;
        parts.part(&self.builder).map_err(failed)?;
        parts.part(&self.builder.element_rows()).map_err(failed)?;
        parts.part(&self.builder.scope_rows()).map_err(failed)?;
        let facts = self
            .facts
            .get()
            .ok_or_else(|| io::Error::other("the library's facts could not be read back"))?;
        parts.part(&facts).map_err(failed)?;
        parts.part(&SortedNames(&self.root_names)).map_err(failed)?;
        parts.part(&self.plans).map_err(failed)?;
        parts.part(&prefix).map_err(failed)?;
        parts.part(&lookup).map_err(failed)?;
        parts
            .part(&*self.hosts.lock().unwrap_or_else(|e| e.into_inner()))
            .map_err(failed)?;
        let (table, body, ends) = parts.finish();
        let mut header = MAGIC.to_vec();
        header.extend_from_slice(crate::libcache::TOOLKIT_BUILD.as_bytes());
        header.push(b'\n');
        header.extend_from_slice(&key.to_le_bytes());
        // The part table: the string table, then each record's slice of
        // the body, with the checksum of each.
        let mut extents = Vec::with_capacity(PARTS);
        extents.push((table.len(), checksum(&table)));
        let mut start = 0;
        for end in ends {
            extents.push((end - start, checksum(&body[start..end])));
            start = end;
        }
        debug_assert_eq!(extents.len(), PARTS, "one part per record");
        for (len, sum) in extents {
            header.extend_from_slice(&(len as u64).to_le_bytes());
            header.extend_from_slice(&sum.to_le_bytes());
        }
        if (header.len() + table.len() + body.len()) as u64 > MAX_BYTES {
            return Err(io::Error::other(
                "prepared library exceeds cache size limit",
            ));
        }
        Ok([header, table, body])
    }

    pub fn save(&self, path: &Path, key: u64) -> io::Result<()> {
        let [header, table, body] = self.encoded(key)?;
        crate::libcache::write_atomically_parts(path, &[&header, &table, &body])
    }
}
/// A set of names written in order, so that the same snapshot is written
/// the same way every time (see [`sorted_set`]).
pub(crate) fn sorted_names<S: serde::Serializer>(
    names: &std::collections::HashSet<String>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    sorted_set(names, serializer)
}

/// A hash set written as a sequence in its elements' order, whatever order
/// the table holds them in: a set over a seeded hasher iterates differently
/// in every process, and a snapshot's bytes must not. Read back as the set
/// it was, by the set's own deserializer.
pub(crate) fn sorted_set<T: Ord + Serialize, H, S: serde::Serializer>(
    set: &std::collections::HashSet<T, H>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut items: Vec<&T> = set.iter().collect();
    items.sort_unstable();
    serializer.collect_seq(items)
}

/// A hash map written as a map in its keys' order, as [`sorted_set`] writes
/// a set. Read back as the map it was, by the map's own deserializer.
pub(crate) fn sorted_map<K: Ord + Serialize, V: Serialize, H, S: serde::Serializer>(
    map: &std::collections::HashMap<K, V, H>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut entries: Vec<(&K, &V)> = map.iter().collect();
    entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
    serializer.collect_map(entries)
}

/// The implied-specialization and positional plans of a library's own rows
/// (see [`crate::json::LibraryPlans`]): read back from the snapshot when the
/// writer had made them, made otherwise by the first build on the library
/// that plans. A snapshot written from the handle carries them only when the
/// handle's own did or [`PreparedLibrary::make_plans`] asked for it — a
/// build on a shared handle changes nothing the handle writes.
#[derive(Default)]
struct Plans {
    /// The plans the snapshot carried — decoded, or still in the snapshot
    /// — until the first request reads them back.
    carried: std::sync::Mutex<Carried>,
    /// The plans read back or made, once requested (`None` when they cannot
    /// be made).
    made: std::sync::OnceLock<Option<Arc<crate::json::LibraryPlans>>>,
    /// Whether a snapshot written from the handle carries the plans.
    written: std::sync::atomic::AtomicBool,
    /// Whether the plans the snapshot left to be read apart turned out
    /// not to verify or decode (see [`PreparedLibrary::damaged`]).
    damaged: std::sync::atomic::AtomicBool,
    /// The thread making the plans ahead of the first request (see
    /// [`PreparedLibrary::start_plans`]), until a request takes what it made.
    #[cfg(not(target_family = "wasm"))]
    started: std::sync::Mutex<Option<std::thread::JoinHandle<MadePlans>>>,
}

/// What making the plans yields (`None` when they cannot be made).
#[cfg(not(target_family = "wasm"))]
type MadePlans = Option<Arc<crate::json::LibraryPlans>>;

impl Plans {
    /// The plans a snapshot carried (none when it carried none).
    fn carried(wire: Carried) -> Self {
        Self {
            written: std::sync::atomic::AtomicBool::new(wire.carries()),
            carried: std::sync::Mutex::new(wire),
            made: std::sync::OnceLock::new(),
            damaged: std::sync::atomic::AtomicBool::new(false),
            #[cfg(not(target_family = "wasm"))]
            started: std::sync::Mutex::new(None),
        }
    }

    /// The plans the snapshot carried, taken (see [`Carried::take`]). A
    /// snapshot read and found to carry none leaves none for a write
    /// either, as one held whole does.
    fn take_carried(&self) -> Option<crate::json::LibraryPlansWire> {
        let mut carried = self.carried.lock().unwrap_or_else(|e| e.into_inner());
        let pending = carried.pending();
        match carried.take() {
            Some(Some(wire)) => Some(wire),
            Some(None) => {
                self.written
                    .store(false, std::sync::atomic::Ordering::Release);
                None
            }
            None => {
                // Left in the snapshot and not read back: the part did
                // not verify or decode.
                if pending {
                    self.damaged
                        .store(true, std::sync::atomic::Ordering::Release);
                }
                None
            }
        }
    }

    /// Whether the plans left in the snapshot turned out not to read back.
    fn damaged(&self) -> bool {
        self.damaged.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Take the plans a started thread made, when one was started: they are
    /// the plans made from then on. A thread that ended early leaves nothing,
    /// and the next request makes the plans itself.
    fn settle(&self) {
        #[cfg(not(target_family = "wasm"))]
        {
            let started = self
                .started
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .take();
            if let Some(handle) = started {
                if let Ok(made) = handle.join() {
                    let _ = self.made.get_or_init(|| made);
                }
            }
        }
    }
}

/// The header of a snapshot held whole — its part table — and the payload
/// after it; `None` for another build's or another library's snapshot, or
/// one whose parts do not add up to its payload.
fn header_parts(bytes: &[u8], key: u64) -> Option<([Part; PARTS], &[u8])> {
    let bytes = bytes.strip_prefix(MAGIC)?;
    let build = crate::libcache::TOOLKIT_BUILD.as_bytes();
    let mut bytes = bytes.strip_prefix(build)?.strip_prefix(b"\n")?;
    let mut word = || -> Option<u64> {
        let (head, tail) = bytes.split_at_checked(8)?;
        bytes = tail;
        Some(u64::from_le_bytes(head.try_into().ok()?))
    };
    if word()? != key {
        return None;
    }
    let mut parts = [Part { len: 0, sum: 0 }; PARTS];
    for part in &mut parts {
        part.len = usize::try_from(word()?).ok()?;
        part.sum = word()?;
    }
    let total = parts
        .iter()
        .try_fold(0usize, |total, part| total.checked_add(part.len))?;
    (total == bytes.len()).then_some((parts, bytes))
}

/// The records of a snapshot held whole: every part verified against its
/// checksum and decoded over the one string table — the records side by
/// side where threads are had (see [`crate::par`]), the builder's tables,
/// most of the payload, first.
fn decode_wire(bytes: &[u8], key: u64, keep_host_parts: bool) -> Option<Wire> {
    use crate::cache_codec::{Slice, StringTable};
    let (parts, payload) = header_parts(bytes, key)?;
    let mut slices = [&[][..]; PARTS];
    let mut rest = payload;
    for (slice, part) in slices.iter_mut().zip(&parts) {
        let (head, tail) = rest.split_at_checked(part.len)?;
        *slice = head;
        rest = tail;
    }
    // A part is read only once its bytes are verified.
    let verified = |i: usize| (checksum(slices[i]) == parts[i].sum).then_some(slices[i]);
    let table = StringTable::decode(Slice(verified(0)?)).ok()?;
    decode_records(&table.strings(), &verified, None, keep_host_parts)
}

/// The records of a snapshot a load keeps (see [`Snapshot`]): as
/// [`decode_wire`], with the facts and the plans left in the snapshot, to
/// be read apart from the load.
fn decode_wire_apart(snapshot: &Arc<Snapshot>, keep_host_parts: bool) -> Option<Wire> {
    let verified = |i: usize| snapshot.verified(i);
    decode_records(
        &snapshot.strings.strings(),
        &verified,
        Some(snapshot),
        keep_host_parts,
    )
}

/// The records of a snapshot over its string table, each from its verified
/// bytes (`verified(i)` is part `i`'s, or `None` when it does not verify):
/// the four small records on the calling thread; the element rows, the
/// scope rows, the rest of the builder, the facts and the plans each on a
/// thread of their own, the largest first. With `apart`, the facts and the
/// plans are not decoded here: they are left to their cells, which read
/// them from the snapshot on a thread of their own beside the load where
/// one can be had, else on first use.
fn decode_records<'a, V: Fn(usize) -> Option<&'a [u8]> + Sync>(
    strings: &[&str],
    verified: &V,
    apart: Option<&Arc<Snapshot>>,
    keep_host_parts: bool,
) -> Option<Wire> {
    use crate::cache_codec::{Slice, decode_part};
    /// One record over the table, from its verified bytes.
    fn record<T: serde::de::DeserializeOwned>(strings: &[&str], bytes: Option<&[u8]>) -> Option<T> {
        decode_part(strings, Slice(bytes?)).ok()
    }
    let small = || {
        (
            record::<Arc<LibraryUnits>>(strings, verified(1)),
            record::<std::collections::HashSet<String>>(strings, verified(6)),
            record::<Option<crate::json::PrefixWire>>(strings, verified(8)),
            record::<Option<crate::json::GraphWire>>(strings, verified(9)),
            // Dropped, the hosts' part is verified and not decoded.
            if keep_host_parts {
                record::<HostParts>(strings, verified(HOSTS_PART))
            } else {
                verified(HOSTS_PART).map(|_| HostParts::default())
            },
        )
    };
    // The two parts read apart start their cells here, ahead of the rest;
    // held whole, each is decoded on a thread like the others.
    let (facts_apart, plans_apart) = match apart {
        Some(snapshot) => (
            Some(FactsWire::Pending(PendingFacts::start(Arc::clone(
                snapshot,
            )))),
            Some(Carried::start(Arc::clone(snapshot))),
        ),
        None => (None, None),
    };
    let plans_on = move || match plans_apart {
        Some(plans) => (Some(plans), small()),
        None => crate::par::join(
            || {
                record::<Option<crate::json::LibraryPlansWire>>(strings, verified(PLANS_PART))
                    .map(Carried::from_wire)
            },
            small,
        ),
    };
    let facts_on = move || match facts_apart {
        Some(facts) => (Some(facts), plans_on()),
        None => crate::par::join(
            || {
                record::<crate::check::facts::Facts>(strings, verified(FACTS_PART))
                    .map(|facts| FactsWire::Decoded(Box::new(facts)))
            },
            plans_on,
        ),
    };
    let builder_on = || crate::par::join(|| record::<Builder>(strings, verified(2)), facts_on);
    let scopes_on = || {
        crate::par::join(
            || record::<crate::json::ScopeRowsOwned>(strings, verified(4)),
            builder_on,
        )
    };
    let (
        elements,
        (scopes, (builder, (facts, (plans, (units, root_names, prefix, lookup, hosts))))),
    ) = crate::par::join(
        || record::<crate::json::ElementRowsOwned>(strings, verified(3)),
        scopes_on,
    );
    let mut builder = builder?;
    builder.attach_rows(elements?, scopes?);
    Some(Wire {
        units: units?,
        builder,
        facts: facts?,
        root_names: root_names?,
        plans: plans?,
        prefix: prefix?,
        lookup: lookup?,
        hosts: hosts?,
    })
}

/// A snapshot a load keeps — mapped, or read whole — for the two parts it
/// reads apart from the load: the facts, which only the checks read, and
/// the plans, which only a build that plans reads. Each is decoded on a
/// thread of its own beside the load where one can be had (see
/// [`crate::par`]), else on first use; a run that reads neither never
/// decodes them. Held by those parts' cells until each is read and by
/// nothing else, so the file is unmapped once both are.
pub(crate) struct Snapshot {
    bytes: crate::libcache::SnapshotBytes,
    strings: crate::cache_codec::StringTable,
    /// Where each part lies in the bytes, with its checksum.
    parts: [(std::ops::Range<usize>, u64); PARTS],
    /// The cache's own file these bytes are, removed when a part of it
    /// does not verify or decode (see [`Self::part`]); `None` for a
    /// snapshot read in place, which is left where it lies.
    cache_file: Option<std::path::PathBuf>,
}

impl Snapshot {
    /// The snapshot held in `bytes`, its header read and its string table
    /// decoded; `None` for another build's or another library's, or one
    /// whose parts do not add up (see [`header_parts`]).
    fn new(
        bytes: crate::libcache::SnapshotBytes,
        key: u64,
        cache_file: Option<std::path::PathBuf>,
    ) -> Option<Self> {
        use crate::cache_codec::{Slice, StringTable};
        let (table, payload) = header_parts(bytes.as_ref(), key)?;
        let mut at = bytes.as_ref().len() - payload.len();
        let parts = std::array::from_fn(|i| {
            let range = at..at + table[i].len;
            at += table[i].len;
            (range, table[i].sum)
        });
        let strings = {
            let table = &bytes.as_ref()[parts[0].0.clone()];
            if checksum(table) != parts[0].1 {
                return None;
            }
            StringTable::decode(Slice(table)).ok()?
        };
        Some(Self {
            bytes,
            strings,
            parts,
            cache_file,
        })
    }

    /// Part `i`'s bytes, once verified against its checksum; `None` when
    /// they do not verify.
    fn verified(&self, i: usize) -> Option<&[u8]> {
        let bytes = &self.bytes.as_ref()[self.parts[i].0.clone()];
        (checksum(bytes) == self.parts[i].1).then_some(bytes)
    }

    /// Part `i` verified and decoded over the string table; `None` when it
    /// does not verify or decode. Such a part of the cache's own file
    /// removes the file: the next run then prepares the library afresh and
    /// writes a sound one, instead of every run working around the part.
    fn part<T: serde::de::DeserializeOwned>(&self, i: usize) -> Option<T> {
        use crate::cache_codec::{Slice, decode_part};
        let part = self
            .verified(i)
            .and_then(|bytes| decode_part(&self.strings.strings(), Slice(bytes)).ok());
        if part.is_none() {
            if let Some(path) = &self.cache_file {
                // (a file gone already, or one the platform holds, is left)
                let _ = std::fs::remove_file(path);
            }
        }
        part
    }
}

/// The facts record of a snapshot as the decode leaves it: decoded with the
/// rest, or left in the snapshot.
enum FactsWire {
    Decoded(Box<crate::check::facts::Facts>),
    Pending(PendingFacts),
}

/// The library's facts still to be read from its snapshot.
enum PendingFacts {
    /// Read, or never there.
    None,
    /// Decoded on first use.
    Part(Arc<Snapshot>),
    /// Being decoded on a thread of their own, joined on first use.
    #[cfg(not(target_family = "wasm"))]
    Thread(std::thread::JoinHandle<Option<crate::check::facts::Facts>>),
}

impl PendingFacts {
    /// The facts of `snapshot`, decoding on a thread of their own where one
    /// can be had.
    fn start(snapshot: Arc<Snapshot>) -> Self {
        #[cfg(not(target_family = "wasm"))]
        if crate::par::enabled() {
            let held = Arc::clone(&snapshot);
            let spawned = std::thread::Builder::new()
                .name("sysmlv2-library-facts".into())
                .stack_size(crate::par::STACK_BYTES)
                .spawn(move || held.part(FACTS_PART));
            // A thread the host refuses leaves the facts to be read in line.
            if let Ok(handle) = spawned {
                return Self::Thread(handle);
            }
        }
        Self::Part(snapshot)
    }

    /// The facts, decoded; `None` once taken or when the part does not
    /// decode.
    fn take(&mut self) -> Option<crate::check::facts::Facts> {
        match std::mem::replace(self, Self::None) {
            Self::None => None,
            Self::Part(snapshot) => snapshot.part(FACTS_PART),
            #[cfg(not(target_family = "wasm"))]
            Self::Thread(handle) => handle.join().ok().flatten(),
        }
    }
}

/// The static facts of a library's rows, shared by every build on it:
/// made when the library was prepared from source, or decoded with the
/// snapshot held whole, or — from a snapshot file — read apart from the
/// load on first use (see [`Snapshot`]). A part that does not verify or
/// decode leaves no facts: a build then makes its own over every row, as
/// one without a prepared library does, and answers the same.
pub(crate) struct LibraryFacts {
    /// The library's rows, which the facts must cover exactly.
    rows: usize,
    pending: std::sync::Mutex<PendingFacts>,
    made: std::sync::OnceLock<Option<Arc<crate::check::facts::Facts>>>,
}

impl LibraryFacts {
    /// Facts made or decoded already, validated and frozen.
    fn made(facts: Arc<crate::check::facts::Facts>) -> Self {
        Self {
            rows: 0,
            pending: std::sync::Mutex::new(PendingFacts::None),
            made: std::sync::OnceLock::from(Some(facts)),
        }
    }

    /// Facts still to be read, over `rows` rows.
    fn pending(rows: usize, pending: PendingFacts) -> Self {
        Self {
            rows,
            pending: std::sync::Mutex::new(pending),
            made: std::sync::OnceLock::new(),
        }
    }

    /// The facts, read on the first call: validated against the rows and
    /// frozen. `None` when the snapshot's part does not verify, decode or
    /// fit the rows.
    pub(crate) fn get(&self) -> Option<Arc<crate::check::facts::Facts>> {
        self.made
            .get_or_init(|| {
                let mut facts = self
                    .pending
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .take()?;
                if !facts.valid(self.rows) {
                    return None;
                }
                facts.freeze();
                Some(Arc::new(facts))
            })
            .clone()
    }

    /// Whether the facts left in the snapshot turned out not to verify,
    /// decode or fit the rows.
    fn damaged(&self) -> bool {
        matches!(self.made.get(), Some(None))
    }

    /// Whether the facts have been read (or were made with the handle).
    #[cfg(test)]
    pub(crate) fn is_made(&self) -> bool {
        self.made.get().is_some()
    }

    /// Whether the facts are still to be read from the snapshot.
    #[cfg(test)]
    fn holds_snapshot(&self) -> bool {
        !matches!(
            *self.pending.lock().unwrap_or_else(|e| e.into_inner()),
            PendingFacts::None
        )
    }
}

/// The plans a snapshot carries, as a handle holds them until the first
/// request reads them back.
#[derive(Default)]
enum Carried {
    /// None carried, or read back already.
    #[default]
    None,
    /// Decoded with the snapshot held whole.
    Wire(Box<crate::json::LibraryPlansWire>),
    /// Left in the snapshot, decoded on first use.
    Part(Arc<Snapshot>),
    /// Being decoded on a thread of their own, joined on first use.
    #[cfg(not(target_family = "wasm"))]
    Thread(std::thread::JoinHandle<Option<Option<crate::json::LibraryPlansWire>>>),
}

impl Carried {
    /// The plans decoded with the snapshot (`None` when it carried none).
    fn from_wire(wire: Option<crate::json::LibraryPlansWire>) -> Self {
        wire.map_or(Self::None, |wire| Self::Wire(Box::new(wire)))
    }

    /// The plans of `snapshot`, decoding on a thread of their own where one
    /// can be had.
    fn start(snapshot: Arc<Snapshot>) -> Self {
        #[cfg(not(target_family = "wasm"))]
        if crate::par::enabled() {
            let held = Arc::clone(&snapshot);
            let spawned = std::thread::Builder::new()
                .name("sysmlv2-library-plans-wire".into())
                .stack_size(crate::par::STACK_BYTES)
                .spawn(move || held.part(PLANS_PART));
            if let Ok(handle) = spawned {
                return Self::Thread(handle);
            }
        }
        Self::Part(snapshot)
    }

    /// Whether plans are carried and not yet read back.
    fn carries(&self) -> bool {
        !matches!(self, Self::None)
    }

    /// Whether the plans are still in the snapshot, to be read apart.
    fn pending(&self) -> bool {
        !matches!(self, Self::None | Self::Wire(_))
    }

    /// Whether the plans are still to be read from the snapshot.
    #[cfg(test)]
    fn holds_snapshot(&self) -> bool {
        !matches!(self, Self::None | Self::Wire(_))
    }

    /// The plans, taken: decoded from the snapshot when still in it.
    /// `Some(None)` when the snapshot was read and carried none, `None`
    /// once taken or when the part does not verify or decode — the
    /// library is then planned instead.
    fn take(&mut self) -> Option<Option<crate::json::LibraryPlansWire>> {
        match std::mem::replace(self, Self::None) {
            Self::None => None,
            Self::Wire(wire) => Some(Some(*wire)),
            Self::Part(snapshot) => snapshot.part(PLANS_PART),
            #[cfg(not(target_family = "wasm"))]
            Self::Thread(handle) => handle.join().ok().flatten(),
        }
    }

    /// The plans read back into place, decoded, for a write: `Some(true)`
    /// with plans in place, `Some(false)` when the snapshot was read and
    /// carried none, `None` when there is nothing left to read.
    fn read_back(&mut self) -> Option<bool> {
        if matches!(self, Self::Wire(_)) {
            return Some(true);
        }
        if matches!(self, Self::None) {
            return None;
        }
        match self.take() {
            Some(Some(wire)) => {
                *self = Self::Wire(Box::new(wire));
                Some(true)
            }
            Some(None) => Some(false),
            None => None,
        }
    }
}

/// A set of names written in order (see [`sorted_names`]).
struct SortedNames<'a>(&'a std::collections::HashSet<String>);
impl Serialize for SortedNames<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        sorted_names(self.0, serializer)
    }
}

impl serde::Serialize for Plans {
    /// The plans as the snapshot carries them: those carried and not yet
    /// read back, else those read back or made — when the handle writes
    /// them at all.
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if !self.written.load(std::sync::atomic::Ordering::Acquire) {
            return None::<crate::json::LibraryPlansWire>.serialize(serializer);
        }
        // Plans a thread is still making are waited for: the snapshot
        // carries them, not the thread's absence.
        self.settle();
        // The carried plans are read back under the lock, a thread still
        // decoding them joined there; the decoder takes no lock.
        let mut carried = self.carried.lock().ok();
        if let Some(carried) = carried.as_deref_mut() {
            match carried.read_back() {
                Some(true) => {
                    if let Carried::Wire(wire) = carried {
                        return Some(wire).serialize(serializer);
                    }
                }
                // Read, and found to carry none: none are written.
                Some(false) => {
                    self.written
                        .store(false, std::sync::atomic::Ordering::Release);
                    return None::<crate::json::LibraryPlansWire>.serialize(serializer);
                }
                None => {}
            }
        }
        self.made
            .get()
            .and_then(|plans| plans.as_ref())
            .and_then(|plans| plans.to_wire())
            .serialize(serializer)
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
    /// The cache writes a cold load started on another thread: finished
    /// by [`Self::finish`], left to the process by [`PendingSave::detach`]
    /// (the command line joins them before it exits), joined when dropped.
    /// `None` when the load wrote nothing, or wrote in line.
    pub pending: Option<PendingSave>,
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
    /// Whether the library is the cache directory's one snapshot, decoded
    /// while the library directory's content key was computed and kept
    /// because the key agreed, rather than read once the key was known
    /// (see [`load_library_with_cache`]).
    pub guessed: bool,
}

/// Load a directory library with ambient sources. Prepared snapshots serve new
/// models; the resolution-only cache remains available when appending libraries
/// to an existing model. `SYSMLV2_LIB_CACHE=off` disables both paths.
///
/// Complete snapshots are saved during preparation; see [`LibraryLoad`] for
/// what the caller does with the result.
pub fn load_library_with_cache(model: &mut Model, dir: &Path) -> io::Result<LibraryLoad> {
    load_library_with_cache_in(model, dir, crate::libcache::default_cache_dir().as_deref())
}

/// [`load_library_with_cache`] with the cache in `cache_dir` (`None`: no
/// cache directory, so nothing is read from or written to one).
fn load_library_with_cache_in(
    model: &mut Model,
    dir: &Path,
    cache_dir: Option<&Path>,
) -> io::Result<LibraryLoad> {
    use crate::{ambient, libcache};
    let enabled = !std::env::var_os("SYSMLV2_LIB_CACHE").is_some_and(|v| v == "off");
    if !enabled {
        return load_library_with_cache_from(model, dir, None, None, &[]);
    }
    // The content key reads and hashes every library file. The cache
    // directory's one snapshot — the common case — is read and decoded
    // meanwhile, on a thread, and kept when the key it was written under is
    // the key the directory hashes to; a snapshot of another library is
    // dropped and the load goes on as if nothing had been read. Nothing is
    // guessed for a model that already has units (it takes no snapshot) or
    // for a library this process already holds (the registry serves it).
    let format = model.graph_format();
    let guess = cache_dir
        .filter(|_| model.unit_count() == 0)
        .and_then(|cache_dir| snapshot_guess(cache_dir, format))
        .filter(|(_, recording)| !shared_holds(recording));
    let (guessed, key) = crate::par::join(
        || {
            let (key, recording) = guess?;
            let library = PreparedLibrary::load_cache(&recording.with_extension("prepared"), key)
                .filter(|library| library.graph_format() == format)?;
            Some((key, library))
        },
        || libcache::hash_library_dir(dir).map(ambient::mix_key),
    );
    let key = key?;
    let cache = cache_dir.map(|cache_dir| libcache::cache_path_in(cache_dir, key));
    let shipped = libcache::shipped_cache_paths_for(key, Some(dir));
    let guessed = guessed.filter(|(guessed_key, _)| *guessed_key == key);
    load_library_with_cache_with(model, dir, Some(key), cache, &shipped, guessed)
}

/// The one complete snapshot in the cache directory `dir` for `format`, as
/// the key it was written under and its recording path — `None` when the
/// directory holds none or more than one, or cannot be read.
fn snapshot_guess(
    dir: &Path,
    format: crate::model::GraphFormat,
) -> Option<(u64, std::path::PathBuf)> {
    let suffix = match format {
        crate::model::GraphFormat::CanonicalV3 => ".v3.prepared",
        _ => ".prepared",
    };
    let mut found = None;
    for entry in std::fs::read_dir(dir).ok()?.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let Some(hex) = name
            .strip_prefix("stdlib-")
            .and_then(|rest| rest.strip_suffix(suffix))
        else {
            continue;
        };
        let Ok(key) = u64::from_str_radix(hex, 16) else {
            continue;
        };
        if hex.len() != 16 || found.is_some() {
            return None;
        }
        found = Some((key, dir.join(format!("stdlib-{key:016x}.libcache"))));
    }
    found
}

/// Where a cold load's two cache files were written by [`prepare_library_into`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedPaths {
    /// The complete snapshot, `stdlib-<key>.prepared`.
    pub snapshot: std::path::PathBuf,
    /// The resolution recording beside it, `stdlib-<key>.libcache`, when
    /// the preparation recorded one.
    pub recording: Option<std::path::PathBuf>,
}

/// Prepare the directory library `dir` (with the ambient sources, as a
/// load does) and write its snapshot and recording into `out`, named by the
/// library's content key as the cache names them — so that a process whose
/// cache has no snapshot reads them from there instead of preparing the
/// library from source (see [`crate::libcache::shipped_cache_paths_for`]). The
/// files are for this toolkit build and the default graph format: another
/// build, or a run with another format, passes them over and prepares. The
/// snapshot alone serves a run; without the recording beside it, a build
/// that must resolve the library jointly resolves it without replay.
pub fn prepare_library_into(dir: &Path, out: &Path) -> io::Result<PreparedPaths> {
    use crate::{ambient, libcache};
    let key = ambient::mix_key(libcache::hash_library_dir(dir)?);
    let recording = out.join(format!("stdlib-{key:016x}.libcache"));
    let snapshot = recording.with_extension("prepared");
    let mut model = Model::new();
    model.load_library_dir(dir)?;
    ambient::add_to(&mut model);
    model.record_library_cache();
    let library = model.prepare_library()?;
    let recorded = model.take_recorded_library_cache();
    if let Some(recorded) = &recorded {
        recorded.save(&recording)?;
    }
    library.make_plans();
    library.save(&snapshot, key)?;
    Ok(PreparedPaths {
        snapshot,
        recording: recorded.map(|_| recording),
    })
}

/// [`load_library_with_cache`] with an explicit content key and resolution
/// cache path. The complete snapshot lives beside that path under the
/// `prepared` extension. A prepared model also keeps the resolution recording
/// reachable for builds that must resolve jointly after all: those replay it
/// instead of resolving the whole library cold. A snapshot miss records that
/// recording while preparing, and the handle then keeps it in memory; a
/// decoded handle leaves it on disk, unread until such a build.
#[cfg(test)]
pub(crate) fn load_library_with_cache_at(
    model: &mut Model,
    dir: &Path,
    cache: Option<(u64, std::path::PathBuf)>,
) -> io::Result<LibraryLoad> {
    let (key, path) = match cache {
        Some((key, path)) => (Some(key), Some(path)),
        None => (None, None),
    };
    load_library_with_cache_from(model, dir, key, path, &[])
}

/// The libraries this process prepared or decoded, by key and graph format,
/// with the recording path a model that installs one again reads lazily.
type SharedLibraries = std::sync::Mutex<
    std::collections::HashMap<(u64, u8), (std::sync::Weak<PreparedLibrary>, std::path::PathBuf)>,
>;
static SHARED: std::sync::OnceLock<SharedLibraries> = std::sync::OnceLock::new();

/// The libraries the process keeps after the last session on each closed,
/// so that the next load of the same directory is served by the registry
/// instead of decoding the snapshot again: an SDK or a language server
/// opening sessions one after the other pays the decode once. Decoded
/// handles are kept, not ones prepared from source in this process (those
/// carry their parsed units; the run that prepared a library decodes it
/// once more, and keeps that). The two most recently loaded are kept (a
/// host switching between two libraries keeps both);
/// `SYSMLV2_LIB_RETAIN=off` keeps none, and [`release_retained_libraries`]
/// lets them go.
static RETAINED: std::sync::Mutex<Vec<Arc<PreparedLibrary>>> = std::sync::Mutex::new(Vec::new());
const RETAINED_LIBRARIES: usize = 2;

fn retain(library: &Arc<PreparedLibrary>) {
    if library.damaged()
        || std::env::var_os("SYSMLV2_LIB_RETAIN").is_some_and(|v| v == "off" || v == "0")
    {
        return;
    }
    let mut retained = RETAINED.lock().unwrap_or_else(|e| e.into_inner());
    retained.retain(|kept| !Arc::ptr_eq(kept, library));
    retained.push(Arc::clone(library));
    if retained.len() > RETAINED_LIBRARIES {
        retained.remove(0);
    }
}

/// Let go of the libraries the process retained after their sessions closed
/// (see [`load_library_with_cache`]): a library no session holds is freed,
/// and the next load of its directory reads the snapshot again. A host that
/// is done with a library, or must give its memory back, calls this.
pub fn release_retained_libraries() {
    RETAINED.lock().unwrap_or_else(|e| e.into_inner()).clear();
}

/// Let go of `library` alone, should the process have retained it.
fn release_retained(library: &Arc<PreparedLibrary>) {
    RETAINED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .retain(|kept| !Arc::ptr_eq(kept, library));
}

impl PreparedLibrary {
    /// Whether a part of the snapshot this handle was loaded from — its
    /// facts or its plans, read apart from the load — turned out not to
    /// verify or decode. The loader removed the cache's file then (see
    /// [`Snapshot::part`]); the handle answers without that part, and the
    /// process serves it to no further load, so that the next one prepares
    /// the library afresh and writes a sound snapshot.
    fn damaged(&self) -> bool {
        self.facts.damaged() || self.plans.damaged()
    }
}

/// Whether this process still holds a library whose recording path is
/// `recording` — one the registry will serve without reading anything.
fn shared_holds(recording: &Path) -> bool {
    SHARED.get().is_some_and(|shared| {
        shared
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .values()
            .any(|(library, path)| library.strong_count() > 0 && path == recording)
    })
}

/// [`load_library_with_cache_at`] with the content key apart from the cache
/// path — a run may have a key and no cache directory — and the snapshots
/// shipped with the toolkit: `shipped` lists recording paths
/// (`stdlib-<key>.libcache`) whose `prepared` siblings are tried, in order,
/// after the cache's own, and read in place; nothing is copied into the
/// cache. With a key and no cache path only a shipped snapshot is read:
/// without one the library is built with the model, as without a key.
pub(crate) fn load_library_with_cache_from(
    model: &mut Model,
    dir: &Path,
    key: Option<u64>,
    cache: Option<std::path::PathBuf>,
    shipped: &[std::path::PathBuf],
) -> io::Result<LibraryLoad> {
    load_library_with_cache_with(model, dir, key, cache, shipped, None)
}

/// [`load_library_with_cache_from`] with a snapshot already decoded from the
/// cache — the cache's own, read while the key was computed — which stands
/// in for reading it, when its key is the load's.
fn load_library_with_cache_with(
    model: &mut Model,
    dir: &Path,
    key: Option<u64>,
    cache: Option<std::path::PathBuf>,
    shipped: &[std::path::PathBuf],
    guessed: Option<(u64, PreparedLibrary)>,
) -> io::Result<LibraryLoad> {
    use crate::{ambient, libcache};
    use std::sync::Mutex;
    let for_format = |path: std::path::PathBuf| {
        if model.graph_format() == crate::model::GraphFormat::CanonicalV3 {
            path.with_extension("v3.cache")
        } else {
            path
        }
    };
    let cache = cache.map(for_format);
    let shipped: Vec<std::path::PathBuf> = shipped.iter().cloned().map(for_format).collect();
    let mut warnings = Vec::new();
    let mut pending = None;
    if model.unit_count() == 0 {
        if let Some(key) = key {
            let shared = SHARED.get_or_init(Mutex::default);
            let cached = {
                let mut entries = shared.lock().unwrap_or_else(|e| e.into_inner());
                entries.retain(|_, (value, _)| value.strong_count() > 0);
                entries
                    .get(&(key, model.graph_format().version()))
                    .and_then(|(value, recording)| Some((value.upgrade()?, recording.clone())))
            };
            // A handle whose snapshot proved corrupt in part is let go,
            // not served: the next load prepares the library afresh.
            let cached = cached.filter(|(library, _)| {
                let sound = !library.damaged();
                if !sound {
                    release_retained(library);
                }
                sound
            });
            if let Some((library, recording)) = cached {
                // A handle prepared from source in this process keeps its
                // recording in memory, so the cache file is left unread.
                let recorded = library.recording.is_some();
                if !recorded {
                    retain(&library);
                }
                library.install(model)?;
                if !recorded {
                    model.set_lazy_library_cache(recording);
                }
                return Ok(LibraryLoad::default());
            }
            // The cache's own snapshot first — decoded already when it was
            // guessed while the key was computed — then the ones shipped with
            // the toolkit, read where they lie.
            let guessed = guessed
                .filter(|(guessed_key, library)| {
                    *guessed_key == key && library.graph_format() == model.graph_format()
                })
                .and_then(|(_, library)| Some((library, cache.clone()?)));
            let was_guessed = guessed.is_some();
            let found = guessed.or_else(|| {
                // The cache's own file is removed should a part of it turn
                // out corrupt; a shipped one is read where it lies.
                let own = cache.iter().map(|recording| (recording, true));
                let in_place = shipped.iter().map(|recording| (recording, false));
                own.chain(in_place).find_map(|(recording, own)| {
                    let snapshot = recording.with_extension("prepared");
                    let library = if own {
                        PreparedLibrary::load_cache(&snapshot, key)
                    } else {
                        PreparedLibrary::load(&snapshot, key)
                    }
                    .filter(|library| library.graph_format() == model.graph_format())?;
                    Some((library, recording.clone()))
                })
            });
            let prepared = match found {
                Some((library, recording)) => {
                    let library = Arc::new(library);
                    // The plans a build asks for first are read back on a
                    // thread while the model is lowered and resolved.
                    library.start_plans();
                    library.clone().install(model)?;
                    Some((library, recording))
                }
                // Nothing to read: prepare, when there is a cache to write
                // the snapshot into; with none, the library is built with the
                // model below, as without a key.
                None => match &cache {
                    Some(path) => {
                        model.load_library_dir(dir)?;
                        ambient::add_to(model);
                        model.record_library_cache();
                        let library = model.prepare_library()?;
                        let recorded = model.take_recorded_library_cache();
                        // The library's plans are made now, so the snapshot
                        // carries them and no later process plans the library
                        // again.
                        library.make_plans();
                        // Written while the build on the library goes on.
                        pending = save_in_background(
                            LibrarySave {
                                library: Arc::clone(&library),
                                recording: recorded.map(|recording| (recording, path.clone())),
                                snapshot: path.with_extension("prepared"),
                                key,
                            },
                            &mut warnings,
                        );
                        Some((library, path.clone()))
                    }
                    None => {
                        warnings.push(
                            "no cache directory for the standard library: none of \
                             SYSMLV2_CACHE_DIR, XDG_CACHE_HOME or HOME is set (on Windows, \
                             LOCALAPPDATA or USERPROFILE), so the library is prepared from \
                             source on every run"
                                .to_string(),
                        );
                        None
                    }
                },
            };
            if let Some((library, recording_path)) = prepared {
                if library.recording.is_none() {
                    retain(&library);
                    model.set_lazy_library_cache(recording_path.clone());
                }
                shared.lock().unwrap_or_else(|e| e.into_inner()).insert(
                    (key, model.graph_format().version()),
                    (Arc::downgrade(&library), recording_path),
                );
                return Ok(LibraryLoad {
                    pending,
                    recording_path: None,
                    warnings,
                    guessed: was_guessed,
                });
            }
        }
    }
    model.load_library_dir(dir)?;
    ambient::add_to(model);
    if let Some(path) = cache.as_ref() {
        match libcache::LibraryCache::load(path) {
            Some(cache) => model.set_library_cache(cache),
            None => model.record_library_cache(),
        }
    }
    Ok(LibraryLoad {
        pending: None,
        recording_path: cache,
        warnings,
        guessed: false,
    })
}

impl LibraryLoad {
    /// Wait for the cache writes the load started on another thread and
    /// add what could not be written to [`Self::warnings`].
    pub fn finish(&mut self) {
        if let Some(pending) = self.pending.take() {
            self.warnings.extend(pending.finish());
        }
    }
}

/// What a cold load writes for the next process: the resolution recording,
/// when the load made one, and the complete snapshot.
struct LibrarySave {
    library: Arc<PreparedLibrary>,
    recording: Option<(crate::libcache::LibraryCache, std::path::PathBuf)>,
    snapshot: std::path::PathBuf,
    key: u64,
}

impl LibrarySave {
    fn run(&self) -> Vec<String> {
        let mut warnings = Vec::new();
        if let Some((recording, path)) = &self.recording {
            if let Err(error) = recording.save(path) {
                warnings.push(unsaved_warning(path, &error));
            }
        }
        if let Err(error) = self.library.save(&self.snapshot, self.key) {
            warnings.push(unsaved_warning(&self.snapshot, &error));
        }
        warnings
    }
}

/// A cold load's cache writes, running on another thread (see
/// [`load_library_with_cache`]).
#[derive(Debug)]
pub struct PendingSave {
    #[cfg(not(target_family = "wasm"))]
    handle: Option<std::thread::JoinHandle<Vec<String>>>,
}

#[cfg(not(target_family = "wasm"))]
static PENDING_SAVES: std::sync::Mutex<Vec<std::thread::JoinHandle<Vec<String>>>> =
    std::sync::Mutex::new(Vec::new());

#[cfg(not(target_family = "wasm"))]
const SAVE_ENDED_EARLY: &str =
    "the library cache write ended early; every run will prepare the library from source";

impl PendingSave {
    /// Wait for the writes; what could not be written.
    pub fn finish(mut self) -> Vec<String> {
        self.take_warnings()
    }

    /// Leave the writes to the process: [`finish_pending_saves`] joins
    /// them. For a command that runs one verb and exits.
    #[cfg_attr(target_family = "wasm", allow(unused_mut))]
    pub fn detach(mut self) {
        #[cfg(not(target_family = "wasm"))]
        if let Some(handle) = self.handle.take() {
            PENDING_SAVES
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push(handle);
        }
    }

    fn take_warnings(&mut self) -> Vec<String> {
        #[cfg(not(target_family = "wasm"))]
        if let Some(handle) = self.handle.take() {
            return handle
                .join()
                .unwrap_or_else(|_| vec![SAVE_ENDED_EARLY.to_owned()]);
        }
        Vec::new()
    }
}

impl Drop for PendingSave {
    /// A save dropped unfinished is waited for, so the files are complete
    /// when the caller goes on; what could not be written is lost with it
    /// — finish or detach the save to be told.
    fn drop(&mut self) {
        let _ = self.take_warnings();
    }
}

/// Start the writes on a thread where the target has them, so that the
/// build on the library goes on meanwhile; where no thread can be started
/// the writes run here, their warnings into `warnings`.
fn save_in_background(save: LibrarySave, warnings: &mut Vec<String>) -> Option<PendingSave> {
    #[cfg(not(target_family = "wasm"))]
    {
        let save = Arc::new(save);
        let on_thread = Arc::clone(&save);
        if let Ok(handle) = std::thread::Builder::new()
            .name("sysmlv2-library-cache".into())
            .spawn(move || on_thread.run())
        {
            return Some(PendingSave {
                handle: Some(handle),
            });
        }
        warnings.extend(save.run());
    }
    #[cfg(target_family = "wasm")]
    warnings.extend(save.run());
    None
}

/// Wait for the library cache writes that were left to the process (see
/// [`PendingSave::detach`]) and return their warnings. A process that exits
/// without this leaves at worst a temporary file behind: every write lands
/// under its final name by a rename.
pub fn finish_pending_saves() -> Vec<String> {
    #[cfg(not(target_family = "wasm"))]
    {
        let handles: Vec<_> =
            std::mem::take(&mut *PENDING_SAVES.lock().unwrap_or_else(|e| e.into_inner()));
        handles
            .into_iter()
            .flat_map(|handle| {
                handle
                    .join()
                    .unwrap_or_else(|_| vec![SAVE_ENDED_EARLY.to_owned()])
            })
            .collect()
    }
    #[cfg(target_family = "wasm")]
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json::ResolvedModel;

    /// The cache directory's one snapshot is decoded while the library
    /// directory's key is computed and kept when the key agrees; a snapshot
    /// of another library, or two to choose from, is not taken, and the load
    /// reads what the key names as before.
    #[test]
    fn the_caches_one_snapshot_is_decoded_while_the_key_is_computed() {
        let root = std::env::temp_dir().join(format!("sysmlv2-guess-{}", std::process::id()));
        let lib = root.join("lib");
        let cache = root.join("cache");
        std::fs::create_dir_all(&lib).unwrap();
        std::fs::create_dir_all(&cache).unwrap();
        std::fs::write(
            lib.join("lib.sysml"),
            "standard library package L { part def A; }",
        )
        .unwrap();
        let snapshots = || {
            std::fs::read_dir(&cache)
                .unwrap()
                .flatten()
                .filter(|entry| entry.path().extension().is_some_and(|x| x == "prepared"))
                .count()
        };
        // Nothing to guess from: the load prepares and writes the snapshot.
        let mut cold = Model::new();
        let mut load = load_library_with_cache_in(&mut cold, &lib, Some(&cache)).unwrap();
        load.finish();
        assert!(!load.guessed);
        assert_eq!(snapshots(), 1);
        drop((load, cold));
        // The one snapshot is guessed and kept.
        let mut warm = Model::new();
        let load = load_library_with_cache_in(&mut warm, &lib, Some(&cache)).unwrap();
        assert!(
            load.guessed,
            "the one snapshot was decoded while the key was computed"
        );
        assert_eq!(warm.loaded_library_unit_count(), 0, "installed as prepared");
        drop((load, warm));
        // The library changed: the guess is of another key and is dropped; the
        // load prepares and writes a second snapshot.
        std::fs::write(
            lib.join("lib.sysml"),
            "standard library package L { part def A; part def B; }",
        )
        .unwrap();
        let mut changed = Model::new();
        let mut load = load_library_with_cache_in(&mut changed, &lib, Some(&cache)).unwrap();
        load.finish();
        assert!(!load.guessed);
        assert_eq!(snapshots(), 2);
        drop((load, changed));
        // Two snapshots: nothing is guessed; the load reads the one the key names.
        let mut two = Model::new();
        let load = load_library_with_cache_in(&mut two, &lib, Some(&cache)).unwrap();
        assert!(!load.guessed);
        assert_eq!(two.loaded_library_unit_count(), 0, "installed as prepared");
        std::fs::remove_dir_all(root).unwrap();
    }

    /// A library whose last session closed is kept by the process, so the
    /// next load of its directory is served by the registry: nothing is
    /// read, and the one snapshot in the cache is not even guessed. Once
    /// released, the next load reads the snapshot again.
    #[test]
    fn a_retained_library_serves_the_next_load_after_its_session_closed() {
        let root = std::env::temp_dir().join(format!("sysmlv2-retain-{}", uuid::Uuid::new_v4()));
        let lib = root.join("lib");
        let cache = root.join("cache");
        std::fs::create_dir_all(&lib).unwrap();
        std::fs::create_dir_all(&cache).unwrap();
        std::fs::write(
            lib.join("lib.sysml"),
            "standard library package L { part def A; part def B :> A; }",
        )
        .unwrap();
        // Prepared from source: the handle carries its units and is not kept.
        let mut first = Model::new();
        let mut load = load_library_with_cache_in(&mut first, &lib, Some(&cache)).unwrap();
        load.finish();
        assert!(!load.guessed);
        drop((load, first));
        // Decoded from the one snapshot (guessed), and kept.
        let mut decoded = Model::new();
        let load = load_library_with_cache_in(&mut decoded, &lib, Some(&cache)).unwrap();
        assert!(load.guessed);
        assert_eq!(decoded.loaded_library_unit_count(), 0);
        drop((load, decoded));
        // Served by the registry: a prepared install that read no snapshot
        // (with one snapshot in the cache, a read would have been a guess).
        let mut next = Model::new();
        let load = load_library_with_cache_in(&mut next, &lib, Some(&cache)).unwrap();
        assert!(!load.guessed, "the retained library was served, not read");
        assert_eq!(next.loaded_library_unit_count(), 0, "installed as prepared");
        assert_eq!(next.lib_cache_kind(), "lazy");
        drop((load, next));
        // Released: once nothing else holds the handle (reading its plans
        // back on a thread holds it until the plans are made), the next load
        // reads the one snapshot, guessed as before.
        release_retained_libraries();
        let key = crate::ambient::mix_key(crate::libcache::hash_library_dir(&lib).unwrap());
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while SHARED.get().is_some_and(|shared| {
            shared
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .iter()
                .any(|((held, _), (library, _))| *held == key && library.strong_count() > 0)
        }) {
            assert!(
                std::time::Instant::now() < deadline,
                "the retained handle is released"
            );
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        let mut again = Model::new();
        let load = load_library_with_cache_in(&mut again, &lib, Some(&cache)).unwrap();
        assert!(load.guessed, "nothing retained: the snapshot was read");
        assert_eq!(again.loaded_library_unit_count(), 0);
        std::fs::remove_dir_all(root).unwrap();
    }

    /// With the cache on but no directory to keep it in, the load says so
    /// (and prepares the library with the model, as before).
    #[test]
    fn a_load_without_a_cache_directory_says_so() {
        let root = std::env::temp_dir().join(format!("sysmlv2-nocache-{}", uuid::Uuid::new_v4()));
        let lib = root.join("lib");
        std::fs::create_dir_all(&lib).unwrap();
        std::fs::write(
            lib.join("lib.sysml"),
            "standard library package L { part def A; }",
        )
        .unwrap();
        let mut model = Model::new();
        let load = load_library_with_cache_in(&mut model, &lib, None).unwrap();
        assert!(
            load.warnings
                .iter()
                .any(|w| w.contains("no cache directory")),
            "{:?}",
            load.warnings
        );
        assert!(load.pending.is_none() && load.recording_path.is_none());
        assert!(
            model.loaded_library_unit_count() > 0,
            "built with the model"
        );
        std::fs::remove_dir_all(root).unwrap();
    }

    /// A prepared library carries its elements' implied relationships and
    /// owned results as the last rows of its prefix, with its own ownership
    /// view, and a snapshot carries them too. A build on it lists none of
    /// them among the user elements, reads what they derive — the type a
    /// user expression's result takes through a library enumeration
    /// literal's implied typing — and materializes rows of its own
    /// elements only.
    #[test]
    fn a_prepared_library_carries_its_own_semantic_rows() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.sysml",
            "standard library package L { enum def K { a; b; } part def P { attribute x : K; } }",
        );
        let prepared = base.prepare_library().unwrap();
        let b = &prepared.builder;
        assert!(
            b.carries_semantic_rows(),
            "materialized rows {}..{}",
            b.lib_implied_from,
            b.lib_boundary
        );
        assert_eq!(b.lib_boundary, b.elements.len(), "the rows end the prefix");
        // The library's own export lists its source rows alone, as it did
        // before it was prepared (the model now builds on the prepared
        // library).
        let exported = crate::json::library_to_compact_json(&base);
        let mut fresh = Model::new();
        fresh.add_library_source(
            "lib.sysml",
            "standard library package L { enum def K { a; b; } part def P { attribute x : K; } }",
        );
        assert_eq!(exported, crate::json::library_to_compact_json(&fresh));
        // The library's check facts are its source rows' only, as a build
        // from source has them: the materialized rows add no edge.
        let facts = prepared.facts.get().expect("the library's facts");
        let mut source = crate::json::ResolvedModel::build(&fresh);
        let expected = source.b.facts();
        for e in 0..b.lib_implied_from {
            assert_eq!(facts.supers[e], expected.supers[e], "row {e}");
        }
        let bytes = prepared.to_bytes(5).unwrap();
        let decoded = PreparedLibrary::from_bytes(&bytes, 5).expect("the snapshot decodes");
        assert_eq!(decoded.builder.lib_implied_from, b.lib_implied_from);
        assert_eq!(decoded.builder.lib_boundary, b.lib_boundary);
        assert!(
            decoded.builder.carries_semantic_rows(),
            "carried by the snapshot"
        );

        for library in [prepared, Arc::new(decoded)] {
            // The frozen rows by id cover the materialized rows, in the
            // preparing process and from a snapshot alike.
            let b = &library.builder;
            let ids = b.prefix_ids.as_ref().expect("the frozen rows by id");
            for i in b.lib_implied_from..b.lib_boundary {
                assert_eq!(ids.get(&b.elem_id(i)), Some(&i), "row {i} by id");
            }
            let mut model = Model::new();
            library.install(&mut model).unwrap();
            model.add_source(
                "user.sysml",
                "package U { part p : L::P { attribute :>> x = L::K::a; } }",
            );
            let mut r = crate::json::ResolvedModel::build(&model);
            assert!(r.b.library_facts.is_some(), "the prepared path");
            assert!(
                r.user_elements().all(|e| e.0 >= r.b.lib_boundary),
                "no library row among the user elements"
            );
            let k = r.resolve_qualified("L::K").expect("the enumeration");
            let k = r.element_id(k).to_string();
            let full = crate::full::model_to_full_json(&model);
            let result = full
                .as_array()
                .unwrap()
                .iter()
                .find(|e| e["name"] == "result" && e["@type"] == "Feature")
                .expect("the expression's owned result");
            assert!(
                result["type"]
                    .as_array()
                    .is_some_and(|types| types.iter().any(|t| t["@id"] == k)),
                "the result takes the literal's enumeration as a type: {}",
                result["type"]
            );
            // Only the build's own rows are materialized (a derived read of a
            // usage materializes them): every one is anchored at a user
            // element.
            let usage = r.resolve_qualified("U::p").expect("the part usage");
            let _ = r.property(usage, "ownedSpecialization");
            assert!(r.b.explicit_len() < r.b.elements.len(), "rows of its own");
            for i in r.b.explicit_len()..r.b.elements.len() {
                assert!(
                    !r.is_library_element(crate::json::ElementRef(i)),
                    "row {i} is the library's"
                );
            }
        }
    }

    /// The dynamic planner validates the library's specialization rows
    /// once per prepared library: the first session's planning keeps the
    /// validation with the prefix, the next session's reads it, and both
    /// answer the same.
    #[test]
    fn the_librarys_rows_are_validated_once_for_every_session_on_it() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.sysml",
            "standard library package L { enum def K { a; b; } \
                part def P { attribute x : K; } part def Q :> P { attribute :>> x; } \
                calc def F { in p : P; return r : K; } }",
        );
        let prepared = base.prepare_library().unwrap();
        assert!(prepared.builder.carries_semantic_rows());
        let floor = prepared.builder.lib_implied_from;
        assert!(
            prepared.builder.prefix_validation.get().is_none(),
            "nothing validated before a session plans"
        );
        let mut answers = Vec::new();
        for _ in 0..2 {
            let mut model = Model::new();
            Arc::clone(&prepared).install(&mut model).unwrap();
            model.add_source(
                "user.sysml",
                "package U { part q : L::Q { attribute :>> x = L::K::b; } \
                    attribute k : L::K = L::F(q); }",
            );
            let mut r = crate::json::ResolvedModel::build(&model);
            let usage = r.resolve_qualified("U::k").expect("the attribute usage");
            answers.push((
                r.property(usage, "ownedSpecialization")
                    .map(|v| v.to_string()),
                r.property(usage, "type").map(|v| v.to_string()),
            ));
            let kept =
                r.b.prefix_validation
                    .get()
                    .expect("the session's planning kept the library's validation");
            assert_eq!(
                kept.rows(),
                floor,
                "the frozen rows below the library's own"
            );
            assert!(
                Arc::ptr_eq(&r.b.prefix_validation, &prepared.builder.prefix_validation),
                "the cell is the library's"
            );
        }
        assert_eq!(
            answers[0], answers[1],
            "the second session answers as the first"
        );
        assert!(answers[0].0.is_ok(), "{:?}", answers[0].0);
    }

    /// A chunk feed over `bytes`, `step` bytes at a time at most.
    fn feed(bytes: &[u8], step: usize) -> impl FnMut(&mut [u8]) -> usize + '_ {
        let mut at = 0;
        move |buf: &mut [u8]| {
            let n = buf.len().min(step).min(bytes.len() - at);
            buf[..n].copy_from_slice(&bytes[at..at + n]);
            at += n;
            n
        }
    }

    /// Plans started on a thread when a snapshot is decoded are the plans the
    /// first request gets, equal to the ones made in line; a snapshot written
    /// from either handle carries the same plans.
    #[test]
    fn plans_started_on_a_thread_equal_the_plans_made_in_line() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.sysml",
            "standard library package L { part def A; part def B :> A; part b : B; }",
        );
        let library = base.prepare_library().unwrap();
        library.make_plans();
        let bytes = library.to_bytes(5).unwrap();
        let in_line = Arc::new(PreparedLibrary::from_bytes(&bytes, 5).unwrap());
        let started = Arc::new(PreparedLibrary::from_bytes(&bytes, 5).unwrap());
        assert!(in_line.carries_plans() && started.carries_plans());
        started.start_plans();
        // Starting twice starts nothing more; a request takes what the thread made.
        started.start_plans();
        let wire = |plans: Option<Arc<crate::json::LibraryPlans>>| {
            plans
                .and_then(|plans| plans.to_wire())
                .map(|wire| crate::cache_codec::encode(&wire).unwrap())
        };
        let expected = wire(in_line.library_plans());
        assert!(expected.is_some(), "the fixture has plans to carry");
        assert_eq!(wire(started.library_plans()), expected);
        // The started handle writes the plans it made where the in-line
        // handle writes the ones it still carries.
        let again = Arc::new(PreparedLibrary::from_bytes(&bytes, 5).unwrap());
        again.start_plans();
        assert_eq!(again.to_bytes(5).unwrap(), in_line.to_bytes(5).unwrap());
    }

    /// The same library prepared twice in one process encodes to the same
    /// bytes: every set and map a snapshot carries is written in a fixed
    /// order, whatever order its table happens to hold, so two snapshots of
    /// one library can be compared byte for byte. The fixture fills the
    /// tables whose order is otherwise the hasher's where a small library
    /// can: the builder's default values, flows and executable
    /// calculations (asserted non-empty), and one scope's many redefined
    /// names. The ownership view's additions and results are empty in a
    /// library this small, and are covered only by two runs of the
    /// standard-library generator comparing equal.
    #[test]
    fn the_same_library_prepared_twice_encodes_to_the_same_bytes() {
        use std::fmt::Write as _;
        let mut source = String::from("standard library package L {\n");
        source.push_str("  part def A {\n");
        for i in 0..40 {
            writeln!(source, "    attribute a{i} default {i};").unwrap();
        }
        source.push_str("  }\n  part def B :> A {\n");
        for i in 0..40 {
            writeln!(source, "    attribute :>> a{i} = {};", i + 1).unwrap();
        }
        // One feature redefining many: its body scope's redefined names.
        source.push_str("    attribute x redefines ");
        for i in 0..40 {
            if i > 0 {
                source.push_str(", ");
            }
            write!(source, "a{i}").unwrap();
        }
        source.push_str(" { attribute y; }\n");
        source.push_str("  }\n");
        for i in 0..12 {
            // An action in a calculation's body makes it executable.
            writeln!(source, "  calc def C{i} {{ action s{i}; {i} + 1 }}").unwrap();
            writeln!(
                source,
                "  part def F{i} {{ part x {{ attribute v; }} part y {{ attribute w; }} flow from x.v to y.w; }}"
            )
            .unwrap();
        }
        source.push_str("}\n");
        let encode = || {
            let mut model = Model::new();
            model.add_library_source("lib.sysml", &source);
            let library = model.prepare_library().unwrap();
            let builder = &library.builder;
            assert!(
                builder.default_values.len() >= 40
                    && builder.payload_flows.len() >= 12
                    && builder.executable_calculations.len() >= 12,
                "the fixture fills the builder's sets"
            );
            library.make_plans();
            library.to_bytes(8).unwrap()
        };
        let first = encode();
        let second = encode();
        if first != second {
            let (parts, _) = header_parts(&first, 8).expect("the header reads back");
            let (others, _) = header_parts(&second, 8).expect("the header reads back");
            let differing: Vec<usize> = (0..PARTS)
                .filter(|&i| parts[i].len != others[i].len || parts[i].sum != others[i].sum)
                .collect();
            panic!("two preparations of one library differ in parts {differing:?}");
        }
    }

    /// Each part of a snapshot is verified against a checksum of its own: a
    /// byte changed anywhere in any part is refused by both readers, as is a
    /// snapshot whose parts do not add up to its payload.
    #[test]
    fn each_part_is_verified_against_its_own_checksum() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.sysml",
            "standard library package L { part def A; part def B :> A; part b : B; }",
        );
        let library = base.prepare_library().unwrap();
        library.make_plans();
        let bytes = library.to_bytes(6).unwrap();
        let (parts, payload) = header_parts(&bytes, 6).expect("the header reads back");
        assert!(PreparedLibrary::from_bytes(&bytes, 6).is_some());
        assert!(header_parts(&bytes, 7).is_none(), "another library's key");
        let mut start = bytes.len() - payload.len();
        for (i, part) in parts.iter().enumerate() {
            assert!(
                part.len > 0,
                "part {i} is written even when its record is absent"
            );
            let mut corrupt = bytes.clone();
            corrupt[start + part.len / 2] ^= 0x55;
            assert!(
                PreparedLibrary::from_bytes(&corrupt, 6).is_none(),
                "part {i} changed in place is refused"
            );
            assert!(
                PreparedLibrary::from_chunks(corrupt.len(), feed(&corrupt, 1000), 6).is_none(),
                "part {i} changed is refused when fed in chunks"
            );
            start += part.len;
        }
        let mut short = bytes.clone();
        short.truncate(bytes.len() - 1);
        assert!(PreparedLibrary::from_bytes(&short, 6).is_none());
        assert!(PreparedLibrary::from_chunks(short.len(), feed(&short, 1000), 6).is_none());
        let mut long = bytes.clone();
        long.push(0);
        assert!(PreparedLibrary::from_bytes(&long, 6).is_none());
        assert!(PreparedLibrary::from_chunks(long.len(), feed(&long, 1000), 6).is_none());
    }
    /// What a host ships with the library rides its snapshot: decoded with
    /// its hosts' parts kept — the snapshot held whole, fed in chunks, or
    /// loaded from a file — it is read back as it was carried, once — a
    /// value longer than a run of the snapshot's included — and a snapshot
    /// written from the handle after that no longer carries it. A tag never
    /// carried, or a value read back as another type, answers nothing.
    #[test]
    fn a_host_part_rides_the_snapshot_and_is_read_back_once() {
        let mut base = Model::new();
        base.add_library_source("lib.sysml", "standard library package L { part def A; }");
        let library = base.prepare_library().unwrap();
        let value: (u32, Vec<String>, String) = (
            7,
            vec!["A".into(), "L::A".into()],
            "x".repeat(3 * HOST_CHUNK + 5),
        );
        library.carry_host_part("table", &value).unwrap();
        library.carry_host_part("other", &1u8).unwrap();
        let bytes = library.to_bytes(4).unwrap();
        let dir = std::env::temp_dir().join(format!("sysmlv2-host-part-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("stdlib-0000000000000004.prepared");
        library.save(&path, 4).unwrap();
        let decoded = [
            PreparedLibrary::from_bytes_with(&bytes, 4, true).unwrap(),
            PreparedLibrary::from_chunks_with(bytes.len(), feed(&bytes, 1000), 4, true).unwrap(),
            PreparedLibrary::load_with(&path, 4, true).unwrap(),
        ];
        for handle in &decoded {
            assert_eq!(
                handle.take_host_part::<String>("other"),
                None,
                "another type"
            );
            assert_eq!(
                handle.take_host_part::<(u32, Vec<String>, String)>("missing"),
                None
            );
            assert_eq!(handle.take_host_part("table"), Some(value.clone()));
            assert_eq!(
                handle.take_host_part::<(u32, Vec<String>, String)>("table"),
                None
            );
            let again =
                PreparedLibrary::from_bytes_with(&handle.to_bytes(4).unwrap(), 4, true).unwrap();
            assert_eq!(
                again.take_host_part::<(u32, Vec<String>, String)>("table"),
                None
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A decode that does not ask to keep the hosts' parts — the snapshot
    /// held whole, fed in chunks, or loaded from a file — holds none of
    /// them, and a snapshot written from it carries none; it still verifies
    /// them, so a damaged part refuses the snapshot whether the decode
    /// keeps the parts or not.
    #[test]
    fn a_decode_drops_the_hosts_parts_unless_asked_and_still_verifies_them() {
        let mut base = Model::new();
        base.add_library_source("lib.sysml", "standard library package L { part def A; }");
        let library = base.prepare_library().unwrap();
        let value = "x".repeat(3 * HOST_CHUNK + 5);
        library.carry_host_part("table", &value).unwrap();
        let bytes = library.to_bytes(4).unwrap();
        let dir = std::env::temp_dir().join(format!("sysmlv2-host-drop-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("stdlib-0000000000000004.prepared");
        library.save(&path, 4).unwrap();
        let dropped = [
            PreparedLibrary::from_bytes(&bytes, 4).unwrap(),
            PreparedLibrary::from_chunks(bytes.len(), feed(&bytes, 1000), 4).unwrap(),
            PreparedLibrary::load(&path, 4).unwrap(),
        ];
        for handle in &dropped {
            assert!(handle.hosts.lock().unwrap().0.is_empty(), "nothing held");
            assert_eq!(handle.take_host_part::<String>("table"), None);
            let again =
                PreparedLibrary::from_bytes_with(&handle.to_bytes(4).unwrap(), 4, true).unwrap();
            assert_eq!(again.take_host_part::<String>("table"), None);
        }
        let corrupt = super::apart_tests::corrupt_bytes(&path, 4, HOSTS_PART);
        let corrupt_path = super::apart_tests::corrupted(&path, 4, HOSTS_PART);
        for keep in [false, true] {
            assert!(PreparedLibrary::from_bytes_with(&corrupt, 4, keep).is_none());
            assert!(
                PreparedLibrary::from_chunks_with(corrupt.len(), feed(&corrupt, 1000), 4, keep)
                    .is_none()
            );
            assert!(PreparedLibrary::load_with(&corrupt_path, 4, keep).is_none());
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A library prepared while recording, or with a snapshot the preparing
    /// build rejects as stale, keeps a recording; a build that must resolve
    /// the library together with user units arms it, validates it and
    /// replays it, and equals a cold build in both graphs. A decoded handle
    /// has none, a lazy cache slot the loader set is left alone, and a model
    /// that gains a library unit after installing builds without the handle.
    #[test]
    fn joint_builds_replay_the_recording_the_library_was_prepared_with() {
        let library = "package L { part def A; part def B :> A; }";
        // `Parts` is a root name the library looked up and missed.
        let user = "package Parts; package U { part a : L::A; part b : L::B; }";
        let graphs = |model: &Model| {
            (
                crate::json::model_to_compact_json(model),
                crate::json::library_to_compact_json(model),
            )
        };
        let mut cold = Model::new();
        cold.add_library_source("lib.sysml", library);
        cold.add_source("user.sysml", user);
        let cold = graphs(&cold);
        // A snapshot of another library decodes but fails the build's
        // validation, so the preparing build records in its place.
        let mut other = Model::new();
        other.add_library_source("lib.sysml", "package L { part def A; }");
        other.record_library_cache();
        let _ = ResolvedModel::build(&other);
        let stale = other.take_recorded_library_cache().unwrap();
        let mut prepared = None;
        for (label, snapshot) in [
            ("recording while preparing", None),
            ("rejecting a stale snapshot", Some(stale)),
        ] {
            let mut base = Model::new();
            base.add_library_source("lib.sysml", library);
            match snapshot {
                Some(cache) => base.set_library_cache(cache),
                None => base.record_library_cache(),
            }
            let library = base.prepare_library().unwrap();
            assert!(library.recording.is_some(), "{label}: preparing recorded");
            let mut warm = Model::new();
            Arc::clone(&library).install(&mut warm).unwrap();
            assert_eq!(
                warm.lib_cache_kind(),
                "off",
                "{label}: installing arms nothing"
            );
            warm.add_source("user.sysml", user);
            let r = ResolvedModel::build(&warm);
            assert!(r.b.library_facts.is_none(), "{label}: resolved jointly");
            assert_eq!(
                warm.lib_cache_kind(),
                "use",
                "{label}: the joint build armed the recording and it validated"
            );
            assert_eq!(
                graphs(&warm),
                cold,
                "{label}: both graphs equal a cold build's"
            );
            prepared = Some(library);
        }
        let prepared = prepared.unwrap();
        // A decoded prepared snapshot carries no recording; its joint builds
        // resolve the library cold.
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(9).unwrap(), 9).unwrap());
        assert!(decoded.recording.is_none());
        let mut fresh = Model::new();
        decoded.install(&mut fresh).unwrap();
        fresh.add_source("user.sysml", user);
        assert!(ResolvedModel::build(&fresh).b.library_facts.is_none());
        assert_eq!(fresh.lib_cache_kind(), "off", "nothing to arm");
        assert_eq!(graphs(&fresh), cold);
        // The same snapshot fed in chunks decodes to the same library; a
        // window narrower than any item still works, and the refusals match.
        {
            let bytes = prepared.to_bytes(9).unwrap();
            fn feed(bytes: &[u8], step: usize) -> impl FnMut(&mut [u8]) -> usize + '_ {
                let mut at = 0;
                move |buf: &mut [u8]| {
                    let n = buf.len().min(step).min(bytes.len() - at);
                    buf[..n].copy_from_slice(&bytes[at..at + n]);
                    at += n;
                    n
                }
            }
            for step in [1, 1000, usize::MAX] {
                let chunked = Arc::new(
                    PreparedLibrary::from_chunks(bytes.len(), feed(&bytes, step), 9).unwrap(),
                );
                let mut m = Model::new();
                chunked.install(&mut m).unwrap();
                m.add_source("user.sysml", user);
                assert_eq!(graphs(&m), cold, "step {step}");
            }
            assert!(
                PreparedLibrary::from_chunks(bytes.len(), feed(&bytes, 1000), 8).is_none(),
                "other key"
            );
            assert!(
                PreparedLibrary::from_chunks(
                    bytes.len() - 1,
                    feed(&bytes[..bytes.len() - 1], 1000),
                    9
                )
                .is_none(),
                "truncated"
            );
            let mut corrupt = bytes.clone();
            let last = corrupt.len() - 1;
            corrupt[last] ^= 0xff;
            assert!(
                PreparedLibrary::from_chunks(corrupt.len(), feed(&corrupt, 1000), 9).is_none(),
                "corrupt"
            );
        }
        // A decoded handle holding the encoded recording arms the lazy slot
        // on install; the joint build decodes and replays it, and a prepared
        // build never touches it.
        let recording_bytes = prepared.recording.as_ref().unwrap().to_bytes();
        let held = Arc::new(
            PreparedLibrary::from_bytes(&prepared.to_bytes(9).unwrap(), 9)
                .unwrap()
                .with_lazy_recording(recording_bytes),
        );
        assert!(held.recording.is_none() && held.lazy_recording.is_some());
        let mut plain = Model::new();
        held.clone().install(&mut plain).unwrap();
        assert_eq!(
            plain.lib_cache_kind(),
            "lazy",
            "installing arms the held recording"
        );
        plain.add_source("user.sysml", "package U { part a : L::A; }");
        assert!(
            ResolvedModel::build(&plain).b.library_facts.is_some(),
            "prepared build"
        );
        assert_eq!(
            plain.lib_cache_kind(),
            "lazy",
            "a prepared build leaves it encoded"
        );
        let mut joint = Model::new();
        held.install(&mut joint).unwrap();
        joint.add_source("user.sysml", user);
        assert!(
            ResolvedModel::build(&joint).b.library_facts.is_none(),
            "resolved jointly"
        );
        assert_eq!(
            joint.lib_cache_kind(),
            "use",
            "the joint build decoded and replayed it"
        );
        assert_eq!(graphs(&joint), cold);
        // A lazy cache slot the directory loader set stays in place.
        let mut lazy = Model::new();
        Arc::clone(&prepared).install(&mut lazy).unwrap();
        lazy.set_lazy_library_cache(std::path::PathBuf::from("/nonexistent/stdlib.libcache"));
        lazy.add_source("user.sysml", user);
        assert!(ResolvedModel::build(&lazy).b.library_facts.is_none());
        assert_eq!(
            lazy.lib_cache_kind(),
            "off",
            "the lazy slot, not the recording, was consulted"
        );
        assert_eq!(graphs(&lazy), cold);
        // A library unit added after installing drops the prepared library
        // and with it the recording: no sealed-id lowering to throw away.
        let more = "package More { part def C; }";
        let mut grown = Model::new();
        prepared.install(&mut grown).unwrap();
        grown.add_library_source("more.sysml", more);
        grown.add_source("user.sysml", user);
        assert!(ResolvedModel::build(&grown).b.library_facts.is_none());
        assert_eq!(grown.lib_cache_kind(), "off");
        let mut both = Model::new();
        both.add_library_source("lib.sysml", library);
        both.add_library_source("more.sysml", more);
        both.add_source("user.sysml", user);
        assert_eq!(graphs(&grown), graphs(&both));
    }
    /// A user root declaration named like a library root declaration keeps
    /// the prepared build while every root lookup of the name still selects
    /// what the library's own bindings select — a kind that does not
    /// overlap the library's, the referential warning's "references
    /// resolve to the library" — and resolves jointly once a lookup would
    /// select otherwise: a same-kind declaration makes the name ambiguous,
    /// a library type whose own base lookup excludes itself would select
    /// the user's declaration in its place even though the warning reports
    /// the library, and a user declaration or alias stands in front of, or
    /// merges into, a library root alias of its name, which the warning
    /// does not see; a user alias of a name no library lookup can miss is
    /// never read. Either way the graphs equal a cold build's.
    #[test]
    fn root_shadowing_resolves_jointly_only_when_a_root_lookup_changes() {
        let graphs = |model: &Model| {
            (
                crate::json::model_to_compact_json(model),
                crate::json::library_to_compact_json(model),
            )
        };
        for (library, user, joint, resolves_to_library) in [
            // A package by short name beside a standard library package:
            // the kinds do not overlap, and `L::A` reaches the library.
            (
                "standard library package L { part def A; part def B :> A; }",
                "package <L> 'User L' { part def C; } package U { part a : L::A; part b : L::B; }",
                false,
                Some(true),
            ),
            // A part definition beside a library package: the same.
            (
                "package L { part def A; part def B :> A; }",
                "part def L; package U { part a : L::A; part b : L::B; }",
                false,
                Some(true),
            ),
            // A package beside a package: the name is ambiguous.
            (
                "package L { part def A; part def B :> A; }",
                "package L { part def C; } package U { part a : L::A; }",
                true,
                Some(false),
            ),
            // A private package too: ambiguous to the lookups that admit it.
            (
                "package L { part def A; part def B :> A; }",
                "private package L { part def C; } package U { part a : L::A; }",
                true,
                Some(false),
            ),
            // A library type whose base is its own name through a root
            // import: with the type excluded, the lookup selects the user's
            // package in place of the import's, and `y : Z` resolves no
            // more — though the warning, which excludes nothing, reports
            // the library.
            (
                "package Other { part def L { part def Z; } } private import Other::*; \
                 part def L :> L { part y : Z; }",
                "package <L> 'My L' { part def C; }",
                true,
                Some(true),
            ),
            // A library root alias: the library's `x : L` read it where no
            // declaration of the name was bound, and the user's now is —
            // no collision the warning can report.
            (
                "package Other { part def L; } alias L for Other::L; package P { part x : L; }",
                "part def L;",
                true,
                None,
            ),
            // A user root alias beside it: two aliases of one spelling make
            // the read ambiguous.
            (
                "package Other { part def L; } alias L for Other::L; package P { part x : L; }",
                "alias L for Other::L;",
                true,
                None,
            ),
            // A user root alias beside a standard library package: no
            // lookup of the name can miss the package, so the alias is
            // never read, and `L::A` reaches the library.
            (
                "standard library package L { part def A; }",
                "package U { part def M; } alias L for U::M; package V { part a : L::A; }",
                false,
                None,
            ),
        ] {
            let mut cold = Model::new();
            cold.add_library_source("lib.sysml", library);
            cold.add_source("user.sysml", user);
            let cold = graphs(&cold);
            let mut base = Model::new();
            base.add_library_source("lib.sysml", library);
            let prepared = base.prepare_library().unwrap();
            let mut warm = Model::new();
            prepared.install(&mut warm).unwrap();
            warm.add_source("user.sysml", user);
            let r = ResolvedModel::build(&warm);
            assert_eq!(
                r.b.library_facts.is_none(),
                joint,
                "{user}: resolved jointly"
            );
            assert_eq!(graphs(&warm), cold, "{user}: equals a cold build");
            let report = crate::json::model_resolution_report(&warm);
            let verdicts: Vec<(&str, bool)> = report
                .shadowed_roots
                .iter()
                .map(|s| (s.name.as_str(), s.resolves_to_library))
                .collect();
            let expected: Vec<(&str, bool)> =
                resolves_to_library.map(|v| ("L", v)).into_iter().collect();
            assert_eq!(verdicts, expected, "{user}: the warning's verdict");
        }
    }

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
            "package MeasurementReferences { datatype MeasurementUnit; } package L { datatype A; datatype B; feature f : A; }",
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
            // Imports the imported namespace does not re-export.
            "package Q { private import L::*; part def Y; } private import Q::*; package U { part a : L::A; }",
            "package Q { protected import L::*; } private import Q::**; package U { part a : L::A; }",
        ] {
            same_graphs(&complete, ("user.sysml", source), true);
        }
        for source in [
            // A user namespace re-exporting through its own import, an
            // alias target, and a recursive import reaching a probed name.
            "package Q { public import L::*; } private import Q::*; package U { part a : A; }",
            "package Q { private import L::*; } private import all Q::*; package U { part a : A; }",
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
        let mut load = load_library_with_cache_at(
            &mut model,
            &dir,
            Some((7, blocked.join("stdlib.libcache"))),
        )
        .unwrap();
        assert!(model.unit_count() > 0, "the library still loaded");
        load.finish();
        assert_eq!(load.warnings.len(), 2, "{:?}", load.warnings);
        for warning in &load.warnings {
            assert!(
                warning.contains("could not save the library cache at"),
                "{warning}"
            );
        }
        std::fs::remove_dir_all(&root).ok();
    }

    /// A snapshot written ahead of time into a directory is read from there
    /// by a load whose cache has none, without copying it into the cache;
    /// one that does not decode is passed over and the library prepared.
    #[test]
    fn a_shipped_snapshot_is_read_in_place() {
        let root = std::env::temp_dir().join(format!("sysml-shipped-{}", uuid::Uuid::new_v4()));
        let dir = root.join("lib");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("Lib.sysml"),
            "library package L { part def A; part def B :> A { attribute a : ScalarValues::Real; } }",
        )
        .unwrap();
        let shipped = prepare_library_into(&dir, &root.join("shipped")).unwrap();
        assert!(shipped.snapshot.exists());
        let recording = shipped.recording.clone().expect("the preparation recorded");
        assert!(recording.exists());
        let key = crate::ambient::mix_key(crate::libcache::hash_library_dir(&dir).unwrap());
        assert_eq!(
            shipped.snapshot.file_name().unwrap().to_str().unwrap(),
            format!("stdlib-{key:016x}.prepared")
        );
        let mut cold = Model::new();
        cold.load_library_dir(&dir).unwrap();
        crate::ambient::add_to(&mut cold);
        let expected = crate::json::library_to_compact_json(&cold);

        let cache = root.join("cache").join("stdlib.libcache");
        let mut model = Model::new();
        let load = load_library_with_cache_from(
            &mut model,
            &dir,
            Some(key),
            Some(cache.clone()),
            std::slice::from_ref(&recording),
        )
        .unwrap();
        assert!(
            load.pending.is_none() && load.warnings.is_empty(),
            "{:?}",
            load.warnings
        );
        assert_eq!(model.loaded_library_unit_count(), 0, "decoded, not parsed");
        assert_eq!(model.lib_cache_kind(), "lazy");
        assert_eq!(crate::json::library_to_compact_json(&model), expected);
        assert!(
            !cache.with_extension("prepared").exists() && !cache.exists(),
            "read in place, nothing copied into the cache"
        );
        // A second model in the same process installs the shared handle and
        // reads the shipped recording lazily too.
        let mut second = Model::new();
        load_library_with_cache_from(
            &mut second,
            &dir,
            Some(key),
            Some(cache.clone()),
            std::slice::from_ref(&recording),
        )
        .unwrap();
        assert_eq!(second.loaded_library_unit_count(), 0);
        assert_eq!(second.lib_cache_kind(), "lazy");
        drop(second);
        // A run with a key and no cache directory reads the shipped snapshot
        // as well, and writes nothing.
        let mut nowhere = Model::new();
        let load = load_library_with_cache_from(
            &mut nowhere,
            &dir,
            Some(key),
            None,
            std::slice::from_ref(&recording),
        )
        .unwrap();
        assert!(load.pending.is_none() && load.warnings.is_empty());
        assert_eq!(
            nowhere.loaded_library_unit_count(),
            0,
            "decoded, not parsed"
        );
        assert_eq!(crate::json::library_to_compact_json(&nowhere), expected);
        drop(nowhere);

        // A shipped snapshot that does not decode is passed over. The first
        // handle is dropped first: while it lives, a load of the same key in
        // this process installs it from memory and reads nothing. The thread
        // reading its plans back holds it too, until the plans are made.
        drop(model);
        release_retained_libraries();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while SHARED.get().is_some_and(|shared| {
            shared
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .iter()
                .any(|((held, _), (library, _))| *held == key && library.strong_count() > 0)
        }) {
            assert!(
                std::time::Instant::now() < deadline,
                "the first handle is released"
            );
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        std::fs::write(&shipped.snapshot, b"not a snapshot").unwrap();
        let mut again = Model::new();
        let mut load = load_library_with_cache_from(
            &mut again,
            &dir,
            Some(key),
            Some(cache.clone()),
            std::slice::from_ref(&recording),
        )
        .unwrap();
        load.finish();
        assert!(load.warnings.is_empty(), "{:?}", load.warnings);
        assert!(
            again.loaded_library_unit_count() > 0,
            "prepared from source"
        );
        assert!(
            cache.with_extension("prepared").exists(),
            "and written into the cache"
        );
        assert_eq!(crate::json::library_to_compact_json(&again), expected);
        // A key with neither a cache directory nor a shipped snapshot is the
        // joint build, as without a key: nothing prepared, nothing lazy.
        drop(again);
        let mut joint = Model::new();
        let load = load_library_with_cache_from(&mut joint, &dir, Some(key), None, &[]).unwrap();
        assert!(load.pending.is_none() && load.recording_path.is_none());
        assert!(joint.loaded_library_unit_count() > 0, "parsed, not decoded");
        assert_ne!(joint.lib_cache_kind(), "lazy");
        assert_eq!(crate::json::library_to_compact_json(&joint), expected);
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn directory_cache_separates_graph_formats_in_memory_and_on_disk() {
        use crate::model::GraphFormat;
        let root =
            std::env::temp_dir().join(format!("sysml-graph-format-{}", uuid::Uuid::new_v4()));
        let dir = root.join("library");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("L.kerml"),
            "standard library package L { feature x = if true ? 1 else 2; }",
        )
        .unwrap();
        let path = root.join("stdlib.libcache");
        // Keep both models alive to exercise the process-wide shared cache.
        let mut legacy = Model::new();
        load_library_with_cache_at(&mut legacy, &dir, Some((91, path.clone()))).unwrap();
        let mut canonical = Model::with_graph_format(GraphFormat::CanonicalV3);
        load_library_with_cache_at(&mut canonical, &dir, Some((91, path.clone()))).unwrap();
        let expected = crate::json::library_to_compact_json(&canonical);
        assert_ne!(crate::json::library_to_compact_json(&legacy), expected);
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut shared = Model::with_graph_format(format);
            load_library_with_cache_at(&mut shared, &dir, Some((91, path.clone()))).unwrap();
            assert_eq!(shared.graph_format(), format);
        }
        drop(legacy);
        drop(canonical);
        let mut disk = Model::with_graph_format(GraphFormat::CanonicalV3);
        load_library_with_cache_at(&mut disk, &dir, Some((91, path.clone()))).unwrap();
        assert_eq!(disk.loaded_library_unit_count(), 0);
        assert_eq!(crate::json::library_to_compact_json(&disk), expected);
        assert!(path.with_extension("prepared").exists());
        assert!(path.with_extension("v3.prepared").exists());
        std::fs::remove_dir_all(root).unwrap();
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
        let mut load = load_library_with_cache_at(&mut cold, &dir, cache()).unwrap();
        load.finish();
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
        // The handle prepared here keeps the recording in memory, so this
        // process leaves the file unread: a joint build arms the handle's.
        assert_eq!(cold.lib_cache_kind(), "off");
        cold.add_source(
            "user.sysml",
            "private import Other::*; package U { part a : L::A; }",
        );
        assert!(ResolvedModel::build(&cold).b.library_facts.is_none());
        assert_eq!(
            cold.lib_cache_kind(),
            "use",
            "the fallback replays the recording the handle keeps"
        );
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

    /// A snapshot carries the frozen rows' kept lookup graph, which reads
    /// back as the graph the writer had, memos included; the graph a
    /// decoded library's freeze would build from the rows instead agrees
    /// with it in every table but the memos, which lookups fill.
    #[test]
    fn a_snapshot_carries_the_kept_lookup_graph() {
        // The second library materializes rows of its own (the enumeration
        // usage's implied relationships), which the graph covers too.
        for (name, source) in [
            (
                "lib.kerml",
                "standard library package L { \
                    class P { feature f; protected feature g; } \
                    class Q :> P { feature redefines f; alias ff for f; } \
                    package N { class X; } alias Y for N::X; }",
            ),
            (
                "lib.sysml",
                "standard library package L { enum def K { a; b; } \
                    part def P { attribute x : K; } part def Q :> P { attribute :>> x; } }",
            ),
        ] {
            let mut base = Model::new();
            base.add_library_source(name, source);
            let prepared = base.prepare_library().unwrap();
            assert_eq!(
                prepared.builder.carries_semantic_rows(),
                name.ends_with(".sysml"),
                "{name}: rows of its own"
            );
            let written = prepared
                .builder
                .lookup_wire()
                .expect("the library keeps a lookup graph");
            let bytes = prepared.to_bytes(7).unwrap();
            let carried = PreparedLibrary::from_bytes(&bytes, 7).unwrap();
            assert_eq!(
                carried.builder.lookup_wire(),
                Some(written.clone()),
                "{name}: the carried graph reads back as written"
            );
            let mut wire = decode_wire(&bytes, 7, false).unwrap();
            assert!(
                wire.lookup.take().is_some(),
                "the snapshot carries the graph"
            );
            let built = PreparedLibrary::from_wire(wire)
                .unwrap()
                .builder
                .lookup_wire()
                .expect("the freeze builds a graph when none is carried");
            let memos = ["inherited", "inherited_open", "suppressed"];
            let differences = written.differences(&built);
            assert!(
                differences.iter().all(|table| memos.contains(table)),
                "{name}: the carried graph differs from a built one in {differences:?}"
            );
        }
    }
}

#[cfg(test)]
mod apart_tests {
    use super::*;
    use crate::json::ResolvedModel;

    const LIBRARY: &str = "standard library package L { \
        part def A { attribute x; } part def B :> A { attribute :>> x = 1; } }";
    const USER: &str = "package U { part b : L::B; part def C :> L::A { attribute y; } }";

    /// A snapshot of the library, with its plans, written under `dir`.
    fn written(dir: &Path) -> (std::path::PathBuf, u64) {
        std::fs::create_dir_all(dir).unwrap();
        let mut base = Model::new();
        base.add_library_source("lib.sysml", LIBRARY);
        let library = Arc::new(base.prepare_library().unwrap());
        library.make_plans();
        let path = dir.join("stdlib-0000000000000005.prepared");
        library.save(&path, 5).unwrap();
        (path, 5)
    }

    /// What a build on `library` answers: the graph, the semantic findings
    /// and the facts the checks read.
    fn checked(library: Arc<PreparedLibrary>) -> (serde_json::Value, usize, Vec<u8>) {
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        model.add_source("user.sysml", USER);
        let mut r = ResolvedModel::build(&model);
        assert!(r.b.prepared_from.is_some(), "a build on the library");
        let facts = crate::cache_codec::encode(&*r.b.facts()).unwrap();
        (
            crate::json::model_to_compact_json(&model),
            crate::check::validate_semantics(&model).len(),
            facts,
        )
    }

    /// The snapshot at `path` with one byte of part `part` changed.
    pub(super) fn corrupt_bytes(path: &Path, key: u64, part: usize) -> Vec<u8> {
        let mut bytes = std::fs::read(path).unwrap();
        let (parts, payload) = header_parts(&bytes, key).unwrap();
        let start =
            bytes.len() - payload.len() + parts[..part].iter().map(|p| p.len).sum::<usize>();
        bytes[start + parts[part].len / 2] ^= 0xff;
        bytes
    }

    /// [`corrupt_bytes`], written beside the snapshot.
    pub(super) fn corrupted(path: &Path, key: u64, part: usize) -> std::path::PathBuf {
        let corrupt = path.with_extension(format!("part{part}.prepared"));
        std::fs::write(&corrupt, corrupt_bytes(path, key, part)).unwrap();
        corrupt
    }

    /// A loaded snapshot's facts and plans are read apart from the load:
    /// the load leaves them, a build's checks read them, and what they
    /// read equals what the snapshot held whole gives.
    #[test]
    fn a_loaded_snapshots_facts_and_plans_are_read_apart_from_the_load() {
        let dir = std::env::temp_dir().join(format!("sysmlv2-apart-{}", std::process::id()));
        let (path, key) = written(&dir);
        let whole =
            Arc::new(PreparedLibrary::from_bytes(&std::fs::read(&path).unwrap(), key).unwrap());
        assert!(
            whole.facts.is_made(),
            "held whole, the facts decode with the load"
        );
        let loaded = Arc::new(PreparedLibrary::load(&path, key).unwrap());
        assert!(
            !loaded.facts.is_made(),
            "loaded, the facts are left to the first use"
        );
        assert!(
            loaded.carries_plans(),
            "loaded, the plans are left to the first request"
        );
        assert!(
            loaded.holds_snapshot(),
            "the cells hold the snapshot for them"
        );
        assert_eq!(checked(Arc::clone(&loaded)), checked(Arc::clone(&whole)));
        assert!(loaded.facts.is_made(), "the checks read the facts");
        assert!(!loaded.carries_plans(), "the build read the plans back");
        assert!(
            !loaded.holds_snapshot(),
            "both read, the snapshot is let go"
        );
        // Written again, a loaded handle writes the same snapshot.
        assert_eq!(loaded.to_bytes(key).unwrap(), whole.to_bytes(key).unwrap());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Read in line, as a host without threads reads them, the facts and
    /// the plans equal those read beside the load, and the snapshot is let
    /// go once both are read.
    #[test]
    fn the_parts_read_in_line_equal_the_parts_read_beside_the_load() {
        let dir = std::env::temp_dir().join(format!("sysmlv2-apart-inline-{}", std::process::id()));
        let (path, key) = written(&dir);
        let snapshot = Arc::new(
            Snapshot::new(crate::libcache::map_capped(&path).unwrap(), key, None).unwrap(),
        );
        let loaded = Arc::new(PreparedLibrary::load(&path, key).unwrap());
        let rows = loaded.builder.elements.len();
        let facts = LibraryFacts::pending(rows, PendingFacts::Part(Arc::clone(&snapshot)));
        let mut plans = Carried::Part(Arc::clone(&snapshot));
        assert_eq!(Arc::strong_count(&snapshot), 3);
        let in_line = facts.get().expect("the facts decode in line");
        let wire = plans
            .take()
            .expect("the part decodes")
            .expect("the snapshot carries plans");
        assert_eq!(
            Arc::strong_count(&snapshot),
            1,
            "both cells let the snapshot go"
        );
        let beside = loaded
            .facts
            .get()
            .expect("the facts decode beside the load");
        assert_eq!(
            crate::cache_codec::encode(&*in_line).unwrap(),
            crate::cache_codec::encode(&*beside).unwrap()
        );
        let carried = loaded.plans.take_carried().expect("the plans are carried");
        assert_eq!(
            crate::cache_codec::encode(&wire).unwrap(),
            crate::cache_codec::encode(&carried).unwrap()
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A snapshot written before the library's plans were made carries
    /// none, and a handle loaded from it writes none — as one holding it
    /// whole does — whether or not a build on it has made the plans since.
    #[test]
    fn a_loaded_snapshot_without_plans_writes_none_as_one_held_whole_does() {
        let dir =
            std::env::temp_dir().join(format!("sysmlv2-apart-noplans-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut base = Model::new();
        base.add_library_source("lib.sysml", LIBRARY);
        let library = Arc::new(base.prepare_library().unwrap());
        let path = dir.join("stdlib-0000000000000006.prepared");
        library.save(&path, 6).unwrap();
        let bytes = std::fs::read(&path).unwrap();
        let whole = Arc::new(PreparedLibrary::from_bytes(&bytes, 6).unwrap());
        assert!(!whole.carries_plans());
        let unasked = PreparedLibrary::load(&path, 6).unwrap();
        assert_eq!(
            unasked.to_bytes(6).unwrap(),
            bytes,
            "not asked, none written"
        );
        let loaded = Arc::new(PreparedLibrary::load(&path, 6).unwrap());
        assert_eq!(checked(Arc::clone(&loaded)), checked(Arc::clone(&whole)));
        assert!(loaded.library_plans().is_some() && whole.library_plans().is_some());
        assert_eq!(loaded.to_bytes(6).unwrap(), whole.to_bytes(6).unwrap());
        assert_eq!(
            loaded.to_bytes(6).unwrap(),
            bytes,
            "the plans a build made are not written"
        );
        loaded.make_plans();
        assert_ne!(loaded.to_bytes(6).unwrap(), bytes, "asked for, they are");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A snapshot whose facts part does not verify is refused held whole,
    /// and loads otherwise: the first build then makes facts over every
    /// row, as a build without a prepared library does, and answers the
    /// same.
    #[test]
    fn a_corrupt_facts_part_leaves_the_facts_to_the_build() {
        let dir = std::env::temp_dir().join(format!("sysmlv2-apart-facts-{}", std::process::id()));
        let (path, key) = written(&dir);
        let corrupt = corrupted(&path, key, FACTS_PART);
        assert!(
            PreparedLibrary::from_bytes(&std::fs::read(&corrupt).unwrap(), key).is_none(),
            "held whole, refused"
        );
        let loaded = Arc::new(PreparedLibrary::load(&corrupt, key).unwrap());
        let (graph, findings, facts) = checked(Arc::clone(&loaded));
        assert!(loaded.facts.get().is_none(), "the part did not decode");
        let mut cold = Model::new();
        cold.add_library_source("lib.sysml", LIBRARY);
        cold.add_source("user.sysml", USER);
        let mut r = ResolvedModel::build(&cold);
        assert!(
            r.b.library_facts.is_none(),
            "built without a prepared library"
        );
        assert_eq!(graph, crate::json::model_to_compact_json(&cold));
        assert_eq!(findings, crate::check::validate_semantics(&cold).len());
        assert_eq!(facts, crate::cache_codec::encode(&*r.b.facts()).unwrap());
        assert!(
            loaded.to_bytes(key).is_err(),
            "nothing to write the facts from"
        );
        assert!(corrupt.exists(), "read in place, the file is left");
        let own = Arc::new(PreparedLibrary::load_cache(&corrupt, key).unwrap());
        assert_eq!(checked(Arc::clone(&own)).0, graph);
        assert!(
            !corrupt.exists(),
            "the cache's own file is removed once its part fails"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A snapshot whose plans part does not verify loads: the plans are
    /// made by the first request, and a build answers the same.
    #[test]
    fn a_corrupt_plans_part_is_planned_instead() {
        let dir = std::env::temp_dir().join(format!("sysmlv2-apart-plans-{}", std::process::id()));
        let (path, key) = written(&dir);
        let corrupt = corrupted(&path, key, PLANS_PART);
        let whole =
            Arc::new(PreparedLibrary::from_bytes(&std::fs::read(&path).unwrap(), key).unwrap());
        let loaded = Arc::new(PreparedLibrary::load(&corrupt, key).unwrap());
        assert!(
            loaded.carries_plans(),
            "the part is left to the first request"
        );
        assert!(loaded.library_plans().is_some(), "planned instead");
        assert!(!loaded.carries_plans());
        assert_eq!(checked(Arc::clone(&loaded)), checked(whole));
        assert!(corrupt.exists(), "read in place, the file is left");
        let own = Arc::new(PreparedLibrary::load_cache(&corrupt, key).unwrap());
        assert!(own.library_plans().is_some(), "planned instead");
        assert!(
            !corrupt.exists(),
            "the cache's own file is removed once its part fails"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The cache's own snapshot, taken by the loader, is removed by the run
    /// whose checks find its facts part corrupt, and the next run prepares
    /// the library afresh and writes it again.
    #[test]
    fn a_cache_snapshot_whose_part_does_not_decode_is_removed_and_written_again() {
        let root = std::env::temp_dir().join(format!("sysmlv2-apart-cache-{}", std::process::id()));
        let lib = root.join("lib");
        let cache = root.join("cache");
        std::fs::create_dir_all(&lib).unwrap();
        std::fs::create_dir_all(&cache).unwrap();
        std::fs::write(lib.join("lib.sysml"), LIBRARY).unwrap();
        let snapshot = || {
            std::fs::read_dir(&cache)
                .unwrap()
                .flatten()
                .map(|entry| entry.path())
                .find(|path| path.extension().is_some_and(|x| x == "prepared"))
        };
        // Cold: the library is prepared and the snapshot written.
        let mut cold = Model::new();
        let mut load = load_library_with_cache_in(&mut cold, &lib, Some(&cache)).unwrap();
        load.finish();
        drop(cold);
        let path = snapshot().expect("the cold load writes the snapshot");
        let stem = path.file_stem().unwrap().to_str().unwrap().to_string();
        let key = u64::from_str_radix(stem.trim_start_matches("stdlib-"), 16).unwrap();
        std::fs::write(&path, corrupt_bytes(&path, key, FACTS_PART)).unwrap();
        // Warm: the loader takes the file, the checks find its facts part
        // corrupt, and the file is removed.
        let mut warm = Model::new();
        let load = load_library_with_cache_in(&mut warm, &lib, Some(&cache)).unwrap();
        assert!(load.guessed, "the cache's one snapshot is taken");
        warm.add_source("user.sysml", USER);
        let mut r = ResolvedModel::build(&warm);
        assert!(r.b.library_facts.is_some(), "built on the prepared library");
        let _ = r.b.facts();
        assert!(snapshot().is_none(), "the corrupt file is removed");
        // (the build's handle let go, the process holds the library no
        // longer and the next load reads the cache again)
        drop(r);
        drop(warm);
        // Cold again: prepared afresh and written.
        let mut again = Model::new();
        let mut load = load_library_with_cache_in(&mut again, &lib, Some(&cache)).unwrap();
        load.finish();
        assert!(!load.guessed, "nothing to take");
        assert!(snapshot().is_some(), "written again");
        let _ = std::fs::remove_dir_all(&root);
    }
}
