//! Snapshot encodings of a compact element array read one element at a
//! time. [`ElementRecords`] reads the `n` elements in array order, each
//! made once: it keeps each element's id, what its references and
//! ownership lists name, what its owner backpointers spell and what the
//! id derivation reads of it, and writes its record with references to
//! element identities spelled as their 16 bytes. The compact CBOR and
//! the id-elided compact CBOR are then written by
//! transcoding those records with the references respelled as wire
//! indices and the backpointers that match their derivation left out,
//! so one element's tree is held at a time where the whole array's is
//! several times the size of its JSON text. (The state digest reads the
//! elements in turn on its own, lighter pass: `state_digest_streamed`.)

use crate::cbor::Writer;
use crate::encode::{
    Elided, FLAG_ELIDE_IDS, FLAG_IMPLIED_OWNERS, FLAG_UNIT_PATHS, OWNER_SLOTS, RawIds, WireIndex,
    check_units, elem_of, header_word_with_scheme, id_digest, id_references, owner_absent_bits,
    table_set, transcode_record, write_element, write_owner_exceptions, write_units,
};
use crate::{Error, ordinal};
use serde_json::{Map, Value};
use std::collections::{HashMap, HashSet};
use sysmlv2_model::ids::{IdGraph, Target};
use uuid::Uuid;

/// The two ownership lists, by the slot [`IdGraph::owned`] takes.
const OWNED_LISTS: [&str; 2] = ["ownedRelationship", "ownedRelatedElement"];

/// What an element spells for one of its owner backpointers.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OwnerSpelling {
    /// The key is not in the element.
    Absent,
    /// `null`.
    Null,
    /// `{"@id": …}` naming an element identity.
    Id(Uuid),
    /// Anything else: a symbolic reference, or a shape the encoder
    /// refuses.
    Other,
}

/// A reference property as the id derivation reads it, before the
/// element it names is looked up.
enum Reference {
    Symbolic(String),
    Id(String),
}

/// What the derivation and the owner elision read of one element.
struct Row {
    ty: &'static str,
    fields: &'static [crate::tables::CborField],
    declared_name: Option<String>,
    member_name: Option<String>,
    owning_relationship: Option<Uuid>,
    /// Its `redefinedFeature` or `referencedFeature`, for the two
    /// metaclasses whose it names a feature.
    feature_reference: Option<Reference>,
    /// Its `chainingFeature`, for a `FeatureChaining`.
    chaining_feature: Option<String>,
    spelled: [OwnerSpelling; 2],
    /// The backpointer slots its metaclass carries but it does not spell.
    absent_bits: u64,
}

/// The element records of an `n`-element compact array, written once
/// in array order with raw id references, and what each element names
/// (see the module's documentation). [`Self::to_compact_cbor`] and
/// [`Self::to_compact_cbor_elided`] are byte for byte what the whole
/// array's encoders write, for an
/// array whose element ids are in their canonical spelling (lowercase,
/// hyphenated — the toolkit's emitters' spelling); an array with any
/// other is refused at [`Self::read`], as is whatever the whole array's
/// encoders refuse.
pub struct ElementRecords {
    ids: Vec<Uuid>,
    index: HashMap<Uuid, usize>,
    /// The identities the references name that are not among the
    /// elements, ascending.
    ext: Vec<Uuid>,
    records: Vec<u8>,
    /// Where each element's record starts, and where the last ends.
    starts: Vec<usize>,
    /// Each element's ownership targets, by position, flat, and where
    /// its two lists end.
    owned: Vec<usize>,
    ends: Vec<[usize; 2]>,
    rows: Vec<Row>,
}

impl ElementRecords {
    /// Read the `n`-element array whose element `i` `element(i)` makes,
    /// calling it once for each element, in array order.
    pub fn read(n: usize, mut element: impl FnMut(usize) -> Value) -> Result<Self, Error> {
        let tables = table_set(false);
        let mut ids = Vec::with_capacity(n);
        let mut targets: Vec<Uuid> = Vec::new();
        let mut ends: Vec<[usize; 2]> = Vec::with_capacity(n);
        let mut referenced = HashSet::new();
        let mut records = Writer::default();
        let mut starts = Vec::with_capacity(n + 1);
        let mut rows = Vec::with_capacity(n);
        for i in 0..n {
            let value = element(i);
            let e = elem_of(&value, tables)?;
            ids.push(canonical_uuid(e.id).ok_or_else(|| {
                Error::new(format!(
                    "element {i}'s @id `{}` is a UUID in its canonical spelling",
                    e.id
                ))
            })?);
            let mut end = [0; 2];
            for (slot, key) in OWNED_LISTS.into_iter().enumerate() {
                if let Some(Value::Array(a)) = e.obj.get(key) {
                    // A target spelled otherwise than canonically names
                    // no element, as no canonically spelled id equals it.
                    targets.extend(
                        a.iter()
                            .filter_map(|t| t.get("@id").and_then(Value::as_str))
                            .filter_map(canonical_uuid),
                    );
                }
                end[slot] = targets.len();
            }
            ends.push(end);
            id_references(&e, |u| {
                referenced.insert(u);
            })?;
            rows.push(Row {
                ty: tables[e.code as usize].0,
                fields: e.fields,
                declared_name: text(e.obj, "declaredName")
                    .or_else(|| text(e.obj, "declaredShortName"))
                    .map(str::to_owned),
                member_name: text(e.obj, "memberName")
                    .or_else(|| text(e.obj, "memberShortName"))
                    .map(str::to_owned),
                owning_relationship: e
                    .obj
                    .get("owningRelationship")
                    .and_then(|v| v.get("@id"))
                    .and_then(Value::as_str)
                    .and_then(canonical_uuid),
                feature_reference: match e.ty {
                    "Redefinition" => reference(e.obj, "redefinedFeature"),
                    "ReferenceSubsetting" => reference(e.obj, "referencedFeature"),
                    _ => None,
                },
                chaining_feature: (e.ty == "FeatureChaining")
                    .then(|| text_of(e.obj.get("chainingFeature")?.get("@id")?))
                    .flatten(),
                spelled: OWNER_SLOTS.map(|(prop, _)| spelling(e.obj.get(prop))),
                absent_bits: owner_absent_bits(&e),
            });
            starts.push(records.len());
            write_element(&mut records, &RawIds, &e, None)?;
        }
        starts.push(records.len());
        let mut index = HashMap::with_capacity(n);
        for (i, &id) in ids.iter().enumerate() {
            if index.insert(id, i).is_some() {
                return Err(Error::new(format!("duplicate element @id `{id}`")));
            }
        }
        // The ownership targets by position, those outside the array
        // left out.
        let mut owned = Vec::with_capacity(targets.len());
        let mut at = 0;
        for end in &mut ends {
            for slot in end.iter_mut() {
                owned.extend(targets[at..*slot].iter().filter_map(|u| index.get(u)));
                at = *slot;
                *slot = owned.len();
            }
        }
        let mut ext: Vec<Uuid> = referenced
            .into_iter()
            .filter(|u| !index.contains_key(u))
            .collect();
        ext.sort_unstable();
        Ok(Self {
            ids,
            index,
            ext,
            records: records.into_bytes(),
            starts,
            owned,
            ends,
            rows,
        })
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    /// Whether there are no elements.
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// The element identities the elements' references name that are
    /// not among the elements: the targets an id elision asks its
    /// `external_name` about.
    pub fn externals(&self) -> &[Uuid] {
        &self.ext
    }

    /// Element `i`'s record.
    fn record(&self, i: usize) -> &[u8] {
        &self.records[self.starts[i]..self.starts[i + 1]]
    }

    /// Per element, the derived owner for each backpointer slot — `None`
    /// where no ownership list claims it; the first claimant in element
    /// order, then list order, wins — as the whole array's encoders
    /// derive them.
    fn derived_owners(&self) -> Vec<[Option<usize>; 2]> {
        let mut owners = vec![[None, None]; self.len()];
        for i in 0..self.len() {
            // Slot 0's backpointer is derived from `ownedRelatedElement`
            // (list 1), slot 1's from `ownedRelationship` (list 0).
            for (slot, list) in [(0, 1), (1, 0)] {
                for &j in self.owned(i, list) {
                    let owner: &mut Option<usize> = &mut owners[j][slot];
                    if owner.is_none() {
                        *owner = Some(i);
                    }
                }
            }
        }
        owners
    }

    /// The backpointers element `i`'s record leaves out: those that
    /// spell their derivation.
    fn elision(&self, i: usize, derived: &[Option<usize>; 2]) -> Elided {
        let row = &self.rows[i];
        let mut elided = Elided::default();
        for (slot, (prop, _)) in OWNER_SLOTS.iter().enumerate() {
            let Some(ord) = ordinal(row.fields, prop) else {
                continue;
            };
            match (derived[slot], row.spelled[slot]) {
                (None, OwnerSpelling::Null) => elided.bits |= 1 << ord,
                (Some(j), OwnerSpelling::Id(u)) if self.ids[j] == u => elided.entries |= 1 << ord,
                _ => {}
            }
        }
        elided
    }

    /// The element records, in array order, their backpointers elided
    /// against their derivation, then the owner-exception section.
    fn write_elements(&self, w: &mut Writer) -> Result<(), Error> {
        let owners = self.derived_owners();
        w.array(self.len());
        for (i, derived) in owners.iter().enumerate() {
            transcode_record(w, self, self.record(i), self.elision(i, derived))?;
        }
        let exceptions: Vec<(u64, u64)> = self
            .rows
            .iter()
            .enumerate()
            .filter(|(_, row)| row.absent_bits != 0)
            .map(|(i, row)| (i as u64, row.absent_bits))
            .collect();
        write_owner_exceptions(w, &exceptions);
        Ok(())
    }

    /// The array's compact CBOR carrying the model's unit structure:
    /// what `to_compact_cbor_with_units` writes of the whole array.
    pub fn to_compact_cbor(&self, units: &[(usize, String)]) -> Result<Vec<u8>, Error> {
        let units = check_units(units, self.len())?;
        let mut flags = FLAG_IMPLIED_OWNERS;
        if units.is_some() {
            flags |= FLAG_UNIT_PATHS;
        }
        let mut w = Writer::with_magic_for(self.len());
        w.array(5 + usize::from(units.is_some()));
        w.uint(header_word_with_scheme(flags, crate::ID_SCHEME_VERSION));
        w.array(self.ext.len());
        for u in &self.ext {
            w.bstr(u.as_bytes());
        }
        w.array(self.len());
        for u in &self.ids {
            w.bstr(u.as_bytes());
        }
        self.write_elements(&mut w)?;
        if let Some(units) = units {
            write_units(&mut w, units);
        }
        Ok(w.into_bytes())
    }

    /// The array's id-elided compact CBOR carrying the model's unit
    /// structure: what `to_compact_cbor_elided_with_units` writes of
    /// the whole array. `external_name` is asked about
    /// [`Self::externals`] only.
    pub fn to_compact_cbor_elided(
        &self,
        external_name: &dyn Fn(&str) -> Option<String>,
        units: &[(usize, String)],
    ) -> Result<Vec<u8>, Error> {
        let units = check_units(units, self.len())?;
        let derived = sysmlv2_model::ids::derive_ids_of(self, external_name).map_err(Error::new)?;
        let exceptions: Vec<(u64, Uuid)> = self
            .ids
            .iter()
            .enumerate()
            .filter(|&(i, &u)| derived[i] != Some(u))
            .map(|(i, &u)| (i as u64, u))
            .collect();
        let digest = id_digest(self.ids.iter().copied());
        let mut flags = FLAG_ELIDE_IDS | FLAG_IMPLIED_OWNERS;
        if units.is_some() {
            flags |= FLAG_UNIT_PATHS;
        }
        let mut w = Writer::with_magic_for(self.len());
        w.array(5 + usize::from(units.is_some()));
        w.uint(header_word_with_scheme(flags, crate::ID_SCHEME_VERSION));
        w.array(self.ext.len());
        for u in &self.ext {
            w.bstr(u.as_bytes());
        }
        // In place of the id table: the exception map + the digest.
        w.array(2);
        w.map(exceptions.len());
        for (i, u) in &exceptions {
            w.uint(*i);
            w.bstr(u.as_bytes());
        }
        w.bstr(digest.as_bytes());
        self.write_elements(&mut w)?;
        if let Some(units) = units {
            write_units(&mut w, units);
        }
        Ok(w.into_bytes())
    }

    /// The element a reference's `@id` text names, in the array or
    /// outside it.
    fn named<'a>(&self, id: &'a str) -> Target<'a> {
        match canonical_uuid(id).and_then(|u| self.index.get(&u)) {
            Some(&t) => Target::Local(t),
            None => Target::External(id),
        }
    }
}

impl WireIndex for ElementRecords {
    fn try_index(&self, u: Uuid) -> Option<u64> {
        match self.index.get(&u) {
            Some(&i) => Some(i as u64),
            None => Some((self.len() + self.ext.binary_search(&u).ok()?) as u64),
        }
    }
}

impl IdGraph for ElementRecords {
    fn len(&self) -> usize {
        self.ids.len()
    }

    fn uuid(&self, i: usize) -> Result<Uuid, sysmlv2_model::ids::IdError> {
        Ok(self.ids[i])
    }

    fn ty(&self, i: usize) -> &str {
        self.rows[i].ty
    }

    fn owned(&self, i: usize, slot: usize) -> &[usize] {
        let start = match (slot, i) {
            (0, 0) => 0,
            (0, _) => self.ends[i - 1][1],
            _ => self.ends[i][0],
        };
        &self.owned[start..self.ends[i][slot]]
    }

    fn declared_name(&self, i: usize) -> Option<&str> {
        self.rows[i].declared_name.as_deref()
    }

    fn member_name(&self, i: usize) -> Option<&str> {
        self.rows[i].member_name.as_deref()
    }

    fn owning_relationship(&self, i: usize) -> Option<usize> {
        self.rows[i]
            .owning_relationship
            .and_then(|u| self.index.get(&u).copied())
    }

    fn feature_reference(&self, i: usize, key: &str) -> Option<Target<'_>> {
        let row = &self.rows[i];
        let wanted = match row.ty {
            "Redefinition" => "redefinedFeature",
            "ReferenceSubsetting" => "referencedFeature",
            _ => return None,
        };
        if key != wanted {
            return None;
        }
        Some(match row.feature_reference.as_ref()? {
            Reference::Symbolic(s) => Target::Symbolic(s),
            Reference::Id(s) => self.named(s),
        })
    }

    fn chaining_feature(&self, i: usize) -> Option<Target<'_>> {
        Some(self.named(self.rows[i].chaining_feature.as_deref()?))
    }
}

/// `s` as a UUID when it is the UUID's canonical spelling.
pub(crate) fn canonical_uuid(s: &str) -> Option<Uuid> {
    let u = Uuid::try_parse(s).ok()?;
    let mut spelled = [0; uuid::fmt::Hyphenated::LENGTH];
    (u.hyphenated().encode_lower(&mut spelled) == s).then_some(u)
}

fn text<'a>(obj: &'a Map<String, Value>, key: &str) -> Option<&'a str> {
    obj.get(key).and_then(Value::as_str)
}

fn text_of(v: &Value) -> Option<String> {
    v.as_str().map(str::to_owned)
}

/// Element `key` of `obj` as the derivation reads a feature reference:
/// a `@ref` first, else a `@id`, else nothing.
fn reference(obj: &Map<String, Value>, key: &str) -> Option<Reference> {
    let target = obj.get(key)?;
    if let Some(s) = target.get("@ref").and_then(Value::as_str) {
        return Some(Reference::Symbolic(s.to_owned()));
    }
    Some(Reference::Id(text_of(target.get("@id")?)?))
}

/// What a backpointer value spells.
fn spelling(value: Option<&Value>) -> OwnerSpelling {
    match value {
        None => OwnerSpelling::Absent,
        Some(Value::Null) => OwnerSpelling::Null,
        Some(Value::Object(o)) if o.len() == 1 => {
            match o
                .get("@id")
                .and_then(Value::as_str)
                .and_then(canonical_uuid)
            {
                Some(u) => OwnerSpelling::Id(u),
                None => OwnerSpelling::Other,
            }
        }
        Some(_) => OwnerSpelling::Other,
    }
}
