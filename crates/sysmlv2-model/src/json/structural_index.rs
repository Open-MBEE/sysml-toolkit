//! Reusable immutable stored-graph topology; never semantic proof results.
//! Reuse requires identical element rows and authored/implied provenance.
use super::Builder;
use crate::{layered::Revision, metaclass::conforms};
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, OnceLock},
};
use uuid::Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Carrier {
    Missing,
    Unique(usize),
    Invalid,
}

/// All fields are structural identity facts, independent of names, closure
/// policies, inheritance providers, source lookup contexts and proof budgets.
#[derive(Default)]
pub(super) struct StoredStructure {
    revision: Option<Revision>,
    authored_end: usize,
    logical_work: usize,
    ids: Arc<crate::layered::IdMap<Uuid, usize>>,
    carriers: Vec<Carrier>,
    multiple_membership_carriers: bool,
    pub(super) type_featurings: HashMap<usize, Vec<usize>>,
    pub(super) bad_chains: HashSet<usize>,
    pub(super) bad_bases: HashSet<usize>,
    source_incomplete: bool,
    /// Lazy inverse projection of these same rows; ordinary consumers do not
    /// allocate or scan it. A failed bounded scan is never published.
    typing: OnceLock<Arc<StoredTyping>>,
    // Candidate identities collected during the existing complete row scan.
    // Includes standalone and generated rows, independent of source validity.
    typing_rows: Vec<usize>,
    memberships: OnceLock<Arc<MembershipDomains>>,
    membership_rows: Vec<usize>,
    imports: OnceLock<Arc<ImportDomains>>,
    pub(super) ids_unique: bool,
    /// Includes standalone/orphan authored Import rows, independent of owner
    /// lists or a stored isImplied flag. Shared absence checks cost O(1).
    pub(super) has_authored_import: bool,
    pub(super) has_recursive_import: bool,
    import_rows: Vec<usize>,
    pub(super) metadata_annotation_targets: HashSet<usize>,
    pub(super) metadata_annotation_sources: HashMap<usize, Vec<usize>>,
    pub(super) annotations_incomplete: bool,
    /// The kept scan of the frozen rows this structure's scan extended
    /// (`None` when every row was scanned here): the projections read its
    /// projections for those rows and project only the rows after them.
    prefix: Option<Arc<PrefixStructure>>,
}
/// Inverse Feature.typing and Feature.subsetting, independent of carrier.
/// Suffix rows remain subject to the shared semantic carrier certificate.
#[derive(Default)]
pub(super) struct StoredTyping {
    pub(super) relationships: TypingSources,
    pub(super) sources_incomplete: bool,
}

/// The typing and subsetting relationships by source feature. A projection
/// that extends the frozen rows' own holds only the later rows' entries: those
/// rows name only later features as sources (else every row is projected, see
/// [`StoredStructure::typing`]), so a frozen feature's entry is the frozen
/// projection's.
#[derive(Default)]
pub(super) struct TypingSources {
    own: HashMap<usize, Vec<usize>>,
    frozen: Option<Arc<StoredTyping>>,
}
impl TypingSources {
    pub(super) fn get(&self, feature: &usize) -> Option<&Vec<usize>> {
        self.own
            .get(feature)
            .or_else(|| self.frozen.as_ref()?.relationships.get(feature))
    }
}
#[cfg(test)]
impl std::ops::Index<&usize> for TypingSources {
    type Output = Vec<usize>;
    fn index(&self, feature: &usize) -> &Vec<usize> {
        self.get(feature).expect("a typed feature")
    }
}

/// Inverse ownership contradictions for authored Membership domains. This is
/// structural row evidence, not a new semantic graph or family certificate.
/// Domains that extend the frozen rows' own keep theirs beside the owners the
/// later rows contradict.
#[derive(Default)]
pub(super) struct MembershipDomains {
    bad_owners: HashSet<usize>,
    frozen: Option<Arc<MembershipDomains>>,
    unlocalized: bool,
}
impl MembershipDomains {
    /// Whether every membership claim names a row.
    pub(super) fn localized(&self) -> bool {
        !self.unlocalized
    }
    pub(super) fn owner_complete(&self, owner: usize) -> bool {
        !self.unlocalized
            && !self.bad_owners.contains(&owner)
            && self
                .frozen
                .as_ref()
                .is_none_or(|frozen| !frozen.bad_owners.contains(&owner))
    }
}

/// Authored Import ownership contradictions, kept separate from Membership
/// evidence so a query that does not consume imports need not pay for them.
#[derive(Default)]
pub(super) struct ImportDomains {
    recursive_owners: HashSet<usize>,
    bad_owners: HashSet<usize>,
    unlocalized: bool,
}
impl ImportDomains {
    pub(super) fn localized(&self) -> bool {
        !self.unlocalized
    }
    pub(super) fn recursive_owner(&self, owner: usize) -> bool {
        self.recursive_owners.contains(&owner)
    }
    pub(super) fn owner_complete(&self, owner: usize) -> bool {
        !self.unlocalized && !self.bad_owners.contains(&owner)
    }
}

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}
/// First establish the unique annotating source independently of the target.
/// A certified nonmetadata source cannot contribute semantic metadata, even
/// when its unrelated annotation target is unresolved. Metadata sources still
/// require the complete endpoint/ownership certificate before target admission.
fn annotation_ends(
    b: &Builder,
    relationship: usize,
    carriers: &[Carrier],
    ids: &crate::layered::IdMap<Uuid, usize>,
    unsatisfied: &mut HashSet<Uuid>,
    steps: &mut usize,
) -> Option<(usize, Option<usize>)> {
    charge(steps, 1)?;
    let relation = b.elements.get(relationship)?;
    let Carrier::Unique(owner) = *carriers.get(relationship)? else {
        return None;
    };
    let owner_elem = b.elements.get(owner)?;
    if relation.owning_relationship.is_some() {
        return None;
    }
    charge(steps, relation.children.len())?;
    let mut children = HashSet::new();
    let mut owned_annotating = None;
    for &child in &relation.children {
        let element = b.elements.get(child)?;
        if !children.insert(child)
            || element.owning_relationship != Some(relationship)
            || element
                .props
                .get("owningRelationship")
                .is_some_and(|value| value.as_reference() != Some(relation.id))
        {
            return None;
        }
        if conforms(element.ty, "AnnotatingElement") && owned_annotating.replace(child).is_some() {
            return None;
        }
    }
    let owning_annotating = conforms(owner_elem.ty, "AnnotatingElement").then_some(owner);
    // Exactly one owned or owning annotating element, per XMI7633.
    let source = match (owned_annotating, owning_annotating) {
        (Some(source), None) | (None, Some(source)) => source,
        _ => return None,
    };
    for (key, expected) in [
        ("annotatingElement", Some(source)),
        ("owningAnnotatingElement", owning_annotating),
        ("ownedAnnotatingElement", owned_annotating),
        ("owningRelatedElement", Some(owner)),
    ] {
        if let Some(value) = relation.props.get(key) {
            let matches = match expected {
                Some(element) => value.as_reference() == Some(b.elements[element].id),
                None => value.is_null(),
            };
            if !matches {
                return None;
            }
        }
    }
    let source_id = b.elements[source].id;
    if let Some(value) = relation.props.get("source") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != 1 || values[0].as_reference() != Some(source_id) {
            return None;
        }
    }
    if let Some(value) = relation.props.get("relatedElement") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != 2 || values[0].as_reference() != Some(source_id) {
            return None;
        }
    }
    if let Some(value) = relation.props.get("ownedRelatedElement") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != relation.children.len()
            || values
                .iter()
                .zip(relation.children.iter())
                .any(|(v, &child)| v.as_reference() != Some(b.elements[child].id))
        {
            return None;
        }
    }
    // Keep this early nonmetadata certificate bounded to the two normal
    // ownership shapes. Additional owned endpoints still take the complete
    // validation path below.
    if !conforms(b.elements[source].ty, "MetadataFeature")
        && (relation.children.is_empty()
            || (relation.children.len() == 1 && owned_annotating == Some(relation.children[0])))
    {
        return Some((source, None));
    }
    let target = match relation.props.get("annotatedElement") {
        Some(value) => {
            let id = value.as_reference()?;
            match ids.get(&id) {
                Some(&target) => target,
                None => {
                    unsatisfied.insert(id);
                    return None;
                }
            }
        }
        None if owned_annotating.is_some() => owner,
        None => return None,
    };
    if owned_annotating.is_some() != (target == owner) {
        return None;
    }
    for &child in &relation.children {
        if child != source && child != target {
            return None;
        }
    }
    if let Some(value) = relation.props.get("owningAnnotatedElement") {
        let matches = if target == owner {
            value.as_reference() == Some(owner_elem.id)
        } else {
            value.is_null()
        };
        if !matches {
            return None;
        }
    }
    let target_id = b.elements.get(target)?.id;
    if let Some(value) = relation.props.get("target") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != 1 || values[0].as_reference() != Some(target_id) {
            return None;
        }
    }
    // The source and array shape were validated before source classification.
    if let Some(value) = relation.props.get("relatedElement") {
        if value.as_array()?[1].as_reference() != Some(target_id) {
            return None;
        }
    }
    Some((source, Some(target)))
}

/// What a scan of a range of rows records: the ownership carriers, ids and
/// import rows, the authored relationships' type featurings and base
/// contradictions, and the annotations. The scan of a table's frozen rows
/// is kept and reused ([`PrefixStructure`]); the rows after them are
/// scanned again for every structure.
#[derive(Clone, Default)]
pub(super) struct Scanned {
    carriers: Vec<Carrier>,
    ids: crate::layered::IdMap<Uuid, usize>,
    logical_work: usize,
    source_incomplete: bool,
    ids_unique: bool,
    import_rows: Vec<usize>,
    has_authored_import: bool,
    has_recursive_import: bool,
    type_featurings: HashMap<usize, Vec<usize>>,
    bad_chains: HashSet<usize>,
    bad_bases: HashSet<usize>,
    metadata_annotation_targets: HashSet<usize>,
    metadata_annotation_sources: HashMap<usize, Vec<usize>>,
    annotation_pairs: HashSet<(usize, usize)>,
    annotations_incomplete: bool,
    /// Whether a membership row was claimed by more than one owner.
    multiple_membership_carriers: bool,
    /// The authored membership rows, and the typing and subsetting rows,
    /// in row order: the candidates the domain projections read.
    membership_rows: Vec<usize>,
    typing_rows: Vec<usize>,
    /// The ids the rows' references named that no row scanned carried: a
    /// later row carrying one would be read as their target by a whole
    /// scan, so a scan of later rows reports such a row (see [`scan`]).
    unsatisfied: HashSet<Uuid>,
    /// The budget the scan charged; a reuse charges it again, so the budget
    /// reads as if the rows had been scanned.
    steps: usize,
}
impl Scanned {
    fn new(rows: usize) -> Self {
        Self {
            carriers: vec![Carrier::Missing; rows],
            ids_unique: true,
            ..Self::default()
        }
    }
}

/// The scan of a table's frozen rows, kept beside the rows it describes so
/// that every build sharing them scans only its own rows. The scan reads
/// every frozen relationship as its frozen owner's and every frozen id as
/// its frozen row's, and every id a frozen reference named that no frozen
/// row carried as unsatisfied, which holds while no later row claims one
/// of them: a scan of the later rows that meets such a claim — a row
/// claiming a frozen relationship, carrying a frozen row's id, or carrying
/// an id a frozen reference named — says so, and the table is scanned whole
/// instead (see [`scan`]). No production writer makes such a row —
/// `new_relationship` pushes the row it appends, staged rows index staged
/// rows, and a text-built library stores an unresolved reference as its
/// spelling — so the whole scan is the guard, not the path.
pub(crate) struct PrefixStructure {
    base: Arc<Vec<super::Elem>>,
    scanned: Scanned,
    /// The frozen rows' typing and membership projections, made by the first
    /// structure that reads one and shared by every structure extending this
    /// scan (`None` past the budget, or where the frozen ids are not unique).
    typing: OnceLock<Option<FrozenTyping>>,
    memberships: OnceLock<Option<FrozenMemberships>>,
}
/// A projection of the frozen rows, with the budget it charged: a structure
/// reading it charges that again, so its budget reads as a whole projection's.
struct FrozenTyping {
    typing: Arc<StoredTyping>,
    steps: usize,
}
struct FrozenMemberships {
    domains: Arc<MembershipDomains>,
    steps: usize,
    /// The owned relationships of every frozen row, which a whole projection
    /// visits when a later membership row has several carriers.
    owner_relationships: usize,
}
impl PrefixStructure {
    /// A frozen table's rows are all authored: implied relationships are
    /// materialized after a freeze and lie past them.
    fn scan(b: &Builder, steps: &mut usize) -> Option<Self> {
        let rows = b.elements.base_len();
        let mut scanned = Scanned::new(rows);
        let before = *steps;
        // no rows precede these, so none is claimed
        scan(b, &mut scanned, 0, rows, rows, steps)?;
        scanned.steps = steps.saturating_sub(before);
        Some(Self {
            base: Arc::clone(b.elements.base_arc()),
            scanned,
            typing: OnceLock::new(),
            memberships: OnceLock::new(),
        })
    }

    /// The number of frozen rows.
    fn rows(&self) -> usize {
        self.base.len()
    }

    /// The frozen rows' typing projection; `b` shares them.
    fn typing(&self, b: &Builder) -> Option<&FrozenTyping> {
        self.typing
            .get_or_init(|| {
                let mut steps = 0;
                let scanned = &self.scanned;
                let (own, sources_incomplete) = project_typing(
                    b,
                    &scanned.carriers,
                    &scanned.ids,
                    &scanned.typing_rows,
                    0,
                    &mut steps,
                )??;
                Some(FrozenTyping {
                    typing: Arc::new(StoredTyping {
                        relationships: TypingSources { own, frozen: None },
                        sources_incomplete,
                    }),
                    steps,
                })
            })
            .as_ref()
    }

    /// The frozen rows' membership domains; `b` shares them.
    fn memberships(&self, b: &Builder) -> Option<&FrozenMemberships> {
        self.memberships
            .get_or_init(|| {
                let scanned = &self.scanned;
                if !scanned.ids_unique {
                    return None;
                }
                let mut steps = 0;
                let domains = project_memberships(
                    b,
                    &scanned.carriers,
                    &scanned.ids,
                    &scanned.membership_rows,
                    0..self.rows(),
                    scanned.multiple_membership_carriers,
                    &mut steps,
                )??;
                Some(FrozenMemberships {
                    domains: Arc::new(domains),
                    steps,
                    owner_relationships: self
                        .base
                        .iter()
                        .map(|row| row.owned_relationships.len())
                        .sum(),
                })
            })
            .as_ref()
    }
}

#[cfg(test)]
thread_local! {
    static PREFIX_REUSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(test)]
pub(super) fn prefix_reuses() -> usize {
    PREFIX_REUSES.with(|c| c.get())
}
#[cfg(test)]
fn note_prefix_reuse() {
    PREFIX_REUSES.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
fn note_prefix_reuse() {}

/// The membership domains of `membership_rows` (authored membership rows) and
/// of the rows in `rows`, read as children and — when some membership row has
/// several carriers — as owners. `Some(None)` when a row of `rows` names a
/// relationship before `rows.start` as its owning membership: that
/// relationship's claims are gathered by the projection of the earlier rows.
fn project_memberships(
    b: &Builder,
    carriers: &[Carrier],
    ids: &crate::layered::IdMap<Uuid, usize>,
    membership_rows: &[usize],
    rows: std::ops::Range<usize>,
    multiple_membership_carriers: bool,
    steps: &mut usize,
) -> Option<Option<MembershipDomains>> {
    charge(steps, membership_rows.len())?;
    let mut domains = MembershipDomains::default();
    let mut claims: HashMap<usize, HashSet<usize>> = HashMap::new();
    let mut bad_relations = HashSet::new();
    for &relationship in membership_rows {
        let row = &b.elements[relationship];
        let actual = match carriers[relationship] {
            Carrier::Unique(owner) => Some(owner),
            Carrier::Missing => None,
            Carrier::Invalid => {
                bad_relations.insert(relationship);
                None
            }
        };
        let mut owners = HashSet::new();
        if let Some(owner) = actual {
            owners.insert(owner);
        }
        let mut claim = |value: &crate::properties::Atom| match value
            .as_reference()
            .and_then(|id| ids.get(&id).copied())
        {
            Some(owner) => {
                owners.insert(owner);
                if actual != Some(owner) {
                    bad_relations.insert(relationship);
                }
            }
            None => {
                if !value.is_null() {
                    domains.unlocalized = true;
                }
                if actual.is_some() {
                    bad_relations.insert(relationship);
                }
            }
        };
        for key in [
            "owningRelatedElement",
            "membershipOwningNamespace",
            "owningType",
            "featureWithValue",
        ] {
            if key == "featureWithValue" && !conforms(row.ty, "FeatureValue") {
                continue;
            }
            if key == "owningType" && !conforms(row.ty, "FeatureMembership") {
                continue;
            }
            charge(steps, 1)?;
            if let Some(value) = row.props.get(key) {
                claim(value);
            }
        }
        let mut malformed_array = false;
        for key in ["source", "relatedElement"] {
            charge(steps, 1)?;
            if let Some(value) = row.props.get(key) {
                if let Some(values) = value.as_array() {
                    let count = if key == "source" {
                        values.len()
                    } else {
                        usize::from(!values.is_empty())
                    };
                    charge(steps, count)?;
                    for value in values.iter().take(count) {
                        claim(value);
                    }
                } else {
                    malformed_array = true;
                }
            }
        }
        if malformed_array {
            domains.unlocalized = true;
            bad_relations.insert(relationship);
        }
        claims.insert(relationship, owners);
    }
    // Invalid raw carrier cardinality still identifies every actual owner;
    // localize those contradictions instead of poisoning unrelated domains.
    if multiple_membership_carriers {
        charge(steps, rows.len())?;
        for owner in rows.clone() {
            let relationships = &b.elements[owner].owned_relationships;
            charge(steps, relationships.len())?;
            for &relationship in relationships {
                if carriers.get(relationship) == Some(&Carrier::Invalid)
                    && b.elements
                        .get(relationship)
                        .is_some_and(|r| conforms(r.ty, "Membership"))
                {
                    claims.entry(relationship).or_default().insert(owner);
                }
            }
        }
    }
    // The child side is independent evidence: an omitted extra child can
    // claim a perfectly listed singleton Membership and defeat uniqueness.
    charge(steps, rows.len())?;
    for child in rows.clone() {
        let row = &b.elements[child];
        let mut relationships = HashSet::new();
        if let Some(relationship) = row.owning_relationship {
            if b.elements.get(relationship).is_none() {
                domains.unlocalized = true;
            }
            if b.elements
                .get(relationship)
                .is_some_and(|r| conforms(r.ty, "Membership"))
            {
                relationships.insert(relationship);
            }
        }
        for key in [
            "owningRelationship",
            "owningMembership",
            "owningFeatureMembership",
            "owningParameterMembership",
        ] {
            if matches!(key, "owningFeatureMembership" | "owningParameterMembership")
                && !conforms(row.ty, "Feature")
            {
                continue;
            }
            charge(steps, 1)?;
            if let Some(value) = row.props.get(key) {
                if value.is_null() {
                    continue;
                }
                match value.as_reference().and_then(|id| ids.get(&id).copied()) {
                    Some(relationship) if conforms(b.elements[relationship].ty, "Membership") => {
                        relationships.insert(relationship);
                    }
                    Some(_) if key == "owningRelationship" => {}
                    _ => domains.unlocalized = true,
                }
            }
        }
        if conforms(row.ty, "Feature") {
            if let Some(value) = row.props.get("owningType") {
                charge(steps, 1)?;
                let claimed = value.as_reference().and_then(|id| ids.get(&id).copied());
                let actual = row.owning_relationship.and_then(|relationship| {
                    let membership = b.elements.get(relationship)?;
                    if !conforms(membership.ty, "FeatureMembership") {
                        return None;
                    }
                    match carriers.get(relationship)? {
                        Carrier::Unique(owner) => Some(*owner),
                        _ => None,
                    }
                });
                if claimed.is_none() && !value.is_null() {
                    domains.unlocalized = true;
                }
                if claimed != actual {
                    if let Some(owner) = claimed {
                        domains.bad_owners.insert(owner);
                    }
                    if let Some(owner) = actual {
                        domains.bad_owners.insert(owner);
                    }
                }
            }
        }
        if relationships
            .iter()
            .any(|&relationship| relationship < rows.start)
        {
            return Some(None);
        }
        for relationship in relationships {
            charge(steps, 1)?;
            let membership = &b.elements[relationship];
            if !conforms(membership.ty, "OwningMembership")
                || membership.children.as_ref() != [child]
                || row.owning_relationship != Some(relationship)
            {
                bad_relations.insert(relationship);
            }
            if conforms(membership.ty, "FeatureMembership") {
                if let Some(value) = row.props.get("owningType") {
                    charge(steps, 1)?;
                    let owner = value.as_reference().and_then(|id| ids.get(&id).copied());
                    let actual = match carriers[relationship] {
                        Carrier::Unique(owner) => Some(owner),
                        _ => None,
                    };
                    if owner != actual {
                        bad_relations.insert(relationship);
                        if let Some(owner) = owner {
                            claims.entry(relationship).or_default().insert(owner);
                        } else if !value.is_null() {
                            domains.unlocalized = true;
                        }
                    }
                }
            }
        }
    }
    charge(steps, bad_relations.len())?;
    for relationship in bad_relations {
        if let Some(owners) = claims.get(&relationship) {
            charge(steps, owners.len())?;
            domains.bad_owners.extend(owners.iter().copied());
        } else {
            domains.unlocalized = true;
        }
    }
    Some(Some(domains))
}

/// Typing and subsetting relationships by source feature, and whether some
/// relationship's source is missing or contradictory.
type TypingProjection = (HashMap<usize, Vec<usize>>, bool);

/// The typing and subsetting rows `rows` by source feature, and whether some
/// row's source is missing or contradictory. Feature.type reads inverse
/// associations, including standalone rows and generated result subsettings;
/// this is a projection of the same stored identities and carriers, never an
/// independent semantic graph. `Some(None)` when a row names a feature before
/// `floor` as its source: that feature's entry is the earlier rows'.
fn project_typing(
    b: &Builder,
    carriers: &[Carrier],
    ids: &crate::layered::IdMap<Uuid, usize>,
    rows: &[usize],
    floor: usize,
    steps: &mut usize,
) -> Option<Option<TypingProjection>> {
    charge(steps, rows.len())?;
    let mut typing_relationships: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut typing_sources_incomplete = false;
    for &relationship in rows {
        let element = &b.elements[relationship];
        let mut source_id = None;
        let mut invalid = false;
        for key in [
            "specific",
            "typedFeature",
            "subsettingFeature",
            "redefiningFeature",
            "referencingFeature",
            "crossingFeature",
        ] {
            if let Some(value) = element.props.get(key) {
                match value.as_reference() {
                    Some(id) if source_id.is_none_or(|old| old == id) => source_id = Some(id),
                    _ => invalid = true,
                }
            }
        }
        let source = source_id.and_then(|id| ids.get(&id).copied()).or_else(|| {
            if source_id.is_some() || invalid {
                return None;
            }
            match carriers[relationship] {
                Carrier::Unique(owner) if conforms(b.elements[owner].ty, "Feature") => Some(owner),
                _ => None,
            }
        });
        // Contradictory generic source/relatedElement evidence may name
        // another feature; it cannot be charged only to the scalar source.
        for (key, length) in [("source", 1usize), ("relatedElement", 2usize)] {
            if let Some(value) = element.props.get(key) {
                match value.as_array() {
                    Some(values) => {
                        charge(steps, values.len())?;
                        if values.len() != length
                            || source.is_none_or(|source| {
                                values[0].as_reference() != Some(b.elements[source].id)
                            })
                        {
                            invalid = true;
                        }
                    }
                    None => invalid = true,
                }
            }
        }
        if source_id.is_none()
            && element
                .props
                .get("owningRelatedElement")
                .is_some_and(|value| {
                    value.as_reference() != source.map(|source| b.elements[source].id)
                })
        {
            invalid = true;
        }
        if invalid || source.is_none_or(|source| !conforms(b.elements[source].ty, "Feature")) {
            // Missing/contradictory sources cannot be attributed to an
            // arbitrary local feature, so completeness is globally unknown.
            typing_sources_incomplete = true;
            continue;
        }
        let source = source.unwrap();
        if source < floor {
            return Some(None);
        }
        typing_relationships
            .entry(source)
            .or_default()
            .push(relationship);
    }
    Some(Some((typing_relationships, typing_sources_incomplete)))
}

/// Scan the rows `start..end` into `scanned`. The rows before `start` must
/// be scanned already: an annotation's ends are read through the carriers
/// and ids, and a relationship's base through the ids. Returns whether the
/// rows claimed only rows from `start`: a row claiming the relationship
/// row, or the id, of a row before `start`, or carrying an id a reference
/// of those rows named that none of them carried, makes the earlier scan
/// read those as it would not have, and the caller scans whole.
fn scan(
    b: &Builder,
    scanned: &mut Scanned,
    start: usize,
    end: usize,
    authored_end: usize,
    steps: &mut usize,
) -> Option<bool> {
    if scanned.carriers.len() < end {
        scanned.carriers.resize(end, Carrier::Missing);
    }
    scanned.logical_work = scanned.logical_work.saturating_add(end - start);
    let mut own = true;
    let mut annotation_rows = Vec::new();
    for owner in start..end {
        let element = &b.elements[owner];
        if owner < authored_end && conforms(element.ty, "Membership") {
            scanned.membership_rows.push(owner);
        }
        if conforms(element.ty, "Annotation") {
            annotation_rows.push(owner);
        }
        if conforms(element.ty, "FeatureTyping") || conforms(element.ty, "Subsetting") {
            scanned.typing_rows.push(owner);
        }
        if conforms(element.ty, "Import") {
            scanned.import_rows.push(owner);
            scanned.has_recursive_import |= element
                .props
                .get("isRecursive")
                .is_some_and(|v| v.as_bool() != Some(false));
        }
        own &= !scanned.unsatisfied.contains(&element.id);
        if let Some(previous) = scanned.ids.insert(element.id, owner) {
            scanned.ids_unique = false;
            own &= previous >= start;
        }
        charge(steps, element.owned_relationships.len())?;
        scanned.logical_work = scanned
            .logical_work
            .saturating_add(element.owned_relationships.len());
        for &rel in &element.owned_relationships {
            own &= rel >= start;
            let entry = scanned.carriers.get_mut(rel)?;
            if *entry != Carrier::Missing && conforms(b.elements[rel].ty, "Membership") {
                scanned.multiple_membership_carriers = true;
            }
            *entry = match entry {
                Carrier::Missing => Carrier::Unique(owner),
                _ => Carrier::Invalid,
            };
        }
    }
    // Materialized relationships are owned through the semantic side table,
    // not the authored ownership rows indexed here. Their bases are already
    // supplied by the retained shared implied plan. A stored isImplied flag
    // alone does not establish this provenance and must not bypass checks.
    for rel in start..end.min(authored_end) {
        let carrier = scanned.carriers[rel];
        let element = &b.elements[rel];
        if conforms(element.ty, "Import") {
            scanned.has_authored_import = true;
        }
        let owner = match carrier {
            Carrier::Unique(owner) => Some(owner),
            _ => None,
        };
        let owned_feature = owner.filter(|&e| conforms(b.elements[e].ty, "Feature"));
        let key = if conforms(element.ty, "TypeFeaturing") {
            "featureOfType"
        } else if conforms(element.ty, "FeatureChaining") {
            "featureChained"
        } else if conforms(element.ty, "Conjugation") {
            "conjugatedType"
        } else if conforms(element.ty, "Specialization") {
            [
                "specific",
                "subclassifier",
                "typedFeature",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "crossingFeature",
            ]
            .into_iter()
            .find(|key| element.props.get(key).is_some())
            .unwrap_or("specific")
        } else {
            continue;
        };
        let ty = element.ty;
        let source = match element.props.get(key) {
            Some(value) => match value.as_reference() {
                Some(id) => {
                    let source = scanned.ids.get(&id).copied();
                    if source.is_none() {
                        scanned.unsatisfied.insert(id);
                    }
                    source
                }
                None => {
                    scanned.source_incomplete = true;
                    None
                }
            },
            None => {
                if conforms(ty, "TypeFeaturing") {
                    owned_feature
                } else {
                    owner
                }
            }
        };
        if conforms(ty, "TypeFeaturing") {
            if let Some(source) = source {
                if !conforms(b.elements[source].ty, "Feature") {
                    scanned.source_incomplete = true;
                }
                scanned.type_featurings.entry(source).or_default().push(rel);
            } else {
                // A missing standalone source might name any feature.
                scanned.source_incomplete = true;
            }
        } else if let Some(source) = source {
            if owner != Some(source) {
                if conforms(ty, "FeatureChaining") {
                    scanned.bad_chains.insert(source);
                } else {
                    scanned.bad_bases.insert(source);
                }
            }
        }
    }
    // Validate the annotation candidates the row scan gathered: no second
    // scan of the rows. We cannot ignore an annotation as non-metadata until
    // its ends and ownership agree.
    charge(steps, annotation_rows.len())?;
    scanned.logical_work = scanned.logical_work.saturating_add(annotation_rows.len());
    for relationship in annotation_rows {
        let before = *steps;
        let ends = annotation_ends(
            b,
            relationship,
            &scanned.carriers,
            &scanned.ids,
            &mut scanned.unsatisfied,
            steps,
        );
        scanned.logical_work = scanned
            .logical_work
            .saturating_add(steps.saturating_sub(before));
        charge(steps, 0)?;
        match ends {
            Some((source, Some(target))) if conforms(b.elements[source].ty, "MetadataFeature") => {
                scanned.metadata_annotation_targets.insert(target);
                if scanned.annotation_pairs.insert((source, target)) {
                    scanned
                        .metadata_annotation_sources
                        .entry(target)
                        .or_default()
                        .push(source);
                }
            }
            Some(_) => {}
            None => scanned.annotations_incomplete = true,
        }
    }
    Some(own)
}

impl StoredStructure {
    pub(super) fn has_import_rows(&self) -> bool {
        self.has_authored_import
            || self
                .import_rows
                .last()
                .is_some_and(|&row| row >= self.authored_end)
    }
    /// Import absence requires inverse owner claims as well as the owner's
    /// forward list. This is raw topology only, not an import contribution plan.
    pub(super) fn import_domains(
        &self,
        b: &Builder,
        steps: &mut usize,
    ) -> Option<Arc<ImportDomains>> {
        charge(steps, 1)?;
        if !self.is_current(b) || !self.ids_unique {
            return None;
        }
        if let Some(domains) = self.imports.get() {
            return Some(Arc::clone(domains));
        }
        let mut domains = ImportDomains::default();
        let mut claims: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut bad_relations = HashSet::new();
        let mut multiple_carriers = false;
        if self.has_import_rows() {
            charge(steps, self.import_rows.len())?;
            for &relationship in &self.import_rows {
                let row = &b.elements[relationship];
                let actual = match self.carriers[relationship] {
                    Carrier::Unique(owner) => Some(owner),
                    Carrier::Invalid => {
                        multiple_carriers = true;
                        bad_relations.insert(relationship);
                        None
                    }
                    _ => {
                        bad_relations.insert(relationship);
                        None
                    }
                };
                // No current publisher certifies generated Import semantics.
                // A mutated suffix row may not disappear from absence proofs.
                if relationship >= self.authored_end
                    || actual.is_some_and(|owner| !conforms(b.elements[owner].ty, "Namespace"))
                    || row.owning_relationship.is_some()
                    || !(row.children.is_empty()
                        || (row.ty == "NamespaceImport"
                            && row.children.len() == 1
                            && b.elements.get(row.children[0]).is_some_and(|child| {
                                child.ty == "Package"
                                    && child.owning_relationship == Some(relationship)
                                    && row
                                        .props
                                        .get("importedNamespace")
                                        .and_then(|v| v.as_reference())
                                        == Some(child.id)
                            })))
                {
                    bad_relations.insert(relationship);
                }
                let mut owners = HashSet::new();
                if let Some(owner) = actual {
                    owners.insert(owner);
                }
                let mut claim = |value: &crate::properties::Atom| match value
                    .as_reference()
                    .and_then(|id| self.ids.get(&id).copied())
                {
                    Some(owner) => {
                        owners.insert(owner);
                        if actual != Some(owner) || !conforms(b.elements[owner].ty, "Namespace") {
                            bad_relations.insert(relationship);
                        }
                    }
                    None => {
                        bad_relations.insert(relationship);
                        if !value.is_null() {
                            domains.unlocalized = true;
                        }
                    }
                };
                for key in ["owningRelatedElement", "importOwningNamespace"] {
                    charge(steps, 1)?;
                    if let Some(value) = row.props.get(key) {
                        claim(value);
                    }
                }
                let mut malformed_array = false;
                let mut bad_shape = false;
                for key in ["source", "relatedElement"] {
                    charge(steps, 1)?;
                    if let Some(value) = row.props.get(key) {
                        if let Some(values) = value.as_array() {
                            let count = if key == "source" {
                                values.len()
                            } else {
                                usize::from(!values.is_empty())
                            };
                            charge(steps, count)?;
                            bad_shape |= values.len() != if key == "source" { 1 } else { 2 };
                            for value in values.iter().take(count) {
                                claim(value);
                            }
                        } else {
                            malformed_array = true;
                        }
                    }
                }
                if malformed_array {
                    domains.unlocalized = true;
                }
                if malformed_array || bad_shape {
                    bad_relations.insert(relationship);
                }
                if row
                    .props
                    .get("isRecursive")
                    .is_some_and(|v| v.as_bool() != Some(false))
                {
                    charge(steps, owners.len())?;
                    domains.recursive_owners.extend(owners.iter().copied());
                }
                claims.insert(relationship, owners);
            }
        }
        if multiple_carriers {
            // Only contradictory duplicate-carrier imports need the full owner
            // recovery scan. Ordinary and orphan imports use the indexed rows.
            charge(steps, self.authored_end)?;
            for owner in 0..self.authored_end {
                let relationships = &b.elements[owner].owned_relationships;
                charge(steps, relationships.len())?;
                for &relationship in relationships {
                    if self.carriers.get(relationship) == Some(&Carrier::Invalid)
                        && b.elements
                            .get(relationship)
                            .is_some_and(|r| conforms(r.ty, "Import"))
                    {
                        claims.entry(relationship).or_default().insert(owner);
                    }
                }
            }
        }
        charge(steps, bad_relations.len())?;
        for relationship in bad_relations {
            let owners = claims.get(&relationship)?;
            charge(steps, owners.len())?;
            if owners.is_empty() {
                domains.unlocalized = true;
            } else {
                domains.bad_owners.extend(owners.iter().copied());
            }
        }
        let domains = Arc::new(domains);
        let _ = self.imports.set(Arc::clone(&domains));
        Some(Arc::clone(self.imports.get().unwrap()))
    }

    /// Lazy inverse check of every authored Membership owner and owned-member
    /// backlink. Forward enumeration alone cannot prove a result/input unique.
    /// This index depends only on this raw row revision; generated ownership is
    /// checked by the existing semantic overlay at the consumer boundary.
    ///
    /// A structure that extended the kept scan of the frozen rows extends their
    /// kept domains with its own rows, charging the budget the frozen rows'
    /// projection charged again, so the budget reads as a whole projection's.
    /// A row of its own naming a frozen relationship as its owning membership
    /// would read that relationship's claims, which only a whole projection
    /// gathers together: such a structure projects every row.
    pub(super) fn membership_domains(
        &self,
        b: &Builder,
        steps: &mut usize,
    ) -> Option<Arc<MembershipDomains>> {
        charge(steps, 1)?;
        if !self.is_current(b) || !self.ids_unique {
            return None;
        }
        if let Some(domains) = self.memberships.get() {
            return Some(Arc::clone(domains));
        }
        let whole = |steps: &mut usize| {
            project_memberships(
                b,
                &self.carriers,
                &self.ids,
                &self.membership_rows,
                0..self.authored_end,
                self.multiple_membership_carriers,
                steps,
            )
            .map(|domains| domains.expect("a whole projection claims no earlier row"))
        };
        let domains = match self.prefix.as_ref().and_then(|prefix| {
            prefix
                .memberships(b)
                .map(|frozen| (prefix.rows(), &prefix.scanned, frozen))
        }) {
            Some((floor, frozen_scan, frozen)) => {
                let before = *steps;
                charge(steps, frozen.steps)?;
                // A whole projection visits every owner when any membership
                // row has several carriers; the frozen rows' projection did
                // only when one of theirs had.
                if self.multiple_membership_carriers && !frozen_scan.multiple_membership_carriers {
                    charge(steps, floor.saturating_add(frozen.owner_relationships))?;
                }
                let start = self.membership_rows.partition_point(|&r| r < floor);
                match project_memberships(
                    b,
                    &self.carriers,
                    &self.ids,
                    &self.membership_rows[start..],
                    floor..self.authored_end,
                    self.multiple_membership_carriers,
                    steps,
                )? {
                    Some(own) => MembershipDomains {
                        bad_owners: own.bad_owners,
                        unlocalized: own.unlocalized || frozen.domains.unlocalized,
                        frozen: Some(Arc::clone(&frozen.domains)),
                    },
                    None => {
                        *steps = before;
                        whole(steps)?
                    }
                }
            }
            None => whole(steps)?,
        };
        let domains = Arc::new(domains);
        let _ = self.memberships.set(Arc::clone(&domains));
        Some(domains)
    }

    /// Actual amortized work for a new projection. The legacy get() logical
    /// charge is unchanged, including after this optional projection is built.
    ///
    /// A structure that extended the kept scan of the frozen rows projects only
    /// its own rows and reads a frozen feature's entry from the frozen rows'
    /// kept projection, charging the budget that projection charged again. A
    /// row of its own naming a frozen feature as its source would add to that
    /// feature's entry: such a structure projects every row.
    pub(super) fn typing(&self, b: &Builder, steps: &mut usize) -> Option<Arc<StoredTyping>> {
        charge(steps, 1)?;
        if !self.is_current(b) {
            return None;
        }
        if let Some(typing) = self.typing.get() {
            return Some(Arc::clone(typing));
        }
        let whole = |steps: &mut usize| {
            let (own, sources_incomplete) =
                project_typing(b, &self.carriers, &self.ids, &self.typing_rows, 0, steps)?
                    .expect("a whole projection names no earlier source");
            Some(StoredTyping {
                relationships: TypingSources { own, frozen: None },
                sources_incomplete,
            })
        };
        let typing = match self
            .prefix
            .as_ref()
            .and_then(|prefix| prefix.typing(b).map(|frozen| (prefix.rows(), frozen)))
        {
            Some((floor, frozen)) => {
                let before = *steps;
                charge(steps, frozen.steps)?;
                let start = self.typing_rows.partition_point(|&r| r < floor);
                match project_typing(
                    b,
                    &self.carriers,
                    &self.ids,
                    &self.typing_rows[start..],
                    floor,
                    steps,
                )? {
                    Some((own, sources_incomplete)) => StoredTyping {
                        relationships: TypingSources {
                            own,
                            frozen: Some(Arc::clone(&frozen.typing)),
                        },
                        sources_incomplete: sources_incomplete || frozen.typing.sources_incomplete,
                    },
                    None => {
                        *steps = before;
                        whole(steps)?
                    }
                }
            }
            None => whole(steps)?,
        };
        charge(steps, 0)?;
        let typing = Arc::new(typing);
        // A concurrent structural reader could win publication; either value
        // describes this same immutable row epoch. No proof facts are cached.
        let _ = self.typing.set(Arc::clone(&typing));
        Some(Arc::clone(self.typing.get().unwrap()))
    }

    /// Whether this structure extends the kept scan of the `floor` frozen rows
    /// and its own authored rows leave what the projections hold for the
    /// frozen rows as the frozen rows' own projections give it: no typing row
    /// of its own names a frozen feature as its source, and none of its own
    /// rows contradicts a frozen owner's memberships. Materialized implied
    /// relationships name library types as their sources by design; they are
    /// not authored, and the planners do not read them.
    pub(super) fn extends_frozen_rows(
        &self,
        b: &Builder,
        floor: usize,
        steps: &mut usize,
    ) -> Option<bool> {
        let Some(prefix) = &self.prefix else {
            return Some(false);
        };
        if prefix.rows() != floor {
            return Some(false);
        }
        let own = self.typing_rows.partition_point(|&r| r < floor)
            ..self.typing_rows.partition_point(|&r| r < self.authored_end);
        let authored = &self.typing_rows[own];
        if project_typing(b, &self.carriers, &self.ids, authored, floor, steps)?.is_none() {
            return Some(false);
        }
        if self.ids_unique {
            let domains = self.membership_domains(b, steps)?;
            if domains.frozen.is_none() || domains.bad_owners.iter().any(|&owner| owner < floor) {
                return Some(false);
            }
        }
        Some(true)
    }

    pub(super) fn is_current(&self, b: &Builder) -> bool {
        self.authored_end == b.implied_from.unwrap_or(b.elements.len())
            && self
                .revision
                .as_ref()
                .zip(b.elements.revision())
                .is_some_and(|(stored, current)| stored.same_as(current))
    }
    /// New annotation absence consumers pay construction once, then actual
    /// O(1) immutable-index access. This intentionally differs from get(), whose
    /// legacy TypeRelations caller retains its historical logical scan charge.
    /// No proof result is cached; only current raw topology may be reused.
    pub(super) fn for_annotations(b: &mut Builder, steps: &mut usize) -> Option<Arc<Self>> {
        Self::for_query(b, steps)
    }
    /// Amortized structural access for new bounded proof consumers. Existing
    /// get() callers retain their historical logical scan charge.
    pub(super) fn for_query(b: &mut Builder, steps: &mut usize) -> Option<Arc<Self>> {
        if let Some(stored) = b.stored_structure.as_ref().filter(|s| s.is_current(b)) {
            charge(steps, 1)?;
            let stored = Arc::clone(stored);
            // Sharing an existing immutable UUID map is also O(1), including
            // after a caller cleared lookup caches without changing rows.
            b.id_index = Some(Arc::clone(&stored.ids));
            b.id_index_built_for = b.elements.len();
            Some(stored)
        } else {
            Self::get(b, steps)
        }
    }
    pub(super) fn get(b: &mut Builder, steps: &mut usize) -> Option<Arc<Self>> {
        charge(steps, 1)?;
        let n = b.elements.len();
        if let Some(stored) = b.stored_structure.as_ref().filter(|s| s.is_current(b)) {
            charge(steps, stored.logical_work)?;
            if b.id_index.is_none() || b.id_index_built_for != n {
                charge(steps, n)?;
            }
            // The same immutable UUID projection is shared, not rebuilt or
            // copied. This also restores it after explicit cache clearing.
            let stored = Arc::clone(stored);
            b.id_index = Some(Arc::clone(&stored.ids));
            b.id_index_built_for = n;
            return Some(stored);
        }
        charge(steps, n)?;
        if b.id_index.is_none() || b.id_index_built_for != n {
            charge(steps, n)?;
        }
        let authored_end = b.implied_from.unwrap_or(n);
        let (scanned, prefix) = Self::scanned(b, authored_end, steps)?;
        let stored = Arc::new(Self {
            revision: Some(b.elements.observe_revision()),
            authored_end,
            logical_work: scanned.logical_work,
            ids: Arc::new(scanned.ids),
            carriers: scanned.carriers,
            multiple_membership_carriers: scanned.multiple_membership_carriers,
            type_featurings: scanned.type_featurings,
            bad_chains: scanned.bad_chains,
            bad_bases: scanned.bad_bases,
            source_incomplete: scanned.source_incomplete,
            typing: OnceLock::new(),
            typing_rows: scanned.typing_rows,
            memberships: OnceLock::new(),
            membership_rows: scanned.membership_rows,
            imports: OnceLock::new(),
            ids_unique: scanned.ids_unique,
            has_authored_import: scanned.has_authored_import,
            has_recursive_import: scanned.has_recursive_import,
            import_rows: scanned.import_rows,
            metadata_annotation_targets: scanned.metadata_annotation_targets,
            metadata_annotation_sources: scanned.metadata_annotation_sources,
            annotations_incomplete: scanned.annotations_incomplete,
            prefix,
        });
        b.id_index = Some(Arc::clone(&stored.ids));
        b.id_index_built_for = n;
        b.stored_structure = Some(Arc::clone(&stored));
        Some(stored)
    }

    /// The scan behind a structure over every row: the frozen rows from the
    /// scan their freeze kept, or one made and kept here, while no frozen
    /// row has been written and the implied rows lie past them; the rows
    /// after the frozen ones every time. A table without frozen rows, with
    /// one written since, or with a later row claiming a frozen row or an
    /// id a frozen reference named (see [`PrefixStructure`]) is scanned
    /// whole. With the scan, the kept scan it extended (`None` when whole).
    fn scanned(
        b: &mut Builder,
        authored_end: usize,
        steps: &mut usize,
    ) -> Option<(Scanned, Option<Arc<PrefixStructure>>)> {
        let n = b.elements.len();
        let base_len = b.elements.base_len();
        let whole = |b: &Builder, steps: &mut usize| {
            let mut scanned = Scanned::new(n);
            scan(b, &mut scanned, 0, n, authored_end, steps)?;
            Some((scanned, None))
        };
        if base_len == 0 || !b.elements.base_untouched() || authored_end < base_len {
            return whole(b, steps);
        }
        let before = *steps;
        let kept = b
            .prefix_structure
            .as_ref()
            .filter(|prefix| Arc::ptr_eq(&prefix.base, b.elements.base_arc()));
        let reused = kept.is_some();
        let prefix = match kept {
            Some(prefix) => {
                // the budget a scan of those rows would charge
                charge(steps, prefix.scanned.steps)?;
                Arc::clone(prefix)
            }
            None => {
                let prefix = Arc::new(PrefixStructure::scan(b, steps)?);
                b.prefix_structure = Some(Arc::clone(&prefix));
                prefix
            }
        };
        let mut scanned = prefix.scanned.clone();
        if !scan(b, &mut scanned, base_len, n, authored_end, steps)? {
            // A row of this build claims a frozen relationship or a frozen
            // row's id, which the kept scan read as the frozen rows' own:
            // scan whole, charging what a whole scan charges.
            *steps = before;
            return whole(b, steps);
        }
        if reused {
            note_prefix_reuse();
        }
        Some((scanned, Some(prefix)))
    }

    /// The scan of a table's frozen rows, for its freeze to keep: `None`
    /// without frozen rows, with one written since, or past the budget.
    pub(crate) fn prefix_of(b: &Builder) -> Option<Arc<PrefixStructure>> {
        if b.elements.base_len() == 0 || !b.elements.base_untouched() {
            return None;
        }
        let mut steps = 0;
        PrefixStructure::scan(b, &mut steps).map(Arc::new)
    }

    pub(super) fn incomplete(&self) -> bool {
        !self.ids_unique || self.source_incomplete
    }

    /// Resolve an endpoint in this exact, unique structural snapshot. Consumers
    /// need not depend on the mutable ambient Builder lookup-cache lifecycle.
    pub(super) fn element_for_uuid(&self, b: &Builder, id: Uuid) -> Option<usize> {
        (self.ids_unique && self.is_current(b))
            .then(|| self.ids.get(&id).copied())
            .flatten()
    }

    /// Raw carrier cardinality without scalar alias agreement. A semantic
    /// overlay may combine Missing with certified generated ownership; Invalid
    /// must never become valid merely because an override supplies an owner.
    pub(super) fn raw_carrier(&self, b: &Builder, rel: usize) -> Option<Carrier> {
        self.is_current(b)
            .then(|| self.carriers.get(rel).copied())
            .flatten()
    }

    pub(super) fn carrier(&self, b: &Builder, rel: usize) -> Option<Option<usize>> {
        let owner = match self.raw_carrier(b, rel)? {
            Carrier::Missing => None,
            Carrier::Unique(owner) => Some(owner),
            Carrier::Invalid => return None,
        };
        if let Some(value) = b.elements.get(rel)?.props.get("owningRelatedElement") {
            if value.as_reference() != owner.map(|e| b.elements[e].id) {
                return None;
            }
        }
        Some(owner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    fn fixture() -> ResolvedModel {
        let mut model = Model::new();
        let parsed = model.add_source(
            "structural.kerml",
            "class A {feature x;} class B; featuring A::x by B;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        ResolvedModel::build(&model)
    }

    #[test]
    fn cache_hit_preserves_logical_budget_and_does_not_rebuild() {
        let mut r = fixture();
        let first_id = r.b.elements[0].id;
        r.b.element_index_of_uuid(first_id);
        let mut cold_steps = 0;
        let cold = StoredStructure::get(&mut r.b, &mut cold_steps).unwrap();
        let mut warm_steps = 0;
        let warm = StoredStructure::get(&mut r.b, &mut warm_steps).unwrap();
        assert!(Arc::ptr_eq(&cold, &warm));
        assert_eq!(cold_steps, warm_steps);
        r.b.id_index = None;
        let mut cleared_steps = 0;
        let restored = StoredStructure::get(&mut r.b, &mut cleared_steps).unwrap();
        assert!(Arc::ptr_eq(&warm, &restored));
        assert_eq!(cleared_steps, warm_steps + r.b.elements.len());
        assert!(Arc::ptr_eq(r.b.id_index.as_ref().unwrap(), &restored.ids));
    }

    #[test]
    fn clone_and_freeze_share_only_unchanged_rows() {
        let mut r = fixture();
        let x = r.resolve_qualified("A::x").unwrap().0;
        let membership = r.b.elements[x].owning_relationship.unwrap();
        let original = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        r.b.elements.freeze();
        assert!(Arc::ptr_eq(
            &original,
            &StoredStructure::get(&mut r.b, &mut 0).unwrap()
        ));
        let mut copy = r.b.clone();
        assert!(Arc::ptr_eq(
            &original,
            &StoredStructure::get(&mut copy, &mut 0).unwrap()
        ));
        let owner = original.carrier(&copy, membership).unwrap().unwrap();
        copy.elements[owner].owned_relationships.push(membership);
        assert!(!original.is_current(&copy));
        let changed = StoredStructure::get(&mut copy, &mut 0).unwrap();
        assert!(!Arc::ptr_eq(&original, &changed));
        assert_eq!(changed.carrier(&copy, membership), None);
        assert_eq!(original.carrier(&r.b, membership), Some(Some(owner)));
        assert!(Arc::ptr_eq(
            &original,
            &StoredStructure::get(&mut r.b, &mut 0).unwrap()
        ));
    }

    #[test]
    fn same_length_ids_and_provenance_invalidate_without_stale_uuid_resolution() {
        let mut r = fixture();
        let x = r.resolve_qualified("A::x").unwrap().0;
        let original = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(original.type_featurings.contains_key(&x));
        let old_id = r.b.elements[x].id;
        let new_id = Uuid::from_u128(0x7825786254891);
        r.b.elements[x].id = new_id;
        let changed = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!Arc::ptr_eq(&original, &changed));
        assert!(
            changed.incomplete(),
            "old inverse source must become unresolved"
        );
        assert_eq!(r.b.element_index_of_uuid(new_id), Some(x));
        assert_eq!(r.b.element_index_of_uuid(old_id), None);
        r.b.implied_from = Some(0);
        let generated = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!Arc::ptr_eq(&changed, &generated));
        assert!(generated.type_featurings.is_empty());
        assert!(!generated.incomplete());
    }

    #[test]
    fn failed_budget_or_invalid_carrier_never_publishes_partial_index() {
        let mut r = fixture();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(StoredStructure::get(&mut r.b, &mut exhausted).is_none());
        assert!(r.b.stored_structure.is_none());
        let complete = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        exhausted = crate::eval::MAX_STEPS - 1;
        assert!(StoredStructure::get(&mut r.b, &mut exhausted).is_none());
        assert!(Arc::ptr_eq(
            &complete,
            r.b.stored_structure.as_ref().unwrap()
        ));
        assert!(Arc::ptr_eq(
            &complete,
            &StoredStructure::get(&mut r.b, &mut 0).unwrap()
        ));
        let out_of_range = r.b.elements.len();
        r.b.elements[0].owned_relationships.push(out_of_range);
        assert!(StoredStructure::get(&mut r.b, &mut 0).is_none());
        assert!(!complete.is_current(&r.b));
        assert_eq!(
            r.b.elements[0].owned_relationships.make_mut().pop(),
            Some(out_of_range)
        );
        let repaired = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!Arc::ptr_eq(&complete, &repaired));
        assert!(repaired.is_current(&r.b));
        assert!(!repaired.incomplete());
        assert!(Arc::ptr_eq(
            &repaired,
            &StoredStructure::get(&mut r.b, &mut 0).unwrap()
        ));
    }
}

#[cfg(test)]
mod import_completeness_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    fn fixture() -> (ResolvedModel, usize, usize, usize, usize) {
        let mut model = Model::new();
        let parsed = model.add_source(
            "import-domains.kerml",
            "package P {feature x;} package A {private import P::*;} package B; package Unrelated;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let u = r.resolve_qualified("Unrelated").unwrap().0;
        let import = r.b.elements[a]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| conforms(r.b.elements[rel].ty, "Import"))
            .unwrap();
        (r, a, b, u, import)
    }

    #[test]
    fn inverse_import_claims_localize_actual_and_claimed_owners() {
        for key in [
            "owningRelatedElement",
            "importOwningNamespace",
            "source",
            "relatedElement",
        ] {
            let (mut r, a, b, u, import) = fixture();
            let claim = serde_json::json!({"@id": r.b.elements[b].id.to_string()});
            let value = match key {
                "source" => serde_json::json!([claim]),
                "relatedElement" => {
                    let p = r.resolve_qualified("P").unwrap().0;
                    serde_json::json!([claim, {"@id": r.b.elements[p].id.to_string()}])
                }
                _ => claim,
            };
            r.b.set(import, key, value);
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            let domains = raw.import_domains(&r.b, &mut 0).unwrap();
            assert!(!domains.owner_complete(a), "{key}");
            assert!(!domains.owner_complete(b), "{key}");
            assert!(domains.owner_complete(u), "{key}");
        }
    }

    #[test]
    fn orphan_and_duplicate_import_carriers_do_not_hide_inverse_claims() {
        for duplicate in [false, true] {
            let (mut r, a, b, u, import) = fixture();
            if duplicate {
                r.b.elements[b].owned_relationships.push(import);
            } else {
                r.b.elements[a]
                    .owned_relationships
                    .make_mut()
                    .retain(|&rel| rel != import);
            }
            r.b.set(import, "isImplied", serde_json::json!(true));
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            let domains = raw.import_domains(&r.b, &mut 0).unwrap();
            assert!(!domains.owner_complete(a));
            assert_eq!(domains.owner_complete(b), !duplicate);
            assert!(domains.owner_complete(u));
        }
    }

    #[test]
    fn unknown_import_owner_claims_block_absence_without_inventing_an_owner() {
        for value in [
            serde_json::json!({"@ref": "Missing"}),
            serde_json::json!(false),
        ] {
            let (mut r, a, _, u, import) = fixture();
            r.b.set(import, "importOwningNamespace", value);
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            let domains = raw.import_domains(&r.b, &mut 0).unwrap();
            assert!(!domains.owner_complete(a));
            assert!(!domains.owner_complete(u));
        }
    }

    #[test]
    fn import_domain_is_lazy_budgeted_shared_and_revision_bound() {
        let (mut r, a, b, _, import) = fixture();
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(raw.imports.get().is_none());
        assert!(
            raw.import_domains(&r.b, &mut (crate::eval::MAX_STEPS - 1))
                .is_none()
        );
        assert!(raw.imports.get().is_none());
        let first = raw.import_domains(&r.b, &mut 0).unwrap();
        assert!(first.owner_complete(a));
        let mut warm = 0;
        let second = raw.import_domains(&r.b, &mut warm).unwrap();
        assert!(Arc::ptr_eq(&first, &second));
        assert_eq!(warm, 1);
        let id = r.b.elements[b].id;
        r.b.set(
            import,
            "importOwningNamespace",
            serde_json::json!({"@id": id.to_string()}),
        );
        assert!(raw.import_domains(&r.b, &mut 0).is_none());
        let changed = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        let domains = changed.import_domains(&r.b, &mut 0).unwrap();
        assert!(!domains.owner_complete(a));
        assert!(!domains.owner_complete(b));
        let id = r.b.elements[a].id;
        r.b.set(
            import,
            "importOwningNamespace",
            serde_json::json!({"@id": id.to_string()}),
        );
        let repaired = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(
            repaired
                .import_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(a)
        );
    }

    #[test]
    fn suffix_import_rows_cannot_escape_the_authored_domain_scan() {
        let (mut r, a, _, u, import) = fixture();
        r.b.implied_from = Some(import);
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(raw.has_import_rows());
        let domains = raw.import_domains(&r.b, &mut 0).unwrap();
        assert!(!domains.owner_complete(a));
        assert!(domains.owner_complete(u));
    }
}

#[cfg(test)]
mod annotation_completeness_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    fn annotation_fixture() -> (ResolvedModel, usize, usize, usize) {
        let mut model = Model::new();
        let p = model.add_source(
            "annotations.kerml",
            "metaclass M; class A; class B; @M about A;",
        );
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let rel =
            r.b.elements
                .iter()
                .position(|e| e.ty == "Annotation")
                .unwrap();
        (r, a, b, rel)
    }
    #[test]
    fn valid_annotation_records_target_and_non_metadata_is_ignored_only_after_validation() {
        let (mut r, a, _, rel) = annotation_fixture();
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!raw.annotations_incomplete);
        assert!(raw.metadata_annotation_targets.contains(&a));
        let source = raw.carrier(&r.b, rel).unwrap().unwrap();
        r.b.elements[source].ty = "Documentation";
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!raw.annotations_incomplete);
        assert!(raw.metadata_annotation_targets.is_empty());
        let owner = r.b.elements[source].id;
        let wrong_source = r.b.elements[a].id;
        r.b.elements[rel].props.insert(
            "source",
            serde_json::json!([{"@id":wrong_source.to_string()}]),
        );
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(
            raw.annotations_incomplete,
            "a corrupt nonmetadata source must not prove absence for another target"
        );
        r.b.elements[rel]
            .props
            .insert("source", serde_json::json!([{"@id":owner.to_string()}]));
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(!raw.annotations_incomplete);
    }
    #[test]
    fn contradictory_annotation_target_has_global_uncertainty_and_repair_rebuilds() {
        for key in ["target", "relatedElement", "owningRelatedElement"] {
            let (mut r, a, b, rel) = annotation_fixture();
            let old = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            let owner = old.carrier(&r.b, rel).unwrap().unwrap();
            let value = match key {
                "target" => serde_json::json!([{"@id":r.b.elements[b].id.to_string()}]),
                "relatedElement" => {
                    serde_json::json!([{"@id":r.b.elements[owner].id.to_string()},{"@id":r.b.elements[b].id.to_string()}])
                }
                _ => serde_json::json!({"@id":r.b.elements[b].id.to_string()}),
            };
            let original_props = r.b.elements[rel].props.clone();
            r.b.elements[rel].props.insert(key, value);
            let new = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(new.annotations_incomplete, "{key}");
            assert!(!Arc::ptr_eq(&old, &new));
            assert!(!new.metadata_annotation_targets.contains(&b));
            r.b.elements[rel].props = original_props;
            let repaired = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(!repaired.annotations_incomplete);
            assert!(repaired.metadata_annotation_targets.contains(&a));
        }
    }

    /// Start from actual lowered rows, then express the other normative ownership
    /// shape: annotated A carries Annotation, which owns the annotating element.
    fn owned_annotation_fixture(documentation: bool) -> (ResolvedModel, usize, usize, usize) {
        let (mut r, target, _, rel) = annotation_fixture();
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        let source = raw.carrier(&r.b, rel).unwrap().unwrap();
        let old_membership = r.b.elements[source].owning_relationship.unwrap();
        let source_id = r.b.elements[source].id;
        let target_id = r.b.elements[target].id;
        let rel_id = r.b.elements[rel].id;
        // Retain a non-owning namespace membership for the source identity.
        r.b.elements[old_membership].ty = "Membership";
        r.b.elements[old_membership].children.make_mut().clear();
        r.b.elements[old_membership].props = Default::default();
        r.b.elements[old_membership].props.insert(
            "memberElement",
            serde_json::json!({"@id":source_id.to_string()}),
        );
        r.b.elements[source]
            .owned_relationships
            .make_mut()
            .retain(|&r| r != rel);
        r.b.elements[source].owning_relationship = Some(rel);
        r.b.elements[source].props.insert(
            "owningRelationship",
            serde_json::json!({"@id":rel_id.to_string()}),
        );
        r.b.elements[target].owned_relationships.push(rel);
        r.b.elements[rel].children = vec![source].into();
        r.b.elements[rel].props = Default::default();
        r.b.elements[rel].props.insert(
            "annotatedElement",
            serde_json::json!({"@id":target_id.to_string()}),
        );
        r.b.elements[rel].props.insert(
            "annotatingElement",
            serde_json::json!({"@id":source_id.to_string()}),
        );
        r.b.elements[rel].props.insert(
            "ownedAnnotatingElement",
            serde_json::json!({"@id":source_id.to_string()}),
        );
        r.b.elements[rel].props.insert(
            "owningAnnotatedElement",
            serde_json::json!({"@id":target_id.to_string()}),
        );
        r.b.elements[rel].props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":target_id.to_string()}),
        );
        r.b.elements[rel].props.insert(
            "ownedRelatedElement",
            serde_json::json!([{"@id":source_id.to_string()}]),
        );
        if documentation {
            r.b.elements[source].ty = "Documentation";
        }
        (r, target, source, rel)
    }

    #[test]
    fn target_owned_annotation_admits_metadata_and_valid_documentation_only() {
        for documentation in [false, true] {
            let (mut r, target, _, _) = owned_annotation_fixture(documentation);
            let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(!raw.annotations_incomplete);
            assert_eq!(
                raw.metadata_annotation_targets.contains(&target),
                !documentation
            );
        }
    }

    #[test]
    fn owned_annotation_duplicate_children_and_missing_backlink_cannot_prove_absence() {
        for duplicate in [false, true] {
            // Even a Documentation source must be structurally valid before it is
            // excluded from possible semantic metadata evidence.
            let (mut r, _, source, rel) = owned_annotation_fixture(true);
            if duplicate {
                let id = r.b.elements[source].id;
                r.b.elements[rel].children.push(source);
                r.b.elements[rel].props.insert(
                    "ownedRelatedElement",
                    serde_json::json!([{"@id":id.to_string()}, {"@id":id.to_string()}]),
                );
            } else {
                r.b.elements[source].owning_relationship = None;
            }
            let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(raw.annotations_incomplete);
        }
    }

    #[test]
    fn owned_annotation_child_scalar_backlink_must_match_topology() {
        let (mut r, target, source, rel) = owned_annotation_fixture(true);
        let wrong = r.b.elements[target].id;
        r.b.elements[source].props.insert(
            "owningRelationship",
            serde_json::json!({"@id":wrong.to_string()}),
        );
        assert!(
            StoredStructure::get(&mut r.b, &mut 0)
                .unwrap()
                .annotations_incomplete
        );
        let correct = r.b.elements[rel].id;
        r.b.elements[source].props.insert(
            "owningRelationship",
            serde_json::json!({"@id":correct.to_string()}),
        );
        assert!(
            !StoredStructure::get(&mut r.b, &mut 0)
                .unwrap()
                .annotations_incomplete
        );
    }
    #[test]
    fn unresolved_nonmetadata_target_requires_complete_source_certificate() {
        for key in [
            "annotatingElement",
            "owningAnnotatingElement",
            "ownedAnnotatingElement",
            "owningRelatedElement",
            "source",
            "relatedElement",
            "ownedRelatedElement",
        ] {
            let (mut r, a, _, rel) = annotation_fixture();
            let source = StoredStructure::get(&mut r.b, &mut 0)
                .unwrap()
                .carrier(&r.b, rel)
                .unwrap()
                .unwrap();
            r.b.elements[source].ty = "Comment";
            r.b.elements[rel]
                .props
                .insert("annotatedElement", serde_json::json!({"@ref":"Missing"}));
            let good = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(!good.annotations_incomplete);
            assert!(good.metadata_annotation_targets.is_empty());
            let wrong = r.b.elements[a].id.to_string();
            let value = match key {
                "source" | "ownedRelatedElement" => serde_json::json!([{"@id":wrong}]),
                "relatedElement" => serde_json::json!([{"@id":wrong},{"@ref":"Missing"}]),
                _ => serde_json::json!({"@id":wrong}),
            };
            r.b.elements[rel].props.insert(key, value);
            assert!(
                StoredStructure::get(&mut r.b, &mut 0)
                    .unwrap()
                    .annotations_incomplete,
                "{key}"
            );
        }
    }
    #[test]
    fn unresolved_metadata_target_still_qualifies_every_candidate_target() {
        let (mut r, _, _, rel) = annotation_fixture();
        r.b.elements[rel]
            .props
            .insert("annotatedElement", serde_json::json!({"@ref":"Missing"}));
        assert!(
            StoredStructure::get(&mut r.b, &mut 0)
                .unwrap()
                .annotations_incomplete
        );
    }
    #[test]
    fn owned_documentation_source_can_be_certified_independently_of_target() {
        for conflicting in [false, true] {
            let (mut r, _, source, rel) = owned_annotation_fixture(true);
            r.b.elements[rel]
                .props
                .insert("annotatedElement", serde_json::json!({"@ref":"Missing"}));
            r.b.elements[rel].props.insert(
                "owningAnnotatedElement",
                serde_json::json!({"@ref":"Missing"}),
            );
            let old = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert!(!old.annotations_incomplete);
            if conflicting {
                // A second possible metadata source must defeat the certificate.
                let metadata =
                    r.b.elements
                        .iter()
                        .position(|e| e.ty == "Metaclass")
                        .unwrap();
                r.b.elements[metadata].ty = "MetadataFeature";
                let id = r.b.elements[metadata].id.to_string();
                r.b.elements[rel]
                    .props
                    .insert("annotatingElement", serde_json::json!({"@id":id}));
                assert!(
                    StoredStructure::get(&mut r.b, &mut 0)
                        .unwrap()
                        .annotations_incomplete
                );
            } else {
                r.b.elements[source].ty = "MetadataFeature";
                let mut exhausted = crate::eval::MAX_STEPS;
                assert!(StoredStructure::get(&mut r.b, &mut exhausted).is_none());
                let new = StoredStructure::get(&mut r.b, &mut 0).unwrap();
                assert!(!Arc::ptr_eq(&old, &new));
                assert!(new.annotations_incomplete);
            }
        }
    }
}
#[cfg(test)]
mod typing_cache_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn typing_projection_is_lazy_budgeted_shared_and_row_bound() {
        let mut model = Model::new();
        assert!(
            model
                .add_source("typing-cache.kerml", "class A; class B; feature x:A;")
                .diagnostics
                .is_empty()
        );
        let unrelated: String = (0..1_000).map(|i| format!("class Unrelated{i};")).collect();
        assert!(
            model
                .add_source("unrelated.kerml", &unrelated)
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("x").unwrap().0;
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let structure = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(structure.typing.get().is_none());
        let mut before = 0;
        StoredStructure::get(&mut r.b, &mut before).unwrap();
        let mut exhausted = crate::eval::MAX_STEPS - 1;
        assert!(structure.typing(&r.b, &mut exhausted).is_none());
        assert!(
            structure.typing.get().is_none(),
            "failed construction must not publish"
        );
        let mut cold = 0;
        let typing = structure.typing(&r.b, &mut cold).unwrap();
        assert_eq!(cold, 1 + structure.typing_rows.len());
        let rel = typing.relationships[&x][0];
        let mut warm = 0;
        assert!(Arc::ptr_eq(
            &typing,
            &structure.typing(&r.b, &mut warm).unwrap()
        ));
        assert_eq!(warm, 1);
        let mut after = 0;
        StoredStructure::get(&mut r.b, &mut after).unwrap();
        assert_eq!(before, after, "legacy logical charge is unchanged");
        let a_id = r.b.elements[a].id;
        let b_id = r.b.elements[b].id;
        assert_eq!(
            r.b.elements[rel]
                .props
                .get("type")
                .and_then(|v| v.as_reference()),
            Some(a_id)
        );
        r.b.elements[rel]
            .props
            .insert("type", super::super::id_ref(b_id));
        assert!(structure.typing(&r.b, &mut 0).is_none());
        let rebuilt = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(!Arc::ptr_eq(&structure, &rebuilt));
        assert!(rebuilt.typing.get().is_none());
        assert!(!Arc::ptr_eq(
            &typing,
            &rebuilt.typing(&r.b, &mut 0).unwrap()
        ));
    }
}

#[cfg(test)]
mod membership_domain_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    fn fixture() -> ResolvedModel {
        let mut model = Model::new();
        model.add_source(
            "memberships.kerml",
            "function A {return a;} function B {return b;} function Unrelated {return u;}",
        );
        ResolvedModel::build(&model)
    }
    #[test]
    fn every_inverse_owner_alias_localizes_a_lying_membership() {
        for key in [
            "owningRelatedElement",
            "membershipOwningNamespace",
            "owningType",
            "source",
            "relatedElement",
        ] {
            let mut r = fixture();
            let a = r.resolve_qualified("A").unwrap().0;
            let b = r.resolve_qualified("B").unwrap().0;
            let u = r.resolve_qualified("Unrelated").unwrap().0;
            let child = r.resolve_qualified("B::b").unwrap().0;
            let membership = r.b.elements[child].owning_relationship.unwrap();
            let value = serde_json::json!({"@id":r.b.elements[a].id.to_string()});
            let value = if key == "source" {
                serde_json::json!([value])
            } else if key == "relatedElement" {
                serde_json::json!([value,{"@id":r.b.elements[child].id.to_string()}])
            } else {
                value
            };
            r.b.set(membership, key, value);
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            let domains = raw.membership_domains(&r.b, &mut 0).unwrap();
            assert!(!domains.owner_complete(a), "{key}");
            assert!(!domains.owner_complete(b), "{key}");
            assert!(domains.owner_complete(u), "{key}");
        }
    }
    #[test]
    fn inverse_child_aliases_and_unlisted_owning_type_are_not_ignored() {
        for key in [
            "owningRelationship",
            "owningMembership",
            "owningFeatureMembership",
            "owningParameterMembership",
            "owningType",
        ] {
            let mut r = fixture();
            let a = r.resolve_qualified("A").unwrap().0;
            let ar = r.resolve_qualified("A::a").unwrap().0;
            let u = r.resolve_qualified("Unrelated").unwrap().0;
            let child = r.resolve_qualified("B::b").unwrap().0;
            let target = if key == "owningType" {
                a
            } else {
                r.b.elements[ar].owning_relationship.unwrap()
            };
            let id = r.b.elements[target].id;
            r.b.set(child, key, serde_json::json!({"@id":id.to_string()}));
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            let domains = raw.membership_domains(&r.b, &mut 0).unwrap();
            assert!(!domains.owner_complete(a), "{key}");
            assert!(domains.owner_complete(u), "{key}");
        }
    }
    #[test]
    fn unresolved_owner_claim_refuses_without_fabricating_an_owner() {
        let mut r = fixture();
        let a = r.resolve_qualified("A").unwrap().0;
        let child = r.resolve_qualified("B::b").unwrap().0;
        let membership = r.b.elements[child].owning_relationship.unwrap();
        r.b.set(
            membership,
            "owningType",
            serde_json::json!({"@ref":"Missing"}),
        );
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(
            !raw.membership_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(a)
        );
    }
    #[test]
    fn detached_features_do_not_hide_unknown_owning_type_claims() {
        for value in [
            serde_json::json!({"@ref":"Missing"}),
            serde_json::json!({"@id":uuid::Uuid::new_v4().to_string()}),
            serde_json::json!(false),
        ] {
            let mut r = fixture();
            let a = r.resolve_qualified("A").unwrap().0;
            let child = r.resolve_qualified("B::b").unwrap().0;
            r.b.elements[child].owning_relationship = None;
            r.b.set(child, "owningType", value);
            let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
            assert!(
                !raw.membership_domains(&r.b, &mut 0)
                    .unwrap()
                    .owner_complete(a)
            );
        }
    }
    #[test]
    fn out_of_range_internal_child_backlink_is_unknown() {
        let mut r = fixture();
        let a = r.resolve_qualified("A").unwrap().0;
        let child = r.resolve_qualified("B::b").unwrap().0;
        r.b.elements[child].owning_relationship = Some(usize::MAX);
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(
            !raw.membership_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(a)
        );
    }
    #[test]
    fn duplicate_membership_carriers_recover_all_owners_after_row_changes() {
        let mut r = fixture();
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let unrelated = r.resolve_qualified("Unrelated").unwrap().0;
        let child = r.resolve_qualified("B::b").unwrap().0;
        let membership = r.b.elements[child].owning_relationship.unwrap();
        let clean = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(!clean.multiple_membership_carriers);
        assert!(
            clean
                .membership_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(a)
        );
        r.b.elements[a]
            .owned_relationships
            .make_mut()
            .push(membership);
        assert!(clean.membership_domains(&r.b, &mut 0).is_none());
        let duplicate = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(duplicate.multiple_membership_carriers);
        let domains = duplicate.membership_domains(&r.b, &mut 0).unwrap();
        assert!(!domains.owner_complete(a));
        assert!(!domains.owner_complete(b));
        assert!(domains.owner_complete(unrelated));
        r.b.elements[a]
            .owned_relationships
            .make_mut()
            .retain(|&m| m != membership);
        let repaired = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(!repaired.multiple_membership_carriers);
        let domains = repaired.membership_domains(&r.b, &mut 0).unwrap();
        assert!(domains.owner_complete(a));
        assert!(domains.owner_complete(b));
    }

    #[test]
    fn lazy_domain_budget_retry_cache_and_row_revision_are_shared() {
        let mut r = fixture();
        let a = r.resolve_qualified("A").unwrap().0;
        let child = r.resolve_qualified("B::b").unwrap().0;
        let membership = r.b.elements[child].owning_relationship.unwrap();
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(raw.memberships.get().is_none());
        let mut exhausted = crate::eval::MAX_STEPS - 1;
        assert!(raw.membership_domains(&r.b, &mut exhausted).is_none());
        assert!(raw.memberships.get().is_none());
        let first = raw.membership_domains(&r.b, &mut 0).unwrap();
        let mut warm = 0;
        let second = raw.membership_domains(&r.b, &mut warm).unwrap();
        assert!(Arc::ptr_eq(&first, &second));
        assert_eq!(warm, 1);
        let id = r.b.elements[a].id;
        r.b.set(
            membership,
            "owningType",
            serde_json::json!({"@id":id.to_string()}),
        );
        assert!(raw.membership_domains(&r.b, &mut 0).is_none());
        let fresh = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(
            !fresh
                .membership_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(a)
        );
    }
}

#[cfg(test)]
mod prefix_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model, prepared::PreparedLibrary};

    const LIBRARY: &str = "metaclass M; class A { feature x; doc /* a */ } class B :> A; featuring A::x by B; @M about A;";
    const USER: &str =
        "package U { class C :> B; metaclass N; @N about A; @N about C; import A::*; }";

    /// A model built on a prepared library whose freeze kept the scan of
    /// its rows, with user rows that annotate, specialize and import them.
    fn prepared_fixture() -> (Arc<PreparedLibrary>, ResolvedModel) {
        let mut base = Model::new();
        let parsed = base.add_library_source("lib.kerml", LIBRARY);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let library = base.prepare_library().unwrap();
        assert!(
            library.builder.prefix_structure.is_some(),
            "the freeze keeps the scan"
        );
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        let parsed = model.add_source("user.kerml", USER);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let r = ResolvedModel::build(&model);
        assert!(r.b.library_facts.is_some(), "built on the prepared library");
        (library, r)
    }

    /// The same builder as a table without reusable frozen rows: a frozen
    /// row written with its own clone, which changes nothing but the fact.
    fn force_whole(b: &mut Builder) {
        let row = b.elements[0].clone();
        b.elements[0] = row;
        assert!(!b.elements.base_untouched());
    }

    /// The structure `b` scans whole, with the budget it charges.
    fn scanned_whole(b: &mut Builder) -> (Arc<StoredStructure>, usize) {
        b.stored_structure = None;
        force_whole(b);
        let mut steps = 0;
        let whole = StoredStructure::get(b, &mut steps).unwrap();
        (whole, steps)
    }

    /// Field by field: the structure built through a kept scan equals one
    /// scanned whole.
    fn assert_same(layered: &StoredStructure, whole: &StoredStructure) {
        assert_eq!(layered.logical_work, whole.logical_work);
        assert_eq!(layered.authored_end, whole.authored_end);
        assert_eq!(layered.carriers, whole.carriers);
        assert_eq!(*layered.ids, *whole.ids);
        assert_eq!(layered.type_featurings, whole.type_featurings);
        assert_eq!(layered.bad_chains, whole.bad_chains);
        assert_eq!(layered.bad_bases, whole.bad_bases);
        assert_eq!(layered.source_incomplete, whole.source_incomplete);
        assert_eq!(layered.ids_unique, whole.ids_unique);
        assert_eq!(layered.has_authored_import, whole.has_authored_import);
        assert_eq!(layered.has_recursive_import, whole.has_recursive_import);
        assert_eq!(layered.import_rows, whole.import_rows);
        assert_eq!(
            layered.metadata_annotation_targets,
            whole.metadata_annotation_targets
        );
        assert_eq!(
            layered.metadata_annotation_sources,
            whole.metadata_annotation_sources
        );
        assert_eq!(layered.annotations_incomplete, whole.annotations_incomplete);
        assert_eq!(
            layered.multiple_membership_carriers,
            whole.multiple_membership_carriers
        );
        assert_eq!(layered.membership_rows, whole.membership_rows);
        assert_eq!(layered.typing_rows, whole.typing_rows);
    }

    /// A user row claiming a library relationship row — which no production
    /// writer makes — would make the kept scan read that relationship as the
    /// library's: the build scans whole, and the budget is a whole scan's.
    #[test]
    fn a_row_claiming_a_frozen_relationship_scans_whole() {
        let (_, mut r) = prepared_fixture();
        let base_len = r.b.elements.base_len();
        let annotation = (0..base_len)
            .find(|&i| r.b.elements[i].ty == "Annotation")
            .unwrap();
        let c = r.resolve_qualified("U::C").unwrap().0;
        assert!(c >= base_len);
        r.b.elements[c].owned_relationships.push(annotation);
        assert!(r.b.elements.base_untouched(), "a tail write");
        r.b.stored_structure = None;
        let reuses = prefix_reuses();
        let mut layered_steps = 0;
        let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
        assert_eq!(prefix_reuses(), reuses, "the kept scan did not serve");
        assert_eq!(layered.carriers[annotation], Carrier::Invalid);
        assert!(layered.annotations_incomplete);

        let (_, mut w) = prepared_fixture();
        w.b.elements[c].owned_relationships.push(annotation);
        let (whole, whole_steps) = scanned_whole(&mut w.b);
        assert_eq!(layered_steps, whole_steps);
        assert_same(&layered, &whole);
    }

    /// A user row carrying a library row's id — no production writer makes
    /// one either — would make the kept scan resolve that id to the library
    /// row where a whole scan resolves it to the last row: scanned whole.
    #[test]
    fn a_row_sharing_a_frozen_id_scans_whole() {
        let (_, mut r) = prepared_fixture();
        let base_len = r.b.elements.base_len();
        let b_row = r.resolve_qualified("B").unwrap().0;
        let c = r.resolve_qualified("U::C").unwrap().0;
        assert!(b_row < base_len && c >= base_len);
        r.b.elements[c].id = r.b.elements[b_row].id;
        assert!(r.b.elements.base_untouched());
        r.b.stored_structure = None;
        let reuses = prefix_reuses();
        let mut layered_steps = 0;
        let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
        assert_eq!(prefix_reuses(), reuses, "the kept scan did not serve");
        assert!(!layered.ids_unique);
        assert_eq!(layered.ids.get(&r.b.elements[c].id), Some(&c));

        let (_, mut w) = prepared_fixture();
        w.b.elements[c].id = w.b.elements[b_row].id;
        let (whole, whole_steps) = scanned_whole(&mut w.b);
        assert_eq!(layered_steps, whole_steps);
        assert_same(&layered, &whole);
    }

    /// A frozen relationship whose reference names an id no frozen row
    /// carries — only a corrupt or hand-made library stores one — and a row
    /// of the build carrying that id, which a whole scan would read as the
    /// relationship's source: the build scans whole.
    #[test]
    fn a_row_carrying_an_id_a_frozen_reference_names_scans_whole() {
        let fresh = Uuid::from_u128(0x0123_4567_89ab_cdef_0123_4567_89ab_cdef);
        let build = || {
            let mut base = Model::new();
            let parsed = base.add_library_source("lib.kerml", LIBRARY);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut library = PreparedLibrary::build(&base).unwrap();
            // the `featuring A::x by B` row: its source named by an id no row carries
            let featuring = (0..library.builder.elements.len())
                .find(|&i| library.builder.elements[i].ty == "TypeFeaturing")
                .unwrap();
            library.builder.set(
                featuring,
                "featureOfType",
                serde_json::json!({ "@id": fresh.to_string() }),
            );
            library.builder.elements.freeze();
            library.builder.prefix_structure = StoredStructure::prefix_of(&library.builder);
            let kept = library.builder.prefix_structure.as_ref().unwrap();
            assert!(kept.scanned.source_incomplete, "unsatisfied at the freeze");
            assert!(kept.scanned.unsatisfied.contains(&fresh));
            let library = Arc::new(library);
            let mut model = Model::new();
            library.install(&mut model).unwrap();
            model.add_source("user.kerml", "package U { feature c; }");
            let mut r = ResolvedModel::build(&model);
            let c = r.resolve_qualified("U::c").unwrap().0;
            assert!(c >= r.b.elements.base_len());
            r.b.elements[c].id = fresh;
            assert!(r.b.elements.base_untouched());
            r.b.stored_structure = None;
            (r, c)
        };
        let (mut r, c) = build();
        let reuses = prefix_reuses();
        let mut layered_steps = 0;
        let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
        assert_eq!(prefix_reuses(), reuses, "the kept scan did not serve");
        assert!(!layered.source_incomplete, "the build's row is the source");
        assert_eq!(layered.type_featurings.get(&c).map(Vec::len), Some(1));

        let (mut w, _) = build();
        let (whole, whole_steps) = scanned_whole(&mut w.b);
        assert_eq!(layered_steps, whole_steps);
        assert_same(&layered, &whole);
    }

    /// A library annotation whose target never resolved stores a spelling,
    /// not a reference: incomplete in the kept scan as in a whole one.
    #[test]
    fn a_dangling_library_annotation_target_is_incomplete_either_way() {
        const DANGLING: &str = "metaclass M; class A; @M about Missing;";
        const USER: &str = "package U { class C; }";
        let build = || {
            let mut base = Model::new();
            base.add_library_source("lib.kerml", DANGLING);
            let library = base.prepare_library().unwrap();
            let kept = library.builder.prefix_structure.as_ref().unwrap();
            assert!(kept.scanned.annotations_incomplete);
            let mut model = Model::new();
            Arc::clone(&library).install(&mut model).unwrap();
            model.add_source("user.kerml", USER);
            ResolvedModel::build(&model)
        };
        let mut r = build();
        r.b.stored_structure = None;
        let reuses = prefix_reuses();
        let mut layered_steps = 0;
        let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
        assert_eq!(prefix_reuses(), reuses + 1);
        assert!(layered.annotations_incomplete);
        let mut w = build();
        let (whole, whole_steps) = scanned_whole(&mut w.b);
        assert_eq!(layered_steps, whole_steps);
        assert_same(&layered, &whole);
    }

    /// Implied rows are materialized past the frozen rows; a table whose
    /// implied rows began within them would scan whole, and one whose
    /// implied rows begin exactly at their end keeps the scan.
    #[test]
    fn implied_rows_within_the_frozen_rows_scan_whole() {
        for (implied_from, served) in [(-1isize, 0usize), (0, 1)] {
            let (_, mut r) = prepared_fixture();
            let base_len = r.b.elements.base_len();
            let from = (base_len as isize + implied_from) as usize;
            r.b.implied_from = Some(from);
            r.b.stored_structure = None;
            let reuses = prefix_reuses();
            let mut layered_steps = 0;
            let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
            assert_eq!(prefix_reuses(), reuses + served);
            let (_, mut w) = prepared_fixture();
            w.b.implied_from = Some(from);
            let (whole, whole_steps) = scanned_whole(&mut w.b);
            assert_eq!(layered_steps, whole_steps);
            assert_same(&layered, &whole);
            assert_eq!(layered.authored_end, from);
            assert!(
                !layered.has_authored_import,
                "the user import lies past the authored rows"
            );
        }
    }

    #[test]
    fn frozen_rows_scan_once_and_the_structure_equals_a_whole_scan() {
        let (library, mut r) = prepared_fixture();
        let kept = r.b.prefix_structure.as_ref().unwrap();
        assert!(
            Arc::ptr_eq(kept, library.builder.prefix_structure.as_ref().unwrap()),
            "a build on the library shares the scan its freeze kept"
        );
        let base_len = r.b.elements.base_len();
        assert!(base_len > 0 && r.b.elements.base_untouched());
        let reuses = prefix_reuses();
        r.b.stored_structure = None;
        let mut layered_steps = 0;
        let layered = StoredStructure::get(&mut r.b, &mut layered_steps).unwrap();
        assert_eq!(
            prefix_reuses(),
            reuses + 1,
            "the kept scan served the frozen rows"
        );

        // The same builder with a frozen row written: scanned whole.
        let (_, mut whole) = prepared_fixture();
        whole.b.stored_structure = None;
        let row = whole.b.elements[0].clone();
        whole.b.elements[0] = row;
        assert!(!whole.b.elements.base_untouched());
        let reuses = prefix_reuses();
        let mut whole_steps = 0;
        let scanned = StoredStructure::get(&mut whole.b, &mut whole_steps).unwrap();
        assert_eq!(
            prefix_reuses(),
            reuses,
            "a written frozen row forces a whole scan"
        );

        assert_eq!(
            layered_steps, whole_steps,
            "the budget reads as if scanned whole"
        );
        assert_same(&layered, &scanned);

        // The scan is not trivial: it reaches library and user rows alike.
        let a = r.resolve_qualified("A").unwrap().0;
        let c = r.resolve_qualified("U::C").unwrap().0;
        assert!(a < base_len && c >= base_len);
        assert!(
            layered.metadata_annotation_targets.contains(&a),
            "a library target"
        );
        assert!(
            layered.metadata_annotation_targets.contains(&c),
            "a user target"
        );
        assert_eq!(
            layered.metadata_annotation_sources[&a].len(),
            2,
            "a library and a user source"
        );
        assert!(!layered.type_featurings.is_empty());
        assert!(layered.has_authored_import);
        assert!(layered.ids_unique && !layered.annotations_incomplete);
    }

    /// The scan is not serialized: decoding freezes the rows again, and
    /// that freeze makes the scan the decoded library keeps.
    #[test]
    fn a_decoded_library_keeps_a_scan_of_its_own() {
        let (library, _) = prepared_fixture();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&library.to_bytes(9).unwrap(), 9).unwrap());
        let kept = decoded.builder.prefix_structure.clone();
        assert!(kept.is_some(), "the decoded library's freeze kept a scan");
        assert!(
            !Arc::ptr_eq(
                kept.as_ref().unwrap(),
                library.builder.prefix_structure.as_ref().unwrap()
            ),
            "its own, not the encoded library's"
        );
        let mut model = Model::new();
        decoded.install(&mut model).unwrap();
        model.add_source("user.kerml", USER);
        let reuses = prefix_reuses();
        let mut r = ResolvedModel::build(&model);
        assert!(r.b.library_facts.is_some());
        assert!(prefix_reuses() > reuses, "the build reused the kept scan");
        assert!(Arc::ptr_eq(
            kept.as_ref().unwrap(),
            r.b.prefix_structure.as_ref().unwrap()
        ));
        r.b.stored_structure = None;
        let before = prefix_reuses();
        StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert_eq!(prefix_reuses(), before + 1);
    }
    /// Typed and subsetting features and memberships on both sides of the
    /// frozen rows, and a user feature typed by a library type.
    const TYPED_LIBRARY: &str =
        "class T; class A { feature x : T; feature y :> x; } class S { feature w : A; }";
    const TYPED_USER: &str =
        "package U { class C :> A { feature z : T; feature :>> x; } feature v : S; }";

    fn typed_fixture() -> (Arc<PreparedLibrary>, ResolvedModel) {
        let mut base = Model::new();
        let parsed = base.add_library_source("lib.kerml", TYPED_LIBRARY);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let library = base.prepare_library().unwrap();
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        let parsed = model.add_source("user.kerml", TYPED_USER);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let r = ResolvedModel::build(&model);
        assert!(r.b.library_facts.is_some(), "built on the prepared library");
        (library, r)
    }

    /// The typing projection and membership domains of `layered` (with the
    /// budget each charged) equal those of `whole`, row by row.
    fn assert_same_projections(
        layered: (&StoredStructure, &Builder),
        whole: (&StoredStructure, &Builder),
    ) {
        let (mut layered_steps, mut whole_steps) = (0, 0);
        let lt = layered.0.typing(layered.1, &mut layered_steps).unwrap();
        let wt = whole.0.typing(whole.1, &mut whole_steps).unwrap();
        assert_eq!(layered_steps, whole_steps, "typing budget");
        assert_eq!(lt.sources_incomplete, wt.sources_incomplete);
        let n = whole.1.elements.len();
        for e in 0..n {
            assert_eq!(lt.relationships.get(&e), wt.relationships.get(&e), "{e}");
        }
        let (mut layered_steps, mut whole_steps) = (0, 0);
        let ld = layered.0.membership_domains(layered.1, &mut layered_steps);
        let wd = whole.0.membership_domains(whole.1, &mut whole_steps);
        assert_eq!(layered_steps, whole_steps, "membership budget");
        let (ld, wd) = (ld.unwrap(), wd.unwrap());
        assert_eq!(ld.unlocalized, wd.unlocalized);
        for e in 0..n {
            assert_eq!(ld.owner_complete(e), wd.owner_complete(e), "{e}");
        }
    }

    #[test]
    fn projections_extend_the_frozen_rows_projections_and_equal_whole_ones() {
        let (library, mut r) = typed_fixture();
        r.b.stored_structure = None;
        let layered = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(layered.prefix.is_some(), "the scan extended the kept one");
        let (_, mut w) = typed_fixture();
        let (whole, _) = scanned_whole(&mut w.b);
        assert!(whole.prefix.is_none());
        assert_same_projections((&layered, &r.b), (&whole, &w.b));
        let typing = layered.typing(&r.b, &mut 0).unwrap();
        assert!(typing.relationships.frozen.is_some(), "extended, not whole");
        let domains = layered.membership_domains(&r.b, &mut 0).unwrap();
        assert!(domains.frozen.is_some(), "extended, not whole");
        let x = r.resolve_qualified("A::x").unwrap().0;
        let z = r.resolve_qualified("U::C::z").unwrap().0;
        assert!(x < r.b.lib_boundary && z >= r.b.lib_boundary);
        assert_eq!(typing.relationships[&x].len(), 1);
        assert_eq!(typing.relationships[&z].len(), 1);

        // A second build on the library shares the frozen projections.
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        model.add_source("user.kerml", TYPED_USER);
        let mut second = ResolvedModel::build(&model);
        let other = StoredStructure::for_query(&mut second.b, &mut 0).unwrap();
        let shared = other.typing(&second.b, &mut 0).unwrap();
        assert!(Arc::ptr_eq(
            shared.relationships.frozen.as_ref().unwrap(),
            typing.relationships.frozen.as_ref().unwrap()
        ));
        let shared = other.membership_domains(&second.b, &mut 0).unwrap();
        assert!(Arc::ptr_eq(
            shared.frozen.as_ref().unwrap(),
            domains.frozen.as_ref().unwrap()
        ));
    }

    /// A user typing row naming a library feature as its source — which no
    /// text makes — adds to that feature's entry: the projection is whole.
    #[test]
    fn a_row_typing_a_frozen_feature_projects_whole() {
        let retarget = |r: &mut ResolvedModel| {
            let x = r.resolve_qualified("A::x").unwrap().0;
            let z = r.resolve_qualified("U::C::z").unwrap().0;
            let typing = r.b.elements[z]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| r.b.elements[rel].ty == "FeatureTyping")
                .unwrap();
            let id = r.b.elements[x].id;
            r.b.elements[typing]
                .props
                .insert("typedFeature", crate::properties::Atom::reference(id));
            (x, typing)
        };
        let (_, mut r) = typed_fixture();
        let (x, typing) = retarget(&mut r);
        r.b.stored_structure = None;
        let layered = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(layered.prefix.is_some());
        let (_, mut w) = typed_fixture();
        retarget(&mut w);
        let (whole, _) = scanned_whole(&mut w.b);
        assert_same_projections((&layered, &r.b), (&whole, &w.b));
        let projected = layered.typing(&r.b, &mut 0).unwrap();
        assert!(projected.relationships.frozen.is_none(), "projected whole");
        assert!(projected.relationships[&x].contains(&typing));
    }

    /// A user feature naming a library membership as the membership that
    /// owns it — no text makes one either — reads that membership's claims:
    /// the domains are projected whole.
    #[test]
    fn a_row_owned_through_a_frozen_membership_projects_whole() {
        let reparent = |r: &mut ResolvedModel| {
            let x = r.resolve_qualified("A::x").unwrap().0;
            let z = r.resolve_qualified("U::C::z").unwrap().0;
            let membership = r.b.elements[x].owning_relationship.unwrap();
            let id = r.b.elements[membership].id;
            r.b.elements[z]
                .props
                .insert("owningMembership", crate::properties::Atom::reference(id));
        };
        let (_, mut r) = typed_fixture();
        reparent(&mut r);
        r.b.stored_structure = None;
        let layered = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(layered.prefix.is_some());
        let (_, mut w) = typed_fixture();
        reparent(&mut w);
        let (whole, _) = scanned_whole(&mut w.b);
        assert_same_projections((&layered, &r.b), (&whole, &w.b));
        let domains = layered.membership_domains(&r.b, &mut 0).unwrap();
        assert!(domains.frozen.is_none(), "projected whole");
    }

    /// A user membership row with two carriers makes a whole projection visit
    /// every owner, the frozen ones included: the extended projection charges
    /// what that visit charges.
    #[test]
    fn a_later_membership_with_two_carriers_charges_the_frozen_owners() {
        let share = |r: &mut ResolvedModel| {
            let c = r.resolve_qualified("U::C").unwrap().0;
            let v = r.resolve_qualified("U::v").unwrap().0;
            let membership = r.b.elements[c]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| crate::metaclass::conforms(r.b.elements[rel].ty, "Membership"))
                .unwrap();
            r.b.elements[v].owned_relationships.push(membership);
        };
        let (_, mut r) = typed_fixture();
        share(&mut r);
        r.b.stored_structure = None;
        let layered = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert!(layered.prefix.is_some());
        assert!(layered.multiple_membership_carriers);
        let (_, mut w) = typed_fixture();
        share(&mut w);
        let (whole, _) = scanned_whole(&mut w.b);
        assert_same_projections((&layered, &r.b), (&whole, &w.b));
        let domains = layered.membership_domains(&r.b, &mut 0).unwrap();
        assert!(domains.frozen.is_some(), "extended");
    }
}
