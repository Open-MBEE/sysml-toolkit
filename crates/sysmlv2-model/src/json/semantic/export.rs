//! One checked export frame over the shared published graph. This module does
//! not construct semantic relationships or certify missing property families.
use super::certified_types::Stamp;
use super::{
    CheckedRow, ElementRef, PropertyError, PropertyIssue, ResolvedModel, SemanticExportError,
};
use crate::json::{publication, semantic_ownership, structural_index::StoredStructure};
use serde_json::{Value, json};
use std::collections::{HashMap, HashSet};
use uuid::Uuid;

fn issue(id: Uuid, property: &str, message: &str) -> PropertyIssue {
    PropertyIssue {
        element_id: id,
        property: property.into(),
        reason: PropertyError::InvalidValue(message.into()),
    }
}
fn charge(steps: &mut usize, amount: usize, id: Uuid) -> Result<(), PropertyIssue> {
    *steps = steps.saturating_add(amount);
    if *steps > crate::eval::MAX_STEPS {
        return Err(issue(id, "@snapshot", "strict export work limit"));
    }
    Ok(())
}

struct Snapshot {
    stamp: Stamp,
    elements: Vec<ElementRef>,
    /// All known identities, with a separate local-user/library classification.
    /// A missing entry is an external UUID, not an omitted local row.
    identities: HashMap<Uuid, (usize, bool)>,
    root: Uuid,
    steps: usize,
}

impl Snapshot {
    #[cfg(test)]
    fn prepare(r: &mut ResolvedModel) -> Result<Self, PropertyIssue> {
        Self::prepare_with_budget(r, 0)
    }

    fn prepare_with_budget(r: &mut ResolvedModel, mut steps: usize) -> Result<Self, PropertyIssue> {
        let root = r
            .user_elements()
            .next()
            .map(|e| r.element_id(e))
            .unwrap_or(Uuid::nil());
        if r.b.ensure_semantic_graph() != publication::Status::Ready {
            return Err(issue(
                root,
                "@snapshot",
                "semantic publication is unavailable",
            ));
        }
        r.sync_semantic_publication();
        charge(&mut steps, r.b.elements.len(), root)?;
        let raw = StoredStructure::for_query(&mut r.b, &mut steps)
            .ok_or_else(|| issue(root, "@snapshot", "stored graph evidence is unavailable"))?;
        let ownership =
            r.b.semantic_ownership
                .as_ref()
                .filter(|view| view.matches_suffix(&r.b))
                .ok_or_else(|| issue(root, "@snapshot", "semantic ownership is unavailable"))?;
        let explicit = r.b.explicit_len();
        let library = r.b.lib_boundary;
        let mut identities = HashMap::with_capacity(r.b.elements.len());
        let mut elements = Vec::new();
        for (i, row) in r.b.elements.iter().enumerate() {
            let anchor = ownership.source_anchor(i);
            if anchor >= explicit {
                return Err(issue(
                    row.id,
                    "@snapshot",
                    "generated row has no authored source anchor",
                ));
            }
            let local = anchor >= library;
            if identities.insert(row.id, (i, local)).is_some() {
                return Err(issue(row.id, "@id", "duplicate element identity"));
            }
            if local {
                elements.push(ElementRef(i));
            }
        }
        // The suffix classification comes from central publication. Its current
        // carriers and ordinary child backlinks must still agree with that view.
        for &e in &elements {
            if e.0 < explicit {
                continue;
            }
            let row = &r.b.elements[e.0];
            // Connector is both a Feature and a Relationship, but its node is
            // owned through a Membership. The publisher's role, not metaclass
            // conformance alone, determines which ownership proof applies.
            if ownership.generated_relationship_owner(e.0).is_some() {
                let owner =
                    semantic_ownership::checked_relationship_carrier(&r.b, &raw, e.0, &mut steps)
                        .flatten()
                        .ok_or_else(|| {
                            issue(
                                row.id,
                                "owningRelatedElement",
                                "generated relationship carrier is unproved",
                            )
                        })?;
                if !identities
                    .get(&r.b.elements[owner].id)
                    .is_some_and(|(_, local)| *local)
                {
                    return Err(issue(
                        row.id,
                        "owningRelatedElement",
                        "generated user relationship has a non-user carrier",
                    ));
                }
            } else {
                let owner = row
                    .owning_relationship
                    .and_then(|owner| r.b.elements.get(owner).map(|row| (owner, row)))
                    .ok_or_else(|| {
                        issue(
                            row.id,
                            "owningRelationship",
                            "generated element owner is unproved",
                        )
                    })?;
                charge(&mut steps, owner.1.children.len(), row.id)?;
                if !crate::metaclass::conforms(owner.1.ty, "Relationship")
                    || owner
                        .1
                        .children
                        .iter()
                        .filter(|&&child| child == e.0)
                        .count()
                        != 1
                    || !identities.get(&owner.1.id).is_some_and(|(_, local)| *local)
                    || row
                        .props
                        .get("owningRelationship")
                        .is_some_and(|value| value.as_reference() != Some(owner.1.id))
                {
                    return Err(issue(
                        row.id,
                        "owningRelationship",
                        "generated element ownership is inconsistent",
                    ));
                }
            }
        }
        charge(&mut steps, 0, root)?;
        let stamp = Stamp::capture(r);
        Ok(Self {
            stamp,
            elements,
            identities,
            root,
            steps,
        })
    }

    fn finish(&mut self, r: &ResolvedModel, output: &[Value]) -> Result<(), PropertyIssue> {
        if !self.stamp.current(r) {
            return Err(issue(
                self.root,
                "@snapshot",
                "semantic export snapshot changed during property reads",
            ));
        }
        charge(&mut self.steps, output.len(), self.root)?;
        let mut emitted = HashSet::with_capacity(output.len());
        for row in output {
            let id = row["@id"]
                .as_str()
                .and_then(|id| Uuid::parse_str(id).ok())
                .ok_or_else(|| issue(self.root, "@id", "invalid emitted identity"))?;
            if !emitted.insert(id) {
                return Err(issue(id, "@id", "duplicate emitted element identity"));
            }
        }
        for &e in &self.elements {
            let id = r.element_id(e);
            if !emitted.contains(&id) {
                return Err(issue(
                    id,
                    "@snapshot",
                    "admitted user element is absent from the export",
                ));
            }
        }
        for row in output {
            let id = Uuid::parse_str(row["@id"].as_str().unwrap()).unwrap();
            for (property, value) in row.as_object().unwrap() {
                charge(&mut self.steps, 1, id)?;
                let values = value
                    .as_array()
                    .map(Vec::as_slice)
                    .unwrap_or_else(|| std::slice::from_ref(value));
                charge(&mut self.steps, values.len(), id)?;
                for value in values {
                    if value.get("@ref").is_some() {
                        return Err(issue(id, property, "unresolved spelling in strict export"));
                    }
                    let Some(target) = value.get("@id").and_then(Value::as_str) else {
                        continue;
                    };
                    let target = Uuid::parse_str(target)
                        .map_err(|_| issue(id, property, "invalid reference identity"))?;
                    if self
                        .identities
                        .get(&target)
                        .is_some_and(|(_, local)| *local)
                        && !emitted.contains(&target)
                    {
                        return Err(issue(
                            id,
                            property,
                            "local reference target is absent from the export",
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

pub(super) fn full(r: &mut ResolvedModel) -> Result<Value, SemanticExportError> {
    let mut steps = 0;
    for attempt in 0..2 {
        let mut snapshot =
            Snapshot::prepare_with_budget(r, steps).map_err(|issue| SemanticExportError {
                issues: vec![issue],
            })?;
        let mut output = Vec::with_capacity(snapshot.elements.len());
        let mut issues = Vec::new();
        for &e in &snapshot.elements {
            let ty = r.element_type(e);
            let id = r.element_id(e);
            let mut row = serde_json::Map::new();
            row.insert("@id".into(), json!(id.to_string()));
            row.insert("@type".into(), json!(ty));
            let catalog = crate::schema_props::METACLASS_PROPS;
            let Ok(i) = catalog.binary_search_by_key(&ty, |(name, _)| *name) else {
                issues.push(PropertyIssue {
                    element_id: id,
                    property: "@type".into(),
                    reason: PropertyError::NotDeclared,
                });
                continue;
            };
            if let Err(issue) = charge(&mut snapshot.steps, catalog[i].1.len(), id) {
                issues.push(issue);
                break;
            }
            let mut checked_row = CheckedRow::default();
            for &(name, _) in catalog[i].1 {
                let result = if name == "aliasIds" {
                    Ok(json!([]))
                } else {
                    r.property_with_row(e, name, &mut checked_row)
                };
                match result {
                    Ok(value) => {
                        row.insert(name.into(), value);
                    }
                    Err(reason) => issues.push(PropertyIssue {
                        element_id: id,
                        property: name.into(),
                        reason,
                    }),
                }
            }
            output.push(Value::Object(row));
        }
        // A cold checked provider can complete lazy proof preparation. Never mix
        // values from that transition: discard the entire candidate and recapture
        // once, charging both scans to the same allowance. Continuing changes refuse.
        if !snapshot.stamp.current(r) && attempt == 0 {
            steps = snapshot.steps;
            continue;
        }
        if let Err(issue) = snapshot.finish(r, &output) {
            issues.push(issue);
        }
        if issues.is_empty() {
            return Ok(Value::Array(output));
        } else {
            return Err(SemanticExportError { issues });
        }
    }
    unreachable!("the final export attempt returns or refuses")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ClosurePolicy, model::Model};

    fn model(text: &str) -> ResolvedModel {
        let mut m = Model::new();
        assert!(m.add_source("export.kerml", text).diagnostics.is_empty());
        ResolvedModel::build(&m)
    }
    fn candidate(r: &ResolvedModel, snapshot: &Snapshot) -> Vec<Value> {
        snapshot.elements.iter().map(|&e| {
            let row = &r.b.elements[e.0];
            let relationships = semantic_ownership::owned_relationships(&r.b, e.0).unwrap();
            json!({"@id":row.id,"@type":row.ty,
                "ownedRelationship":relationships.iter().map(|i| json!({"@id":r.b.elements[i].id})).collect::<Vec<_>>(),
                "ownedRelatedElement":row.children.iter().map(|&i| json!({"@id":r.b.elements[i].id})).collect::<Vec<_>>()})
        }).collect()
    }

    #[test]
    fn empty_namespace_export_matches_checked_properties_and_preserves_policy() {
        let mut r = model("");
        let before = r.closure_policy();
        let output = r.to_full_json_strict().unwrap();
        assert_eq!(r.closure_policy(), before);
        assert_eq!(output.as_array().unwrap().len(), 1);
        let e = r.user_elements().next().unwrap();
        for (name, value) in output[0].as_object().unwrap() {
            if matches!(name.as_str(), "@id" | "@type" | "aliasIds") {
                continue;
            }
            assert_eq!(&r.property(e, name).unwrap(), value, "{name}");
        }
        assert_eq!(r.to_full_json_strict().unwrap(), output);
    }

    #[test]
    fn snapshot_includes_the_existing_generated_user_domain_and_no_library_rows() {
        let mut m = Model::new();
        m.add_library_source(
            "library.kerml",
            "standard library package L { feature n=4; feature use=n; }",
        );
        m.add_source("export.kerml", "feature source=4; feature use=source;");
        let mut r = ResolvedModel::build(&m);
        let mut snapshot = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(snapshot.elements.iter().any(|e| e.0 >= r.b.explicit_len()));
        let connector = snapshot
            .elements
            .iter()
            .copied()
            .find(|&e| e.0 >= r.b.explicit_len() && r.element_type(e) == "BindingConnector")
            .expect("the generated result owns a binding connector");
        assert!(r.b.elements[connector.0].owning_relationship.is_some());
        assert_eq!(
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .generated_relationship_owner(connector.0),
            None
        );
        let rows: Vec<_> = r.b.elements.iter().map(|e| (e.ty, e.id)).collect();
        let output = candidate(&r, &snapshot);
        snapshot.finish(&r, &output).unwrap();
        let report = r.to_full_json_strict().unwrap_err();
        let generated_ids: HashSet<_> = snapshot
            .elements
            .iter()
            .filter(|e| e.0 >= r.b.explicit_len())
            .map(|&e| r.element_id(e))
            .collect();
        assert!(
            report
                .issues
                .iter()
                .any(|issue| generated_ids.contains(&issue.element_id))
        );
        assert_eq!(
            rows,
            r.b.elements
                .iter()
                .map(|e| (e.ty, e.id))
                .collect::<Vec<_>>()
        );
        let again = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(snapshot.elements, again.elements);
    }

    #[test]
    fn final_reference_check_distinguishes_missing_local_library_and_external_ids() {
        let mut m = Model::new();
        m.add_library_source("library.kerml", "standard library package L;");
        m.add_source("export.kerml", "package P; package Q;");
        let mut r = ResolvedModel::build(&m);
        let mut snapshot = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        let mut output = candidate(&r, &snapshot);
        let library = r.b.elements[0].id;
        let external = Uuid::from_u128(79);
        output[0]["references"] = json!([{"@id":library},{"@id":external}]);
        snapshot.finish(&r, &output).unwrap();
        let removed = snapshot.elements.pop().unwrap();
        output.retain(|row| row["@id"] != r.element_id(removed).to_string());
        output[0]["references"] = json!([{"@id":r.element_id(removed)}]);
        let error = snapshot.finish(&r, &output).unwrap_err();
        assert!(
            matches!(error.reason, PropertyError::InvalidValue(ref s) if s.contains("local reference target"))
        );
    }

    #[test]
    fn strict_export_refuses_implied_authored_identity_collisions() {
        let mut r = model("feature source=4; feature use=source;");
        let snapshot = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        let generated = snapshot
            .elements
            .iter()
            .find(|e| e.0 >= r.b.explicit_len())
            .unwrap()
            .0;
        r.b.elements[generated].id = r.b.elements[0].id;
        let report = r.to_full_json_strict().unwrap_err();
        assert!(report.issues.iter().any(|issue| issue.property == "@id"));
    }

    #[test]
    fn changed_rows_publication_or_policy_cannot_pass_the_final_snapshot_check() {
        for change in 0..3 {
            let mut r = model("package P;");
            let mut snapshot = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
            let output = candidate(&r, &snapshot);
            match change {
                0 => {
                    r.b.elements[0]
                        .props
                        .insert("declaredName", json!("changed"));
                }
                1 => r.b.publication.published(),
                _ => r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                }),
            }
            assert!(matches!(snapshot.finish(&r, &output).unwrap_err().reason,
                PropertyError::InvalidValue(ref s) if s.contains("snapshot changed")));
        }
    }

    #[test]
    fn publication_refusal_and_bounded_final_scan_are_explicit() {
        let mut r = model("package P;");
        let guard = r.b.publication.begin(true).unwrap();
        assert!(
            r.to_full_json_strict()
                .unwrap_err()
                .issues
                .iter()
                .any(|issue| issue.property == "@snapshot")
        );
        drop(guard);
        let mut snapshot = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        let output = candidate(&r, &snapshot);
        snapshot.steps = crate::eval::MAX_STEPS;
        assert!(matches!(snapshot.finish(&r, &output).unwrap_err().reason,
            PropertyError::InvalidValue(ref s) if s.contains("work limit")));
        let mut retry = Snapshot::prepare(&mut r).unwrap_or_else(|e| panic!("{e:?}"));
        retry.finish(&r, &output).unwrap();
    }

    /// Private, machine-readable census keyed by exact effective declaration,
    /// receiver metaclass and refusal reason. It does not alter the public error.
    fn census(r: &ResolvedModel, report: &SemanticExportError) -> Value {
        let rows: HashMap<_, _> = r.b.elements.iter().map(|row| (row.id, row.ty)).collect();
        let mut groups = std::collections::BTreeMap::<(_, _, _), (usize, Uuid)>::new();
        for issue in &report.issues {
            let ty = rows.get(&issue.element_id).copied().unwrap_or("<snapshot>");
            let declaration = crate::semantic_catalog::property(ty, &issue.property)
                .map(|(requested, effective)| effective.unwrap_or(requested).id)
                .unwrap_or("<export>");
            let count = groups
                .entry((declaration, ty, issue.reason.to_string()))
                .or_insert((0, issue.element_id));
            count.0 += 1;
        }
        Value::Array(groups.into_iter().map(|((declaration,receiver,reason),(count,example))|
            json!({"declaration":declaration,"receiver":receiver,"reason":reason,"count":count,"example":example})).collect())
    }

    #[test]
    fn refusal_census_uses_catalog_identity_without_claiming_generated_family_completeness() {
        let mut r =
            model("function F {in x; return result;} feature source=4; feature use=source;");
        let report = r.to_full_json_strict().unwrap_err();
        let census = census(&r, &report);
        assert_eq!(
            census
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row["count"].as_u64().unwrap() as usize)
                .sum::<usize>(),
            report.issues.len()
        );
        assert!(census.as_array().unwrap().iter().any(|row| {
            row["declaration"]
                .as_str()
                .unwrap()
                .starts_with("Core-Types-Type-")
        }));
        assert!(serde_json::to_string(&census).is_ok());
    }
}
