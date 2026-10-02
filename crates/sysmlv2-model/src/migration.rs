//! Explicit migration of authored compact graphs. Input is never mutated.
use crate::model::GraphFormat;
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};
use uuid::Uuid;

/// A complete migration result. Apply `ids` simultaneously to references held
/// outside this document; a new wrapper can occupy a former operand UUID.
#[derive(Debug)]
pub struct GraphMigration {
    pub source: GraphFormat,
    pub target: GraphFormat,
    pub document: Value,
    /// Every original identity, including unchanged identities.
    pub ids: BTreeMap<Uuid, Uuid>,
    pub added: Vec<Uuid>,
    /// Original row index → migrated row index, including document roots.
    pub element_indices: Vec<usize>,
}

fn id(value: &Value) -> Result<Uuid, String> {
    value
        .get("@id")
        .and_then(Value::as_str)
        .and_then(|s| Uuid::parse_str(s).ok())
        .ok_or_else(|| "expected a UUID reference".to_owned())
}
fn refs(row: &Value, key: &str) -> Result<Vec<Uuid>, String> {
    match row.get(key) {
        None => Ok(Vec::new()),
        Some(Value::Array(a)) => a.iter().map(id).collect(),
        _ => Err(format!("{key} must be a reference array")),
    }
}
fn one(row: &Value, key: &str) -> Result<Uuid, String> {
    let ids = refs(row, key)?;
    if ids.len() != 1 {
        return Err(format!("expected exactly one {key}"));
    }
    Ok(ids[0])
}
fn charge(steps: &mut usize, n: usize) -> Result<(), String> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err("graph migration work limit".into())
    } else {
        Ok(())
    }
}

/// Check the authored ownership forest before deriving or changing identities.
fn index(rows: &[Value], steps: &mut usize) -> Result<HashMap<Uuid, usize>, String> {
    charge(steps, rows.len())?;
    let mut by_id = HashMap::new();
    for (i, row) in rows.iter().enumerate() {
        if by_id.insert(id(row)?, i).is_some() {
            return Err("duplicate element identity".into());
        }
        let ty = row
            .get("@type")
            .and_then(Value::as_str)
            .ok_or("missing metaclass")?;
        if crate::metaclass_name(ty).is_none() {
            return Err("unknown metaclass".into());
        }
        for key in row.as_object().ok_or("element must be an object")?.keys() {
            charge(steps, 1)?;
            if !matches!(
                key.as_str(),
                "@id"
                    | "@type"
                    | "elementId"
                    | "isImpliedIncluded"
                    | "owningRelationship"
                    | "owningRelatedElement"
                    | "ownedRelationship"
                    | "ownedRelatedElement"
            ) && !crate::json::is_owned_property(ty, key)
            {
                return Err(format!(
                    "migration requires compact owned properties: {ty}.{key}"
                ));
            }
        }
        if row.get("isImplied").is_some_and(|v| v != false) {
            return Err("migration requires authored compact rows".into());
        }
        if row
            .get("elementId")
            .is_some_and(|v| v.as_str() != row["@id"].as_str())
        {
            return Err("elementId contradicts @id".into());
        }
    }
    let mut parents = vec![None; rows.len()];
    let mut children = vec![Vec::new(); rows.len()];
    for (i, row) in rows.iter().enumerate() {
        for (forward, inverse) in [
            ("ownedRelationship", "owningRelatedElement"),
            ("ownedRelatedElement", "owningRelationship"),
        ] {
            let edges = refs(row, forward)?;
            if forward == "ownedRelatedElement"
                && !edges.is_empty()
                && !crate::metaclass::conforms(row["@type"].as_str().unwrap(), "Relationship")
            {
                return Err("ownedRelatedElement source is not a Relationship".into());
            }
            charge(steps, edges.len())?;
            for child in edges {
                let &j = by_id.get(&child).ok_or("external ownership target")?;
                if parents[j].replace(i).is_some() {
                    return Err("multiple ownership claims".into());
                }
                if rows[j].get(inverse).map(id).transpose()? != Some(id(row)?) {
                    return Err("nonreciprocal ownership".into());
                }
                let other_inverse = if inverse == "owningRelationship" {
                    "owningRelatedElement"
                } else {
                    "owningRelationship"
                };
                if rows[j].get(other_inverse).is_some_and(|v| !v.is_null()) {
                    return Err("contradictory ownership roles".into());
                }
                if forward == "ownedRelationship"
                    && !crate::metaclass::conforms(
                        rows[j]["@type"].as_str().unwrap(),
                        "Relationship",
                    )
                {
                    return Err("ownedRelationship target is not a Relationship".into());
                }
                children[i].push(j);
            }
        }
    }
    let mut pending = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        for key in ["owningRelationship", "owningRelatedElement"] {
            if row.get(key).is_some_and(|v| !v.is_null()) {
                let owner = id(&row[key])?;
                if parents[i].map(|p| id(&rows[p])).transpose()? != Some(owner) {
                    return Err("unlisted inverse ownership claim".into());
                }
            }
        }
        if parents[i].is_none() {
            if row["@type"] != "Namespace" {
                return Err("unowned non-root element".into());
            }
            pending.push(i);
        }
    }
    let mut seen = HashSet::new();
    while let Some(i) = pending.pop() {
        charge(steps, 1)?;
        if !seen.insert(i) {
            return Err("ownership cycle".into());
        }
        pending.extend(children[i].iter().copied());
    }
    if seen.len() != rows.len() {
        return Err("unreachable ownership cycle".into());
    }
    Ok(by_id)
}

// (FeatureValue, expression) for every grammar-owned conditional operand.
fn operands(
    rows: &[Value],
    by: &HashMap<Uuid, usize>,
    steps: &mut usize,
) -> Result<Vec<(usize, usize)>, String> {
    let mut out = Vec::new();
    for row in rows {
        charge(steps, 1)?;
        if row["@type"] != "OperatorExpression" {
            continue;
        }
        let expected = match row["operator"].as_str() {
            Some("if") => 3,
            Some("and" | "or" | "implies" | "??") => 2,
            _ => continue,
        };
        let owned = refs(row, "ownedRelationship")?;
        charge(steps, owned.len())?;
        let parameters: Vec<_> = owned
            .iter()
            .map(|r| by[r])
            .filter(|&i| rows[i]["@type"] == "ParameterMembership")
            .collect();
        if parameters.len() != expected {
            return Err("conditional operand cardinality".into());
        }
        for membership in parameters.into_iter().skip(1) {
            let parameter = by[&one(&rows[membership], "ownedRelatedElement")?];
            if rows[parameter]["@type"] != "Feature" {
                return Err("conditional operand requires a Feature".into());
            }
            let rels = refs(&rows[parameter], "ownedRelationship")?;
            charge(steps, rels.len())?;
            let values: Vec<_> = rels
                .iter()
                .map(|r| by[r])
                .filter(|&i| rows[i]["@type"] == "FeatureValue")
                .collect();
            if values.len() != 1 {
                return Err("conditional operand requires one value".into());
            }
            let value = values[0];
            let expression = by[&one(&rows[value], "ownedRelatedElement")?];
            if !crate::metaclass::conforms(
                rows[expression]["@type"].as_str().unwrap(),
                "Expression",
            ) {
                return Err("operand value is not an Expression".into());
            }
            out.push((value, expression));
        }
    }
    Ok(out)
}
fn wrapped(rows: &[Value], by: &HashMap<Uuid, usize>, expression: usize) -> Result<bool, String> {
    if rows[expression]["@type"] != "FeatureReferenceExpression" {
        return Ok(false);
    }
    let rels = refs(&rows[expression], "ownedRelationship")?;
    if rels.len() != 1 {
        return Ok(false);
    }
    let member = &rows[by[&rels[0]]];
    if member["@type"] != "FeatureMembership" {
        return Ok(false);
    }
    let children = refs(member, "ownedRelatedElement")?;
    Ok(children.len() == 1
        && crate::metaclass::conforms(
            rows[by[&children[0]]]["@type"].as_str().unwrap(),
            "Expression",
        ))
}

/// The authored constructor fragment admitted by the canonical contract.
/// Generated semantic relationships do not participate in authored shape checks.
struct ConstructorShape {
    owner: usize,
    selector: usize,
    selector_end: usize,
    parameters: Vec<usize>,
}

// Constructor syntax has no spelling for flags on its structural wrapper
// Features and relationships. Admit absent/default values (including full
// export's materialized defaults), but never silently discard nondefaults.
fn constructor_syntax_scalars(row: &Value, direction: Option<&str>) -> Result<(), String> {
    let ty = row["@type"]
        .as_str()
        .ok_or("missing constructor metaclass")?;
    for (key, value) in row.as_object().ok_or("constructor row must be an object")? {
        if matches!(key.as_str(), "elementId" | "isImpliedIncluded") {
            continue; // identity and export closure metadata, not syntax flags
        }
        // Direct selector names retain the existing interchange behavior:
        // compatibility full export materializes them from the target's
        // effective name, which can depend on an external library. The new
        // result/argument wrapper guard does not certify those legacy names.
        if ty == "Membership" && matches!(key.as_str(), "memberName" | "memberShortName") {
            continue;
        }
        let Some((_, Some(spec))) = crate::semantic_catalog::property(ty, key) else {
            continue;
        };
        if spec.derived
            || !(matches!(spec.target, "Boolean" | "String" | "Integer" | "Real")
                || !spec.enum_values.is_empty())
        {
            continue;
        }
        let expected = if key == "direction" {
            direction.map_or(Value::Null, |value| json!(value))
        } else if let Some(default) = spec.default_json {
            serde_json::from_str(default).map_err(|_| "invalid scalar schema default")?
        } else if spec.upper != Some(1) {
            json!([])
        } else {
            Value::Null
        };
        if *value != expected {
            return Err(format!("constructor syntax cannot preserve {ty}.{key}"));
        }
    }
    Ok(())
}

fn constructor_shapes(
    rows: &[Value],
    format: GraphFormat,
    strict_legacy: bool,
    steps: &mut usize,
) -> Result<Vec<ConstructorShape>, String> {
    let mut by = HashMap::new();
    let mut inverse: HashMap<(&str, &str), Vec<usize>> = HashMap::new();
    for (i, row) in rows.iter().enumerate() {
        charge(steps, 1 + row.as_object().map_or(0, |object| object.len()))?;
        if let Some(id) = row["@id"].as_str() {
            by.entry(id).and_modify(|v| *v = None).or_insert(Some(i));
        }
        if row["isImplied"] != true {
            for key in ["owningRelatedElement", "owningRelationship"] {
                if let Some(owner) = row[key]["@id"].as_str() {
                    inverse.entry((key, owner)).or_default().push(i);
                }
            }
        }
    }
    let lookup = |reference: &Value| -> Result<usize, String> {
        reference["@id"]
            .as_str()
            .and_then(|id| by.get(id).copied().flatten())
            .ok_or_else(|| "missing or ambiguous constructor ownership target".into())
    };
    let children = |owner: usize, key: &str| -> Result<Vec<usize>, String> {
        let inverse_key = if key == "ownedRelationship" {
            "owningRelatedElement"
        } else {
            "owningRelationship"
        };
        let other_inverse = if key == "ownedRelationship" {
            "owningRelationship"
        } else {
            "owningRelatedElement"
        };
        let mut children = Vec::new();
        let mut seen = HashSet::new();
        if let Some(values) = rows[owner].get(key) {
            for reference in values
                .as_array()
                .ok_or("constructor ownership must be an array")?
            {
                let child = lookup(reference)?;
                if rows[child]["isImplied"] == true {
                    continue;
                }
                if !seen.insert(child)
                    || rows[child][inverse_key]["@id"] != rows[owner]["@id"]
                    || rows[child].get(other_inverse).is_some_and(|v| !v.is_null())
                {
                    return Err("nonreciprocal or duplicate constructor ownership".into());
                }
                children.push(child);
            }
        }
        if let Some(claims) = rows[owner]["@id"]
            .as_str()
            .and_then(|id| inverse.get(&(inverse_key, id)))
        {
            if claims.len() != children.len() || claims.iter().any(|i| !seen.contains(i)) {
                return Err("unlisted inverse constructor ownership claim".into());
            }
        }
        Ok(children)
    };
    let member = |membership: usize| -> Result<usize, String> {
        let owned = children(membership, "ownedRelatedElement")?;
        if owned.len() != 1 {
            return Err("constructor membership must own exactly one element".into());
        }
        constructor_syntax_scalars(&rows[membership], None)?;
        let ty = rows[membership]["@type"]
            .as_str()
            .ok_or("missing membership metaclass")?;
        for key in [
            "memberElement",
            "ownedMemberElement",
            "ownedMemberFeature",
            "ownedMemberParameter",
            "value",
            "target",
        ] {
            if crate::semantic_catalog::property(ty, key).is_none() {
                continue;
            }
            if let Some(alias) = rows[membership].get(key).filter(|v| !v.is_null()) {
                let target = if key == "target" {
                    let aliases = alias
                        .as_array()
                        .ok_or("constructor target alias must be an array")?;
                    if aliases.len() != 1 {
                        return Err("constructor target alias cardinality".into());
                    }
                    &aliases[0]
                } else {
                    alias
                };
                if lookup(target)? != owned[0] {
                    return Err("constructor membership alias contradicts ownership".into());
                }
            }
        }
        for key in [
            "membershipOwningNamespace",
            "owningType",
            "featureWithValue",
            "source",
        ] {
            if crate::semantic_catalog::property(ty, key).is_none() {
                continue;
            }
            if let Some(alias) = rows[membership].get(key).filter(|v| !v.is_null()) {
                let source = if key == "source" {
                    let aliases = alias
                        .as_array()
                        .ok_or("constructor source alias must be an array")?;
                    if aliases.len() != 1 {
                        return Err("constructor source alias cardinality".into());
                    }
                    &aliases[0]
                } else {
                    alias
                };
                if lookup(source)? != lookup(&rows[membership]["owningRelatedElement"])? {
                    return Err("constructor membership owner alias contradicts ownership".into());
                }
            }
        }
        let owner = lookup(&rows[membership]["owningRelatedElement"])?;
        let child = owned[0];
        let child_type = rows[child]["@type"]
            .as_str()
            .ok_or("missing member metaclass")?;
        for key in [
            "owningMembership",
            "owningFeatureMembership",
            "owningParameterMembership",
            "owner",
            "owningNamespace",
            "owningType",
        ] {
            if crate::semantic_catalog::property(child_type, key).is_none() {
                continue;
            }
            if let Some(alias) = rows[child].get(key).filter(|v| !v.is_null()) {
                let requires_feature_membership =
                    matches!(key, "owningFeatureMembership" | "owningType");
                let requires_parameter_membership = key == "owningParameterMembership";
                if (requires_feature_membership
                    && !crate::metaclass::conforms(ty, "FeatureMembership"))
                    || (requires_parameter_membership
                        && !crate::metaclass::conforms(ty, "ParameterMembership"))
                {
                    return Err(
                        "constructor member owner alias has an invalid relationship kind".into(),
                    );
                }
                let expected = if matches!(
                    key,
                    "owningMembership" | "owningFeatureMembership" | "owningParameterMembership"
                ) {
                    membership
                } else {
                    owner
                };
                if lookup(alias)? != expected {
                    return Err("constructor member owner alias contradicts ownership".into());
                }
            }
        }
        if let Some(alias) = rows[membership]
            .get("relatedElement")
            .filter(|v| !v.is_null())
        {
            let references = alias
                .as_array()
                .ok_or("constructor relatedElement alias must be an array")?;
            if references.len() != 2
                || lookup(&references[0])? != owner
                || lookup(&references[1])? != child
            {
                return Err("constructor relatedElement alias contradicts ownership".into());
            }
        }
        for key in ["memberElementId", "ownedMemberElementId"] {
            if crate::semantic_catalog::property(ty, key).is_some() {
                if let Some(alias) = rows[membership].get(key).filter(|v| !v.is_null()) {
                    if alias != &rows[owned[0]]["@id"] {
                        return Err(
                            "constructor member identity alias contradicts ownership".into()
                        );
                    }
                }
            }
        }
        Ok(owned[0])
    };
    let owned_feature_aliases = |owner: usize, memberships: &[usize]| -> Result<(), String> {
        let ty = rows[owner]["@type"]
            .as_str()
            .ok_or("missing constructor owner metaclass")?;
        for key in ["ownedFeatureMembership", "ownedFeature"] {
            if crate::semantic_catalog::property(ty, key).is_none() {
                continue;
            }
            let Some(alias) = rows[owner].get(key) else {
                continue;
            };
            let values = alias
                .as_array()
                .ok_or("constructor owned-feature alias must be an array")?;
            if values.len() != memberships.len() {
                return Err("constructor owned-feature alias cardinality".into());
            }
            for (reference, &membership) in values.iter().zip(memberships) {
                let expected = if key == "ownedFeature" {
                    member(membership)?
                } else {
                    membership
                };
                if lookup(reference)? != expected {
                    return Err("constructor owned-feature alias contradicts ownership".into());
                }
            }
        }
        Ok(())
    };
    let mut shapes = Vec::new();
    for (owner, row) in rows.iter().enumerate() {
        charge(steps, 1)?;
        if row["@type"] != "ConstructorExpression" || row["isImplied"] == true {
            continue;
        }
        // Keep the historical recovery boundary for legacy imports; recognize
        // and refuse the canonical result rather than flattening it silently.
        if format == GraphFormat::LegacyV2 && !strict_legacy {
            let forward = row["ownedRelationship"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|r| lookup(r).ok());
            let inverse_claims = row["@id"]
                .as_str()
                .and_then(|id| inverse.get(&("owningRelatedElement", id)))
                .into_iter()
                .flatten()
                .copied();
            if forward.chain(inverse_claims).any(|i| {
                rows[i]["@type"] == "ReturnParameterMembership" && rows[i]["isImplied"] != true
            }) {
                return Err("canonical constructor result requires CanonicalV3; migrate explicitly before changing formats".into());
            }
            continue;
        }
        let relationships = children(owner, "ownedRelationship")?;
        charge(steps, relationships.len())?;
        let Some(&selector) = relationships.first() else {
            return Err("constructor requires a type selector".into());
        };
        // A dotted instantiated type owns its synthesized feature chain through
        // an OwningMembership. This is still the selector, not a result Feature.
        let mut selector_end = selector;
        match rows[selector]["@type"].as_str() {
            Some("Membership") if children(selector, "ownedRelatedElement")?.is_empty() => {
                constructor_syntax_scalars(&rows[selector], None)?;
            }
            Some("OwningMembership") => {
                let chain = member(selector)?;
                if rows[chain]["@type"] != "Feature" {
                    return Err("constructor chain selector must own a Feature".into());
                }
                constructor_syntax_scalars(&rows[chain], None)?;
                selector_end = selector_end.max(chain);
                let links = children(chain, "ownedRelationship")?;
                charge(steps, links.len())?;
                if links.len() < 2 {
                    return Err("constructor chain selector requires at least two links".into());
                }
                for link in links {
                    if rows[link]["@type"] != "FeatureChaining"
                        || !children(link, "ownedRelatedElement")?.is_empty()
                        || !children(link, "ownedRelationship")?.is_empty()
                    {
                        return Err("unsupported constructor chain selector relationship".into());
                    }
                    constructor_syntax_scalars(&rows[link], None)?;
                    let target = &rows[link]["chainingFeature"];
                    if target["@id"].as_str().is_none() && target["@ref"].as_str().is_none() {
                        return Err("constructor chain link requires a target".into());
                    }
                    selector_end = selector_end.max(link);
                }
            }
            _ => {
                return Err(
                    "constructor requires a type Membership or owned feature-chain selector".into(),
                );
            }
        }
        let target = &rows[selector]["memberElement"];
        if target["@ref"].as_str().is_none() && target["@id"].as_str().is_none() {
            return Err("constructor selector requires a target".into());
        }
        // This is an authored transport contract. The selected element may
        // fail the semantic Type requirement while still being valid syntax;
        // preserve it so checked semantic consumers can diagnose that failure.
        if target["@id"]
            .as_str()
            .and_then(|id| by.get(id))
            .is_some_and(Option::is_none)
        {
            return Err("ambiguous constructor selector target".into());
        }
        let parameters = if format == GraphFormat::CanonicalV3 {
            if relationships.len() != 2
                || rows[relationships[1]]["@type"] != "ReturnParameterMembership"
            {
                return Err(
                    "canonical constructor must own exactly one result after its selector".into(),
                );
            }
            let result = member(relationships[1])?;
            if rows[result]["@type"] != "Feature" || rows[result]["direction"] != "out" {
                return Err("constructor result must be an out Feature".into());
            }
            constructor_syntax_scalars(&rows[result], Some("out"))?;
            if let Some(alias) = row.get("result").filter(|v| !v.is_null()) {
                if lookup(alias)? != result {
                    return Err("constructor result alias contradicts ownership".into());
                }
            }
            let parameters = children(result, "ownedRelationship")?;
            owned_feature_aliases(owner, &[relationships[1]])?;
            owned_feature_aliases(result, &parameters)?;
            parameters
        } else {
            relationships[1..].to_vec()
        };
        charge(steps, parameters.len())?;
        for &parameter in &parameters {
            if rows[parameter]["@type"] != "ParameterMembership" {
                return Err("constructor arguments require ParameterMembership".into());
            }
            let feature = member(parameter)?;
            if rows[feature]["@type"] != "Feature" || rows[feature]["direction"] != "in" {
                return Err("constructor argument must be an in Feature".into());
            }
            constructor_syntax_scalars(&rows[feature], Some("in"))?;
            let relationships = children(feature, "ownedRelationship")?;
            charge(steps, relationships.len())?;
            let mut value = None;
            let mut redefinition = false;
            for relationship in relationships {
                constructor_syntax_scalars(&rows[relationship], None)?;
                match rows[relationship]["@type"].as_str() {
                    Some("FeatureValue") if value.is_none() => value = Some(relationship),
                    Some("Redefinition") if !redefinition => {
                        redefinition = true;
                        for key in [
                            "redefiningFeature",
                            "subsettingFeature",
                            "specific",
                            "owningFeature",
                            "owningType",
                        ] {
                            if let Some(alias) =
                                rows[relationship].get(key).filter(|v| !v.is_null())
                            {
                                if lookup(alias)? != feature {
                                    return Err(
                                        "constructor redefinition source contradicts ownership"
                                            .into(),
                                    );
                                }
                            }
                        }
                        let target = &rows[relationship]["redefinedFeature"];
                        if target["@id"].as_str().is_none() && target["@ref"].as_str().is_none() {
                            return Err("constructor redefinition requires a target".into());
                        }
                        let same_target = |reference: &Value| {
                            reference.get("@id") == target.get("@id")
                                && reference.get("@ref") == target.get("@ref")
                        };
                        for key in ["general", "subsettedFeature", "target"] {
                            if crate::semantic_catalog::property("Redefinition", key).is_none() {
                                continue;
                            }
                            if let Some(alias) =
                                rows[relationship].get(key).filter(|v| !v.is_null())
                            {
                                let reference = if key == "target" {
                                    let references = alias.as_array().ok_or(
                                        "constructor redefinition target must be an array",
                                    )?;
                                    if references.len() != 1 {
                                        return Err(
                                            "constructor redefinition target cardinality".into()
                                        );
                                    }
                                    &references[0]
                                } else {
                                    alias
                                };
                                if !same_target(reference) {
                                    return Err("constructor redefinition target alias contradicts redefinedFeature".into());
                                }
                            }
                        }
                        if let Some(source) =
                            rows[relationship].get("source").filter(|v| !v.is_null())
                        {
                            let references = source
                                .as_array()
                                .ok_or("constructor redefinition source must be an array")?;
                            if references.len() != 1 || lookup(&references[0])? != feature {
                                return Err(
                                    "constructor redefinition source contradicts ownership".into(),
                                );
                            }
                        }
                        if let Some(related) = rows[relationship]
                            .get("relatedElement")
                            .filter(|v| !v.is_null())
                        {
                            let references = related.as_array().ok_or(
                                "constructor redefinition relatedElement must be an array",
                            )?;
                            if references.len() != 2
                                || lookup(&references[0])? != feature
                                || !same_target(&references[1])
                            {
                                return Err(
                                    "constructor redefinition relatedElement contradicts endpoints"
                                        .into(),
                                );
                            }
                        }
                    }
                    _ => {
                        return Err(
                            "unsupported or duplicate constructor argument relationship".into()
                        );
                    }
                }
            }
            let value = value.ok_or("constructor argument requires one value")?;
            let expression = member(value)?;
            if !rows[expression]["@type"]
                .as_str()
                .is_some_and(|ty| crate::metaclass::conforms(ty, "Expression"))
            {
                return Err("constructor value must own exactly one Expression".into());
            }
            if let Some(alias) = rows[value].get("value").filter(|v| !v.is_null()) {
                if lookup(alias)? != expression {
                    return Err("constructor value alias contradicts ownership".into());
                }
            }
        }
        shapes.push(ConstructorShape {
            owner,
            selector,
            selector_end,
            parameters,
        });
    }
    Ok(shapes)
}

/// Validate authored compact shapes for an explicit graph contract.
/// This checks ownership and conditional/constructor fragments, not whole-model conformance.
pub fn validate_graph_format(document: &Value, format: GraphFormat) -> Result<(), String> {
    let rows = document
        .as_array()
        .ok_or("expected a compact element array")?;
    let mut steps = 0;
    let by = index(rows, &mut steps)?;
    for (_, expression) in operands(rows, &by, &mut steps)? {
        if wrapped(rows, &by, expression)? != (format == GraphFormat::CanonicalV3) {
            return Err("conditional operand shape differs from graph format".into());
        }
    }
    validate_conditional_graph_format(document, format)?;
    Ok(())
}

/// Check authored conditional and constructor fragments in compact or full interchange.
/// Generated relationships are ignored. Unrelated graph fragments retain the
/// loader's existing recovery behavior; ambiguous ownership in these fragments fails.
/// Historical direct selector name recovery is not a lossless-import guarantee.
pub fn validate_conditional_graph_format(
    document: &Value,
    format: GraphFormat,
) -> Result<(), String> {
    let rows = document.as_array().ok_or("expected an element array")?;
    let mut steps = 0;
    constructor_shapes(rows, format, false, &mut steps)?;
    let mut by = HashMap::new();
    for (i, row) in rows.iter().enumerate() {
        charge(&mut steps, 1)?;
        if let Some(id) = row["@id"].as_str() {
            by.entry(id).and_modify(|v| *v = None).or_insert(Some(i));
        }
    }
    let lookup = |reference: &Value| -> Result<usize, String> {
        reference
            .get("@id")
            .and_then(Value::as_str)
            .and_then(|id| by.get(id).copied().flatten())
            .ok_or_else(|| "missing or ambiguous conditional ownership target".into())
    };
    if format == GraphFormat::LegacyV2 {
        // Legacy loaders have always accepted foreign direct-expression
        // parameters and recovered other malformed syntax. Only refuse the
        // recognizable new wrapper: rebuilding it as legacy loses identities.
        let mut pending = Vec::new();
        for row in rows {
            if row["@type"] != "OperatorExpression"
                || !matches!(
                    row["operator"].as_str(),
                    Some("if" | "and" | "or" | "implies" | "??")
                )
            {
                continue;
            }
            let Some(relationships) = row["ownedRelationship"].as_array() else {
                continue;
            };
            charge(&mut steps, relationships.len())?;
            pending.extend(
                relationships
                    .iter()
                    .filter_map(|r| lookup(r).ok())
                    .filter(|&i| {
                        rows[i]["@type"] == "ParameterMembership" && rows[i]["isImplied"] != true
                    })
                    .skip(1)
                    .map(|i| (i, 0)),
            );
        }
        let mut seen = HashSet::new();
        while let Some((i, phase)) = pending.pop() {
            if !seen.insert((i, phase)) {
                continue;
            }
            charge(&mut steps, 1)?;
            let key = match phase {
                0 | 2 | 4 => "ownedRelatedElement",
                _ => "ownedRelationship",
            };
            let Some(references) = rows[i][key].as_array() else {
                continue;
            };
            charge(&mut steps, references.len())?;
            for child in references.iter().filter_map(|r| lookup(r).ok()) {
                if rows[child]["isImplied"] == true {
                    continue;
                }
                match phase {
                    0 if rows[child]["@type"] == "Feature" => pending.push((child, 1)),
                    0 | 2 if rows[child]["@type"] == "FeatureReferenceExpression" => {
                        pending.push((child, 3))
                    }
                    1 if rows[child]["@type"] == "FeatureValue" => pending.push((child, 2)),
                    3 if rows[child]["@type"] == "FeatureMembership" => pending.push((child, 4)),
                    4 if rows[child]["@type"]
                        .as_str()
                        .is_some_and(|ty| crate::metaclass::conforms(ty, "Expression")) =>
                    {
                        return Err("canonical conditional wrapper requires CanonicalV3; migrate explicitly before changing formats".into());
                    }
                    _ => {}
                }
            }
        }
        return Ok(());
    }
    let children = |owner: usize, key: &str| -> Result<Vec<usize>, String> {
        let inverse = if key == "ownedRelationship" {
            "owningRelatedElement"
        } else {
            "owningRelationship"
        };
        let Some(values) = rows[owner].get(key) else {
            return Ok(Vec::new());
        };
        let values = values
            .as_array()
            .ok_or("conditional ownership must be an array")?;
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        for value in values {
            let i = lookup(value)?;
            if rows[i]["isImplied"] == true {
                continue;
            }
            if !seen.insert(i) || rows[i][inverse]["@id"] != rows[owner]["@id"] {
                return Err("nonreciprocal or duplicate conditional ownership".into());
            }
            let other_inverse = if inverse == "owningRelationship" {
                "owningRelatedElement"
            } else {
                "owningRelationship"
            };
            if rows[i].get(other_inverse).is_some_and(|v| !v.is_null()) {
                return Err("contradictory conditional ownership roles".into());
            }
            result.push(i);
        }
        Ok(result)
    };
    let one_child = |owner| -> Result<usize, String> {
        let children = children(owner, "ownedRelatedElement")?;
        if children.len() != 1 {
            return Err("conditional membership must own exactly one element".into());
        }
        Ok(children[0])
    };
    for (operator, row) in rows.iter().enumerate() {
        charge(&mut steps, 1)?;
        if row["@type"] != "OperatorExpression" || row["isImplied"] == true {
            continue;
        }
        let expected = match row["operator"].as_str() {
            Some("if") => 3,
            Some("and" | "or" | "implies" | "??") => 2,
            _ => continue,
        };
        let relationships = children(operator, "ownedRelationship")?;
        charge(&mut steps, relationships.len())?;
        let parameters: Vec<_> = relationships
            .into_iter()
            .filter(|&i| rows[i]["@type"] == "ParameterMembership")
            .collect();
        if parameters.len() != expected {
            return Err("conditional operand cardinality".into());
        }
        for parameter in parameters.into_iter().skip(1) {
            let feature = one_child(parameter)?;
            if rows[feature]["@type"] != "Feature" {
                return Err("conditional operand requires a Feature".into());
            }
            if rows[feature]
                .get("direction")
                .is_some_and(|direction| direction != "in")
            {
                return Err("conditional operand direction must be in".into());
            }
            let relationships = children(feature, "ownedRelationship")?;
            charge(&mut steps, relationships.len())?;
            let values: Vec<_> = relationships
                .into_iter()
                .filter(|&i| rows[i]["@type"] == "FeatureValue")
                .collect();
            if values.len() != 1 {
                return Err("conditional operand requires one value".into());
            }
            let expression = one_child(values[0])?;
            if !rows[expression]["@type"]
                .as_str()
                .is_some_and(|ty| crate::metaclass::conforms(ty, "Expression"))
            {
                return Err("conditional value must own an Expression".into());
            }
            let mut wrapper = false;
            if rows[expression]["@type"] == "FeatureReferenceExpression" {
                let relationships = children(expression, "ownedRelationship")?;
                charge(&mut steps, relationships.len())?;
                let members: Vec<_> = relationships
                    .iter()
                    .copied()
                    .filter(|&i| rows[i]["@type"] == "FeatureMembership")
                    .collect();
                if !members.is_empty() {
                    if members.len() != 1 || relationships.len() != 1 {
                        return Err("ambiguous conditional expression wrapper".into());
                    }
                    let member = members[0];
                    let inner = one_child(member)?;
                    if !rows[inner]["@type"]
                        .as_str()
                        .is_some_and(|ty| crate::metaclass::conforms(ty, "Expression"))
                    {
                        return Err("conditional wrapper must own an Expression".into());
                    }
                    if let Some(alias) = rows[member].get("memberElement") {
                        if !alias.is_null() && lookup(alias)? != inner {
                            return Err("conditional memberElement contradicts ownership".into());
                        }
                    }
                    wrapper = true;
                }
            }
            if wrapper != (format == GraphFormat::CanonicalV3) {
                return Err("conditional operand shape differs from graph format; migrate explicitly before changing formats".into());
            }
        }
    }
    Ok(())
}

/// Migrate a complete user-model authored compact ownership forest from LegacyV2 to
/// CanonicalV3, inserting conditional wrappers and relocating constructor arguments
/// under their new result. References between all supplied documents are updated atomically.
/// External inbound references must be updated by the caller using the returned
/// simultaneous identity map. Decode old ID-elided payloads before migration.
/// Every non-root input identity must match legacy graph derivation. Foreign
/// explicit identities remain loadable but require deliberate source rebuilding
/// before migration. `external_name` must name referenced library targets as in
/// ids::derive_ids; unresolved derivation is refused.
/// Regenerate library graphs from source; their normative IDs use a different rule.
pub fn migrate_conditional_graph(
    document: &Value,
    external_name: &dyn Fn(&str) -> Option<String>,
) -> Result<GraphMigration, String> {
    let original = document
        .as_array()
        .ok_or("expected a compact element array")?;
    let mut steps = 0;
    let by = index(original, &mut steps)?;
    let mut external_ids = HashSet::new();
    collect_external_references(document, &by, &mut external_ids, 0, &mut steps)?;
    let derived = crate::ids::derive_ids(document, external_name).map_err(|e| e.to_string())?;
    for (row, derived) in original.iter().zip(derived) {
        let root = row["@type"] == "Namespace"
            && row["owningRelationship"].is_null()
            && row["owningRelatedElement"].is_null();
        if !root && derived != Some(id(row)?) {
            return Err("migration requires legacy graph-derived identities; rebuild foreign-ID or library graphs from source".into());
        }
    }
    let constructors = constructor_shapes(original, GraphFormat::LegacyV2, true, &mut steps)?;
    let targets = operands(original, &by, &mut steps)?;
    let mut insertions = HashMap::new();
    let mut rows = original.clone();
    // Temporary placeholders participate in both identity derivation and the
    // simultaneous rewrite map. They must not capture an external reference,
    // even when their eventual graph-derived identity would be distinct.
    let mut used: HashSet<_> = by.keys().chain(external_ids.iter()).copied().collect();
    for (value, expression) in targets {
        if wrapped(original, &by, expression)? {
            return Err("document already contains canonical conditional operands".into());
        }
        let old = id(&original[expression])?;
        let wrapper = Uuid::new_v5(&old, b"canonical-conditional-wrapper");
        let membership = Uuid::new_v5(&old, b"canonical-conditional-membership");
        if !used.insert(wrapper) || !used.insert(membership) {
            return Err("temporary migration identity collision".into());
        }
        rows[value]["ownedRelatedElement"] = json!([{"@id":wrapper}]);
        rows[expression]["owningRelationship"] = json!({"@id":membership});
        let additions = vec![
            json!({"@id":wrapper,"@type":"FeatureReferenceExpression","elementId":wrapper,"isImpliedIncluded":false,"ownedRelationship":[{"@id":membership}],"owningRelationship":{"@id":id(&original[value])?}}),
            json!({"@id":membership,"@type":"FeatureMembership","elementId":membership,"isImplied":false,"isImpliedIncluded":false,"ownedRelationship":[],"ownedRelatedElement":[{"@id":old}],"owningRelationship":null,"owningRelatedElement":{"@id":wrapper}}),
        ];
        if insertions.insert(expression, additions).is_some() {
            return Err("operand has multiple values".into());
        }
    }
    for constructor in constructors {
        let owner = id(&original[constructor.owner])?;
        let result = Uuid::new_v5(&owner, b"canonical-constructor-result");
        let membership = Uuid::new_v5(&owner, b"canonical-constructor-result-membership");
        if !used.insert(result) || !used.insert(membership) {
            return Err("temporary migration identity collision".into());
        }
        let selector = id(&original[constructor.selector])?;
        let parameters = constructor
            .parameters
            .iter()
            .map(|&i| id(&original[i]))
            .collect::<Result<Vec<_>, _>>()?;
        rows[constructor.owner]["ownedRelationship"] = json!([{"@id":selector},{"@id":membership}]);
        for &parameter in &constructor.parameters {
            rows[parameter]["owningRelatedElement"] = json!({"@id":result});
        }
        let additions = vec![
            json!({"@id":membership,"@type":"ReturnParameterMembership","elementId":membership,"isImplied":false,"isImpliedIncluded":false,"ownedRelationship":[],"ownedRelatedElement":[{"@id":result}],"owningRelationship":null,"owningRelatedElement":{"@id":owner}}),
            json!({"@id":result,"@type":"Feature","elementId":result,"isImpliedIncluded":false,"ownedRelationship":parameters.into_iter().map(|id| json!({"@id":id})).collect::<Vec<_>>(),"owningRelationship":{"@id":membership},"direction":"out"}),
        ];
        // Source lowering emits the pair after the entire selector subtree, even
        // for an empty constructor. Preserve all existing row order.
        insertions
            .entry(constructor.selector_end + 1)
            .or_default()
            .splice(0..0, additions);
    }
    let mut expanded = Vec::with_capacity(rows.len() + insertions.len() * 2);
    let mut element_indices = Vec::with_capacity(rows.len());
    let mut added_indices = Vec::new();
    for (i, row) in rows.into_iter().enumerate() {
        if let Some(additions) = insertions.remove(&i) {
            for addition in additions {
                added_indices.push(expanded.len());
                expanded.push(addition);
            }
        }
        element_indices.push(expanded.len());
        expanded.push(row);
    }
    if let Some(additions) = insertions.remove(&element_indices.len()) {
        for addition in additions {
            added_indices.push(expanded.len());
            expanded.push(addition);
        }
    }
    let mut document = Value::Array(expanded);
    let rows = document.as_array().unwrap();
    let roots = rows
        .iter()
        .enumerate()
        .filter(|(_, row)| {
            row["@type"] == "Namespace"
                && row["owningRelationship"].is_null()
                && row["owningRelatedElement"].is_null()
        })
        .map(|(i, row)| Ok((i, id(row)?)))
        .collect::<Result<HashMap<_, _>, String>>()?;
    // Assign top-down from final parent IDs. derive_ids intentionally compares
    // each row against its current parent and must not be used for a migration.
    let derived =
        crate::ids::assign_ids(&document, &roots, external_name).map_err(|e| e.to_string())?;
    let mut replacement = HashMap::new();
    let mut final_ids = HashSet::new();
    for (row, derived) in rows.iter().zip(derived) {
        let old = id(row)?;
        let new = derived;
        if external_ids.contains(&new) {
            return Err("migrated identity collides with an external reference".into());
        }
        if !final_ids.insert(new) {
            return Err("migrated identity collision".into());
        }
        replacement.insert(old, new);
    }
    let ids = by.keys().map(|old| (*old, replacement[old])).collect();
    let added = added_indices
        .iter()
        .map(|&i| replacement[&id(&rows[i]).unwrap()])
        .collect();
    rewrite(&mut document, &replacement, 0, &mut steps)?;
    validate_graph_format(&document, GraphFormat::CanonicalV3)?;
    Ok(GraphMigration {
        source: GraphFormat::LegacyV2,
        target: GraphFormat::CanonicalV3,
        document,
        ids,
        added,
        element_indices,
    })
}
fn collect_external_references(
    value: &Value,
    local: &HashMap<Uuid, usize>,
    external: &mut HashSet<Uuid>,
    depth: usize,
    steps: &mut usize,
) -> Result<(), String> {
    charge(steps, 1)?;
    if depth > 128 {
        return Err("nested JSON exceeds migration depth limit".into());
    }
    match value {
        Value::Array(values) => {
            for value in values {
                collect_external_references(value, local, external, depth + 1, steps)?;
            }
        }
        Value::Object(object) => {
            if let Some(id) = object
                .get("@id")
                .and_then(Value::as_str)
                .and_then(|id| Uuid::parse_str(id).ok())
            {
                if !local.contains_key(&id) {
                    external.insert(id);
                }
            }
            for value in object.values() {
                collect_external_references(value, local, external, depth + 1, steps)?;
            }
        }
        _ => {}
    }
    Ok(())
}
fn rewrite(
    value: &mut Value,
    replacements: &HashMap<Uuid, Uuid>,
    depth: usize,
    steps: &mut usize,
) -> Result<(), String> {
    charge(steps, 1)?;
    if depth > 128 {
        return Err("nested JSON exceeds migration depth limit".into());
    }
    match value {
        Value::Array(a) => {
            for v in a {
                rewrite(v, replacements, depth + 1, steps)?;
            }
        }
        Value::Object(map) => {
            for (key, v) in map {
                if matches!(key.as_str(), "@id" | "elementId") {
                    if let Some(new) = v
                        .as_str()
                        .and_then(|s| Uuid::parse_str(s).ok())
                        .and_then(|id| replacements.get(&id))
                    {
                        *v = json!(new);
                    }
                } else {
                    rewrite(v, replacements, depth + 1, steps)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::model_to_compact_json, loader::load_document_with_format, model::Model};

    fn source(format: GraphFormat) -> Model {
        let mut model = Model::with_graph_format(format);
        assert!(model.add_source("document-1.sysml",
            "package P { attribute x = 1; attribute y = 2; attribute z = if true ? x else y; }").diagnostics.is_empty());
        model
    }

    fn constructor_source(format: GraphFormat, expression: &str) -> Model {
        let mut model = Model::with_graph_format(format);
        let text = format!(
            "class C {{feature x; feature y;}} class H {{feature t:C;}} feature h:H; feature call={expression};"
        );
        assert!(
            model
                .add_source("constructor.kerml", &text)
                .diagnostics
                .is_empty()
        );
        model
    }

    #[test]
    fn constructor_migration_matches_direct_lowering_and_preserves_identity_domain() {
        for expression in [
            "new C()",
            "new C(1)",
            "new C(y=2, x=1)",
            "new h.t()",
            "new h.t(1)",
            "new h.t(y=2, x=1)",
            "new C(new h.t(), if true ? new h.t(1) else new C(y=2))",
            "new C(new C(), if true ? new C(1) else new C(y=2))",
        ] {
            let legacy =
                model_to_compact_json(&constructor_source(GraphFormat::LegacyV2, expression));
            let canonical =
                model_to_compact_json(&constructor_source(GraphFormat::CanonicalV3, expression));
            let migrated = migrate_conditional_graph(&legacy, &|_| None).unwrap();
            assert_eq!(migrated.document, canonical, "{expression}");
            assert!(
                load_document_with_format(&canonical, &HashMap::new(), GraphFormat::CanonicalV3)
                    .is_ok(),
                "{expression}"
            );
            assert_eq!(migrated.ids.len(), legacy.as_array().unwrap().len());
            assert_eq!(
                migrated.element_indices.len(),
                legacy.as_array().unwrap().len()
            );
            for (old, &new_index) in legacy
                .as_array()
                .unwrap()
                .iter()
                .zip(&migrated.element_indices)
            {
                assert_eq!(
                    migrated.ids[&id(old).unwrap()],
                    id(&canonical[new_index]).unwrap()
                );
                assert_eq!(old["@type"], canonical[new_index]["@type"]);
            }
            for row in canonical
                .as_array()
                .unwrap()
                .iter()
                .filter(|r| r["@type"] == "ReturnParameterMembership")
            {
                let result = id(&row["ownedRelatedElement"][0]).unwrap();
                assert!(
                    !migrated.ids.contains_key(&result),
                    "result must not reuse a legacy argument UUID"
                );
                assert!(!migrated.ids.contains_key(&id(row).unwrap()));
            }
            assert!(migrate_conditional_graph(&canonical, &|_| None).is_err());
        }
    }

    #[test]
    fn constructor_transport_preserves_semantically_invalid_selector_for_diagnostics() {
        let source = "package P; feature call=new P();";
        let mut legacy = Model::with_graph_format(GraphFormat::LegacyV2);
        let mut canonical = Model::with_graph_format(GraphFormat::CanonicalV3);
        assert!(
            legacy
                .add_source("invalid-selector.kerml", source)
                .diagnostics
                .is_empty()
        );
        assert!(
            canonical
                .add_source("invalid-selector.kerml", source)
                .diagnostics
                .is_empty()
        );
        let legacy = model_to_compact_json(&legacy);
        let canonical = model_to_compact_json(&canonical);
        assert_eq!(
            migrate_conditional_graph(&legacy, &|_| None)
                .unwrap()
                .document,
            canonical
        );
        assert!(validate_graph_format(&canonical, GraphFormat::CanonicalV3).is_ok());
        assert!(
            load_document_with_format(&canonical, &HashMap::new(), GraphFormat::CanonicalV3)
                .is_ok()
        );
        // No Type claim is made: the selector remains the Package from source.
        let rows = canonical.as_array().unwrap();
        let by = index(rows, &mut 0).unwrap();
        let constructor = rows
            .iter()
            .find(|r| r["@type"] == "ConstructorExpression")
            .unwrap();
        let selector = by[&refs(constructor, "ownedRelationship").unwrap()[0]];
        let target = by[&id(&rows[selector]["memberElement"]).unwrap()];
        assert_eq!(rows[target]["@type"], "Package");
    }

    #[test]
    fn constructor_shape_refuses_mixed_contracts_and_malformed_claims() {
        let original =
            model_to_compact_json(&constructor_source(GraphFormat::CanonicalV3, "new C(x=1)"));
        let rows = original.as_array().unwrap();
        let by = index(rows, &mut 0).unwrap();
        let owner = rows
            .iter()
            .position(|r| r["@type"] == "ConstructorExpression")
            .unwrap();
        let relationships = refs(&rows[owner], "ownedRelationship").unwrap();
        let membership = by[&relationships[1]];
        let result = by[&one(&rows[membership], "ownedRelatedElement").unwrap()];
        let parameter = by[&one(&rows[result], "ownedRelationship").unwrap()];
        assert!(validate_conditional_graph_format(&original, GraphFormat::CanonicalV3).is_ok());
        assert!(validate_conditional_graph_format(&original, GraphFormat::LegacyV2).is_err());
        let mut hidden_result = original.clone();
        hidden_result[owner]["ownedRelationship"] = json!([{"@id":relationships[0]}]);
        assert!(validate_conditional_graph_format(&hidden_result, GraphFormat::LegacyV2).is_err());
        let legacy =
            model_to_compact_json(&constructor_source(GraphFormat::LegacyV2, "new C(x=1)"));
        assert!(validate_conditional_graph_format(&legacy, GraphFormat::CanonicalV3).is_err());
        for mutation in 0..8 {
            let mut document = original.clone();
            match mutation {
                0 => document[result]["direction"] = json!("in"),
                1 => document[owner]["ownedRelationship"]
                    .as_array_mut()
                    .unwrap()
                    .push(json!({"@id":relationships[1]})),
                2 => document[result]["ownedRelationship"] = json!([]),
                3 => {
                    document[parameter]["owningRelatedElement"] =
                        json!({"@id":id(&rows[owner]).unwrap()})
                }
                4 => document[owner]["result"] = json!({"@id":id(&rows[owner]).unwrap()}),
                5 => {
                    document[membership]["memberElement"] = json!({"@id":id(&rows[owner]).unwrap()})
                }
                6 => document[membership]["ownedRelatedElement"] = json!([]),
                _ => document[result]["declaredName"] = json!("lost"),
            }
            assert!(
                validate_conditional_graph_format(&document, GraphFormat::CanonicalV3).is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn canonical_constructor_refuses_unrepresentable_scalars_and_contradictory_aliases() {
        let model = constructor_source(GraphFormat::CanonicalV3, "new C(x=1)");
        for original in [
            model_to_compact_json(&model),
            crate::full::model_to_full_json(&model),
        ] {
            validate_conditional_graph_format(&original, GraphFormat::CanonicalV3).unwrap();
            let rows = original.as_array().unwrap();
            let by: HashMap<_, _> = rows
                .iter()
                .enumerate()
                .map(|(i, row)| (id(row).unwrap(), i))
                .collect();
            let constructor = rows
                .iter()
                .position(|row| row["@type"] == "ConstructorExpression")
                .unwrap();
            let result_membership = by[&refs(&rows[constructor], "ownedRelationship").unwrap()[1]];
            let result = by[&one(&rows[result_membership], "ownedRelatedElement").unwrap()];
            let parameter = refs(&rows[result], "ownedRelationship")
                .unwrap()
                .into_iter()
                .map(|id| by[&id])
                .find(|&i| rows[i]["@type"] == "ParameterMembership")
                .unwrap();
            let argument = by[&one(&rows[parameter], "ownedRelatedElement").unwrap()];
            let redefinition = refs(&rows[argument], "ownedRelationship")
                .unwrap()
                .into_iter()
                .map(|id| by[&id])
                .find(|&i| rows[i]["@type"] == "Redefinition")
                .unwrap();
            let selector = by[&refs(&rows[constructor], "ownedRelationship").unwrap()[0]];
            let value = refs(&rows[argument], "ownedRelationship")
                .unwrap()
                .into_iter()
                .map(|id| by[&id])
                .find(|&i| rows[i]["@type"] == "FeatureValue")
                .unwrap();
            for (index, key, invalid) in [
                (result, "isUnique", json!(false)),
                (result, "isUnique", Value::Null),
                (result, "isConstant", json!(true)),
                (result, "isOrdered", json!(true)),
                (result, "isAbstract", json!(true)),
                (argument, "isUnique", json!(false)),
                (argument, "isVariable", json!(true)),
                (argument, "declaredName", json!("lost")),
                (argument, "aliasIds", json!(["lost"])),
                (selector, "visibility", json!("private")),
                (parameter, "visibility", json!("private")),
                (result_membership, "visibility", json!("protected")),
                (value, "isInitial", json!(true)),
                (value, "isDefault", json!(true)),
                (value, "isDefault", Value::Null),
            ] {
                let mut document = original.clone();
                document[index][key] = invalid;
                assert!(
                    validate_conditional_graph_format(&document, GraphFormat::CanonicalV3).is_err(),
                    "{index}.{key}"
                );
                assert!(
                    load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                        .is_err(),
                    "{index}.{key}"
                );
            }
            let wrong = json!({"@id":id(&rows[result_membership]).unwrap()});
            for (index, key, invalid) in [
                (parameter, "ownedMemberParameter", wrong.clone()),
                (parameter, "ownedMemberFeature", wrong.clone()),
                (result_membership, "ownedMemberParameter", wrong.clone()),
                (parameter, "source", json!([wrong.clone()])),
                (value, "value", wrong.clone()),
                (value, "featureWithValue", wrong.clone()),
                (redefinition, "general", wrong.clone()),
                (redefinition, "subsettedFeature", wrong.clone()),
                (redefinition, "target", json!([wrong.clone()])),
                (redefinition, "source", json!([wrong.clone()])),
                (
                    redefinition,
                    "relatedElement",
                    json!([wrong.clone(), wrong.clone()]),
                ),
                (argument, "owningMembership", wrong.clone()),
                (argument, "owningFeatureMembership", wrong.clone()),
                (argument, "owningType", wrong.clone()),
                (
                    parameter,
                    "relatedElement",
                    json!([wrong.clone(), wrong.clone()]),
                ),
                (result, "ownedFeature", json!([wrong.clone()])),
                (constructor, "ownedFeature", json!([wrong.clone()])),
                (
                    constructor,
                    "ownedFeatureMembership",
                    json!([{"@id":id(&rows[parameter]).unwrap()}]),
                ),
            ] {
                let mut document = original.clone();
                document[index][key] = invalid;
                assert!(
                    validate_conditional_graph_format(&document, GraphFormat::CanonicalV3).is_err(),
                    "{index}.{key}"
                );
            }
        }
    }

    #[test]
    fn constructor_full_selector_retains_external_name_compatibility() {
        let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
        model.add_library_source("constructor-library.kerml", "class External {feature x;}");
        assert!(
            model
                .add_source(
                    "external-constructor.kerml",
                    "feature call=new External(x=1);"
                )
                .diagnostics
                .is_empty()
        );
        let mut document = crate::full::model_to_full_json(&model);
        let rows = document.as_array().unwrap();
        let by: HashMap<_, _> = rows
            .iter()
            .enumerate()
            .map(|(i, row)| (id(row).unwrap(), i))
            .collect();
        let constructor = rows
            .iter()
            .find(|row| row["@type"] == "ConstructorExpression")
            .unwrap();
        let selector = by[&refs(constructor, "ownedRelationship").unwrap()[0]];
        let target = id(&rows[selector]["memberElement"]).unwrap();
        assert!(
            !by.contains_key(&target),
            "library target should be outside user payload"
        );
        // A full producer with the external library context can materialize
        // these names. Their historical recovery is outside the new wrapper
        // preservation contract; shape validation is not a lossless certificate.
        document[selector]["memberName"] = json!("External");
        document[selector]["memberShortName"] = json!("Ext");
        validate_conditional_graph_format(&document, GraphFormat::CanonicalV3).unwrap();
    }

    #[test]
    fn constructor_migration_refuses_existing_result_and_temporary_capture_atomically() {
        let original =
            model_to_compact_json(&constructor_source(GraphFormat::LegacyV2, "new C(1)"));
        let constructor = original
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["@type"] == "ConstructorExpression")
            .unwrap();
        for label in [
            b"canonical-constructor-result".as_slice(),
            b"canonical-constructor-result-membership".as_slice(),
        ] {
            let mut document = original.clone();
            let external = Uuid::new_v5(&id(constructor).unwrap(), label);
            let root = id(&document[0]).unwrap();
            let alias = Uuid::new_v5(&root, b"::externalAlias");
            document[0]["ownedRelationship"]
                .as_array_mut()
                .unwrap()
                .push(json!({"@id":alias}));
            document.as_array_mut().unwrap().push(json!({
                "@id":alias,"@type":"Membership","elementId":alias,"isImplied":false,
                "ownedRelationship":[],"ownedRelatedElement":[],"owningRelationship":null,
                "owningRelatedElement":{"@id":root},"memberName":"externalAlias","memberElement":{"@id":external}
            }));
            let snapshot = document.clone();
            assert!(
                migrate_conditional_graph(&document, &|_| None)
                    .unwrap_err()
                    .contains("temporary migration identity collision")
            );
            assert_eq!(document, snapshot);
        }
    }

    #[test]
    fn loaders_refuse_profile_mismatches_even_when_operand_metaclasses_match() {
        for source_format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let model = source(source_format);
            let other = if source_format == GraphFormat::LegacyV2 {
                GraphFormat::CanonicalV3
            } else {
                GraphFormat::LegacyV2
            };
            for document in [
                model_to_compact_json(&model),
                crate::full::model_to_full_json(&model),
            ] {
                assert!(validate_conditional_graph_format(&document, source_format).is_ok());
                assert!(
                    load_document_with_format(&document, &HashMap::new(), source_format).is_ok()
                );
                assert!(load_document_with_format(&document, &HashMap::new(), other).is_err());
            }
        }
    }

    #[test]
    fn unversioned_loader_retains_foreign_conditional_recovery() {
        let canonical = source(GraphFormat::CanonicalV3);
        for document in [
            model_to_compact_json(&canonical),
            crate::full::model_to_full_json(&canonical),
        ] {
            let (model, mut resolved, _, warnings) =
                crate::loader::load_document(&document, &HashMap::new()).unwrap();
            assert_eq!(model.graph_format(), GraphFormat::LegacyV2);
            assert!(
                warnings
                    .iter()
                    .any(|warning| warning.contains("no structural counterpart")),
                "{warnings:?}"
            );
            assert_eq!(
                resolved.evaluate_qualified("P::z"),
                Ok(crate::eval::Value::Integer(1))
            );
            assert!(
                load_document_with_format(&document, &HashMap::new(), GraphFormat::LegacyV2)
                    .is_err()
            );
            assert!(
                load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                    .is_ok()
            );
        }
    }

    #[test]
    fn conditional_alias_and_direction_contradictions_are_refused() {
        let model = source(GraphFormat::CanonicalV3);
        let original = model_to_compact_json(&model);
        let rows = original.as_array().unwrap();
        let mut steps = 0;
        let by = index(rows, &mut steps).unwrap();
        let (value, expression) = operands(rows, &by, &mut steps).unwrap()[0];
        let member_index = by[&one(&rows[expression], "ownedRelationship").unwrap()];
        let mut document = original.clone();
        let wrong = document[0]["@id"].clone();
        document[member_index]["memberElement"] = json!({"@id": wrong});
        assert!(validate_conditional_graph_format(&document, GraphFormat::CanonicalV3).is_err());
        let feature = by[&id(&rows[value]["owningRelatedElement"]).unwrap()];
        let mut document = original.clone();
        document[feature]["direction"] = json!("out");
        assert!(validate_graph_format(&document, GraphFormat::CanonicalV3).is_err());
        assert!(
            load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                .is_err()
        );
    }

    #[test]
    fn migration_distinguishes_identity_domain_from_library_metaclass() {
        let text = "standard library package L { feature value = if true ? 1 else 2; }";
        let mut user = Model::new();
        user.add_source("user.kerml", text);
        assert!(migrate_conditional_graph(&model_to_compact_json(&user), &|_| None).is_ok());
        let mut library = Model::new();
        library.add_library_source("library.kerml", text);
        assert!(
            migrate_conditional_graph(&crate::json::library_to_compact_json(&library), &|_| None)
                .is_err()
        );
        let mut foreign = model_to_compact_json(&source(GraphFormat::LegacyV2));
        let old = id(&foreign[1]).unwrap();
        let new = Uuid::new_v5(&old, b"foreign-id");
        rewrite(&mut foreign, &HashMap::from([(old, new)]), 0, &mut 0).unwrap();
        assert!(
            load_document_with_format(&foreign, &HashMap::new(), GraphFormat::LegacyV2).is_ok()
        );
        assert!(migrate_conditional_graph(&foreign, &|_| None).is_err());
    }

    #[test]
    fn migration_refuses_duplicate_ownership_roles() {
        let mut document = model_to_compact_json(&source(GraphFormat::LegacyV2));
        let row = document
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|row| row["owningRelationship"].is_object())
            .unwrap();
        row["owningRelatedElement"] = row["owningRelationship"].clone();
        assert!(migrate_conditional_graph(&document, &|_| None).is_err());
    }

    #[test]
    fn migration_refuses_capturing_an_external_reference() {
        let mut document = model_to_compact_json(&source(GraphFormat::LegacyV2));
        let initial = migrate_conditional_graph(&document, &|_| None).unwrap();
        let old_ids: HashSet<_> = initial.ids.keys().copied().collect();
        // Added wrappers may reuse former operand/relationship UUIDs. A moved
        // descendant still introduces a final identity outside the old domain.
        let added = initial
            .document
            .as_array()
            .unwrap()
            .iter()
            .map(|row| id(row).unwrap())
            .find(|id| !old_ids.contains(id))
            .unwrap();
        let root = id(&document[0]).unwrap();
        let alias = Uuid::new_v5(&root, b"::externalAlias");
        document[0]["ownedRelationship"]
            .as_array_mut()
            .unwrap()
            .push(json!({"@id":alias}));
        document.as_array_mut().unwrap().push(json!({
            "@id":alias,"@type":"Membership","elementId":alias,"isImplied":false,
            "ownedRelationship":[],"ownedRelatedElement":[],"owningRelationship":null,
            "owningRelatedElement":{"@id":root},"memberName":"externalAlias",
            "memberElement":{"@id":added}
        }));
        let error = migrate_conditional_graph(&document, &|_| None).unwrap_err();
        assert!(
            error.contains("collides with an external reference"),
            "{error}"
        );
    }

    #[test]
    fn migration_temporary_ids_cannot_capture_external_references() {
        let original = model_to_compact_json(&source(GraphFormat::LegacyV2));
        let rows = original.as_array().unwrap();
        let by = index(rows, &mut 0).unwrap();
        let (_, expression) = operands(rows, &by, &mut 0).unwrap()[0];
        let operand = id(&rows[expression]).unwrap();
        for label in [
            b"canonical-conditional-wrapper".as_slice(),
            b"canonical-conditional-membership".as_slice(),
        ] {
            let external = Uuid::new_v5(&operand, label);
            let mut document = original.clone();
            let root = id(&document[0]).unwrap();
            let alias = Uuid::new_v5(&root, b"::externalAlias");
            document[0]["ownedRelationship"]
                .as_array_mut()
                .unwrap()
                .push(json!({"@id":alias}));
            document.as_array_mut().unwrap().push(json!({
                "@id":alias,"@type":"Membership","elementId":alias,"isImplied":false,
                "ownedRelationship":[],"ownedRelatedElement":[],"owningRelationship":null,
                "owningRelatedElement":{"@id":root},"memberName":"externalAlias",
                "memberElement":{"@id":external}
            }));
            let snapshot = document.clone();
            let error = migrate_conditional_graph(&document, &|_| None).unwrap_err();
            assert!(
                error.contains("temporary migration identity collision"),
                "{error}"
            );
            assert_eq!(document, snapshot);
        }
    }

    #[test]
    fn legacy_loader_preserves_foreign_direct_expression_parameter_support() {
        let mut document = model_to_compact_json(&source(GraphFormat::LegacyV2));
        let rows = document.as_array().unwrap();
        let by = index(rows, &mut 0).unwrap();
        let (value, expression) = operands(rows, &by, &mut 0).unwrap()[0];
        let feature = by[&id(&rows[value]["owningRelatedElement"]).unwrap()];
        let parameter = by[&id(&rows[feature]["owningRelationship"]).unwrap()];
        let expression_id = id(&rows[expression]).unwrap();
        let parameter_id = id(&rows[parameter]).unwrap();
        document[parameter]["ownedRelatedElement"] = json!([{"@id":expression_id}]);
        document[expression]["owningRelationship"] = json!({"@id":parameter_id});
        let rows = document.as_array_mut().unwrap();
        for i in [value.max(feature), value.min(feature)] {
            rows.remove(i);
        }
        assert!(
            load_document_with_format(&document, &HashMap::new(), GraphFormat::LegacyV2).is_ok()
        );
        assert!(
            load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                .is_err()
        );
        assert!(migrate_conditional_graph(&document, &|_| None).is_err());
    }

    #[test]
    fn direct_lift_does_not_override_a_conflicting_member_alias() {
        let mut document = model_to_compact_json(&source(GraphFormat::CanonicalV3));
        let rows = document.as_array().unwrap();
        let by = index(rows, &mut 0).unwrap();
        let (_, expression) = operands(rows, &by, &mut 0).unwrap()[0];
        let member = by[&one(&rows[expression], "ownedRelationship").unwrap()];
        let other = rows.iter().find(|row| row["declaredName"] == "y").unwrap()["@id"].clone();
        document[member]["memberElement"] = json!({"@id":other});
        // The compatibility lifter retains its existing alias-first fallback;
        // graph-aware loading rejects this contradiction before lifting.
        let lifted = crate::lift::from_compact_json(&document).unwrap();
        let text = sysmlv2_syntax::print::print_source(&lifted.unit);
        let mut model = Model::new();
        assert!(
            model
                .add_source("replayed.sysml", &text)
                .diagnostics
                .is_empty()
        );
        let mut resolved = crate::json::ResolvedModel::build(&model);
        assert_eq!(
            resolved.evaluate_qualified("P::z"),
            Ok(crate::eval::Value::Integer(2))
        );
        assert!(
            load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                .is_err()
        );
    }
}
