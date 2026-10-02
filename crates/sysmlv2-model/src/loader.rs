//! Loading an interchange document into a model while keeping the ids
//! it carried.
//!
//! This toolkit's model derives every element id from the ownership
//! graph (IDS.md); a document from another producer, or one emitted under
//! other unit names, carries ids the derivation would replace. The loader
//! pairs the document's elements with the rebuilt model's by ownership
//! path and records the given ids as an **overlay** — applied to the
//! resolved model for the read API and to every emitted element array —
//! so a loaded document keeps its identity end to end.

use crate::json::{ResolvedModel, model_to_compact_json};
use crate::model::Model;
use serde_json::Value;
use std::collections::HashMap;
use uuid::Uuid;

/// Explicit ids: graph-derived id → (the id the document carried, the
/// element's metaclass).
pub type ExplicitIds = HashMap<Uuid, (Uuid, &'static str)>;

/// Identity references recovered from an interchange payload, keyed by
/// reference-holder id and property name (with `#index` for arrays).
/// Binding prunes this map to the references that the lift spelled as IDs.
pub type IdReferenceBindings = HashMap<(Uuid, String), Uuid>;

/// Record payload reference identities before textual lifting can confuse
/// an anonymous target's UUID with another element's declared name.
pub fn id_reference_bindings(document: &Value) -> IdReferenceBindings {
    let Some(elements) = document.as_array() else {
        return HashMap::new();
    };
    let by_id: HashMap<_, _> = elements
        .iter()
        .filter_map(|e| Some((e.get("@id")?.as_str()?, e)))
        .collect();
    let mut out = HashMap::new();
    for element in elements {
        let Some(owner) = element
            .get("@id")
            .and_then(Value::as_str)
            .and_then(|id| Uuid::parse_str(id).ok())
        else {
            continue;
        };
        let Some(props) = element.as_object() else {
            continue;
        };
        for (key, value) in props {
            if crate::model::is_payload_usage_flag(element["@type"].as_str().unwrap_or(""), key) {
                continue;
            }
            let mut record = |slot: String, value: &Value| {
                let Some(mut target) = value.get("@id").and_then(Value::as_str) else {
                    return;
                };
                // The lift spells membership imports through the member,
                // and normal resolution restores the membership target.
                if key == "importedMembership" {
                    if let Some(member) = by_id.get(target) {
                        if let Some(id) = member
                            .get("memberElement")
                            .and_then(|v| v.get("@id"))
                            .and_then(Value::as_str)
                            .or_else(|| {
                                member
                                    .get("ownedRelatedElement")
                                    .and_then(Value::as_array)
                                    .and_then(|v| v.first())
                                    .and_then(|v| v.get("@id"))
                                    .and_then(Value::as_str)
                            })
                        {
                            target = id;
                        }
                    }
                }
                if let Ok(target) = Uuid::parse_str(target) {
                    out.insert((owner, slot), target);
                }
            };
            if let Some(items) = value.as_array() {
                for (index, item) in items.iter().enumerate() {
                    record(format!("{key}#{index}"), item);
                }
            } else {
                record(key.clone(), value);
            }
        }
    }
    out
}

/// The explicit-id map of a loaded document: `(derived id → given id)`
/// for every element of `document` whose structural counterpart in the
/// rebuilt `model` derives a different id, plus the number of document
/// elements with no counterpart. Counterparts are paired by ownership
/// path (`ids::segment_paths`): roots by document order, then the
/// `ownedRelationship` / `ownedRelatedElement` positions and names —
/// the same walk the derivation uses, so a document this toolkit emitted
/// pairs completely and maps nothing.
pub fn explicit_id_map(
    document: &Value,
    model: &Model,
    external: &dyn Fn(&str) -> Option<String>,
    warnings: &mut Vec<String>,
) -> (ExplicitIds, usize) {
    let emitted = model_to_compact_json(model);
    let (mut pairs, unmatched) = paired_id_map(document, &emitted, external, warnings);
    pairs.retain(|derived, (given, _)| derived != given);
    (pairs, unmatched)
}

fn paired_id_map(
    document: &Value,
    emitted: &Value,
    external: &dyn Fn(&str) -> Option<String>,
    warnings: &mut Vec<String>,
) -> (ExplicitIds, usize) {
    use crate::ids::segment_paths;
    let omitted = crate::lift::omitted_element_ids(document);
    // Recovery annotations preserve the original unresolved spelling. Use
    // the identity walk's spelling convention so full and compact input have
    // the same structural paths, including quoted and UUID-shaped names.
    let recovered: HashMap<_, _> = document
        .as_array()
        .into_iter()
        .flatten()
        .filter(|e| e["language"] == crate::full::UNRESOLVED_REP_LANGUAGE)
        .filter_map(|e| {
            let spelling = e.get("body")?.as_str()?;
            let leaf = crate::ids::reference_path_name(spelling).to_owned();
            Some((crate::json::dangling_id(spelling), leaf))
        })
        .collect();
    let external = |id: &str| external(id).or_else(|| recovered.get(id).cloned());
    // These expression carriers spell only a target, never a Membership
    // alias. Full emission can nevertheless project the target's memberName.
    // Ignore that projection for structural pairing with the lifted graph.
    // Namespace and general Expression body aliases retain authored names.
    let mut pairing_document = std::borrow::Cow::Borrowed(document);
    if let Some(elements) = document.as_array() {
        let reference_memberships: std::collections::HashSet<_> = elements
            .iter()
            .filter(|e| {
                matches!(
                    e["@type"].as_str(),
                    Some(
                        "FeatureReferenceExpression"
                            | "FeatureChainExpression"
                            | "InvocationExpression"
                            | "ConstructorExpression"
                            | "MetadataAccessExpression"
                    )
                )
            })
            .filter_map(|e| e["ownedRelationship"].as_array())
            .flatten()
            .filter_map(|r| r["@id"].as_str())
            .collect();
        let projected: Vec<_> = elements
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e["@type"] == "Membership"
                    && e.get("qualifiedName").is_some()
                    && e["@id"]
                        .as_str()
                        .is_some_and(|id| reference_memberships.contains(id))
                    && (e["memberName"].is_string() || e["memberShortName"].is_string())
            })
            .map(|(i, _)| i)
            .collect();
        if !projected.is_empty() {
            let elements = pairing_document.to_mut().as_array_mut().unwrap();
            for i in projected {
                let row = elements[i].as_object_mut().unwrap();
                row.remove("memberName");
                row.remove("memberShortName");
            }
        }
    }
    // Pair the same authored composition that the lift reconstructs. Generated
    // redefinitions can supply effective names to otherwise positional argument
    // carriers, and omitted relationships can shift later positional segments.
    // Keep row indices stable while removing only the lift's omitted composition
    // edges; semantic references and authored naming evidence remain untouched.
    if !omitted.is_empty() {
        if let Some(elements) = pairing_document.to_mut().as_array_mut() {
            for element in elements {
                for key in ["ownedRelationship", "ownedRelatedElement"] {
                    if let Some(children) = element.get_mut(key).and_then(Value::as_array_mut) {
                        children.retain(|child| {
                            !child["@id"].as_str().is_some_and(|id| omitted.contains(id))
                        });
                    }
                }
            }
        }
    }
    let (mut doc_paths, model_paths) = match (
        segment_paths(&pairing_document, &external),
        segment_paths(emitted, &external),
    ) {
        (Ok(d), Ok(m)) => (d, m),
        (Err(e), _) | (_, Err(e)) => {
            warnings.push(format!(
                "the document's elements could not be paired with the model's; ids are not \
                 preserved: {e}"
            ));
            return (HashMap::new(), 0);
        }
    };
    // Detached omitted rows must not become roots, especially Namespace rows
    // that would change the document ordinal of every following authored root.
    for (i, path) in doc_paths.iter_mut().enumerate() {
        if document[i]["@id"]
            .as_str()
            .is_some_and(|id| omitted.contains(id))
        {
            *path = None;
        }
    }
    let id_at = |v: &Value, i: usize| -> Option<Uuid> {
        v.get(i)?
            .get("@id")?
            .as_str()
            .and_then(|s| Uuid::parse_str(s).ok())
    };
    let ty_at = |v: &Value, i: usize| -> String {
        v.get(i)
            .and_then(|e| e.get("@type"))
            .and_then(|t| t.as_str())
            .unwrap_or("")
            .to_string()
    };
    // Paths carry the root's *element index*; key roots by their ordinal
    // among roots instead, so a document whose elements are not in this
    // toolkit's emission order still pairs root by root (roots are in
    // document order on both sides — units are lifted in document order).
    // Only document roots (`Namespace` elements) count for the ordinal
    // when a payload has any, so a stray unowned element cannot shift
    // the pairing of every document.
    let ordinal_paths =
        |paths: Vec<Option<(usize, String)>>, arr: &Value| -> Vec<Option<(usize, String)>> {
            let all: std::collections::BTreeSet<usize> =
                paths.iter().flatten().map(|(r, _)| *r).collect();
            let namespaces: Vec<usize> = all
                .iter()
                .copied()
                .filter(|&r| ty_at(arr, r) == "Namespace")
                .collect();
            let roots: Vec<usize> = if namespaces.is_empty() {
                all.into_iter().collect()
            } else {
                namespaces
            };
            paths
                .into_iter()
                .map(|p| p.and_then(|(r, chain)| roots.binary_search(&r).ok().map(|o| (o, chain))))
                .collect()
        };
    let doc_paths = ordinal_paths(doc_paths, document);
    let model_paths = ordinal_paths(model_paths, emitted);
    // A document whose root is not a document Namespace (a bare Package
    // at the top, as other producers emit) is rebuilt under a synthetic
    // root Namespace whose sole member it becomes: re-root the document's
    // chains under that member so the pairing lines up.
    let doc_root_is_namespace: Vec<bool> = {
        let mut v = Vec::new();
        for (i, p) in doc_paths.iter().enumerate() {
            if let Some((o, chain)) = p {
                if chain.is_empty() {
                    if v.len() <= *o {
                        v.resize(*o + 1, true);
                    }
                    v[*o] = ty_at(document, i) == "Namespace";
                }
            }
        }
        v
    };
    let sole_member_chain: HashMap<usize, String> = {
        // A named sole member chains past its membership (`::Name`); an
        // unnamed one sits under a positional membership (`r0/e0`).
        let mut per_root: HashMap<usize, Vec<String>> = HashMap::new();
        for p in model_paths.iter().flatten() {
            if !p.1.is_empty() && !p.1.contains('/') {
                per_root.entry(p.0).or_default().push(p.1.clone());
            }
        }
        per_root
            .into_iter()
            .filter_map(|(o, chains)| {
                if chains.len() != 1 {
                    return None;
                }
                let c = &chains[0];
                if c.starts_with("::") {
                    Some((o, c.clone()))
                } else {
                    let element = format!("{c}/e0");
                    model_paths
                        .iter()
                        .flatten()
                        .any(|p| p.0 == o && p.1 == element)
                        .then_some((o, element))
                }
            })
            .collect()
    };
    let doc_paths: Vec<Option<(usize, String)>> = doc_paths
        .into_iter()
        .map(|p| {
            p.map(|(o, chain)| {
                if doc_root_is_namespace.get(o).copied().unwrap_or(true) {
                    return (o, chain);
                }
                match sole_member_chain.get(&o) {
                    Some(c) if chain.is_empty() => (o, c.clone()),
                    Some(c) => (o, format!("{c}/{chain}")),
                    None => (o, chain),
                }
            })
        })
        .collect();
    let mut by_path: HashMap<(usize, String), Option<(Uuid, String)>> = HashMap::new();
    for (i, path) in model_paths.into_iter().enumerate() {
        if let (Some(path), Some(id)) = (path, id_at(emitted, i)) {
            by_path
                .entry(path)
                .and_modify(|value| *value = None)
                .or_insert_with(|| Some((id, ty_at(emitted, i))));
        }
    }
    // Elements the lift deliberately drops are not "unpreserved": implied
    // relationships and unresolved-reference recovery annotations (with
    // their memberships) of a full-form document.
    let mut doc_path_counts = HashMap::new();
    for path in doc_paths.iter().flatten() {
        *doc_path_counts.entry(path).or_insert(0usize) += 1;
    }
    let mut map = HashMap::new();
    let mut unmatched = 0usize;
    for (i, path) in doc_paths.iter().enumerate() {
        let Some(given) = id_at(document, i) else {
            continue;
        };
        if omitted.contains(given.to_string().as_str()) {
            continue;
        }
        let doc_ty = ty_at(document, i);
        match path
            .as_ref()
            .filter(|p| doc_path_counts.get(p) == Some(&1))
            .and_then(|p| by_path.get(p))
            .and_then(Option::as_ref)
        {
            // Positional pairing is only trusted between elements of the
            // same metaclass (a document that lists a feature's typing
            // and value in the other order must not swap their ids). The
            // one sanctioned change is the chain-target membership this
            // toolkit now spells as an OwningMembership.
            Some((derived, model_ty))
                if *model_ty == doc_ty
                    || (doc_ty == "Membership" && model_ty == "OwningMembership") =>
            {
                let ty = crate::metaclass_name(model_ty).unwrap_or("");
                map.insert(*derived, (given, ty));
            }
            _ => unmatched += 1,
        }
    }
    (map, unmatched)
}

/// Apply a session's explicit ids to an emitted element array: every
/// id the derivation produced is replaced by the id the document
/// carried (`@id`, `elementId`, and every reference), and a reference the
/// lift could only spell as a quoted id (`{"@ref": "'<uuid>'"}`) binds to
/// the element carrying that id. Emission re-lowers the session's text,
/// so the overlay is applied on every emission path; the resolved model
/// carries the same overlay for the read API.
pub fn overlay_explicit_ids(value: &mut Value, explicit_ids: &ExplicitIds) {
    overlay_explicit_ids_impl(value, explicit_ids, true);
}

/// Apply explicit identities and only the payload-proven reference bindings.
/// Authored UUID-shaped `@ref` spellings without such evidence stay names.
/// Supply the current endpoint values from `ResolvedModel::payload_id_reference_values`
/// after binding each rebuilt model; spelling hints are not endpoint values.
pub fn overlay_payload_ids(
    value: &mut Value,
    explicit_ids: &ExplicitIds,
    bindings: &IdReferenceBindings,
) {
    overlay_explicit_ids_impl(value, explicit_ids, false);
    let Some(elements) = value.as_array_mut() else {
        return;
    };
    for element in elements {
        let Some(owner) = element
            .get("@id")
            .and_then(Value::as_str)
            .and_then(|s| Uuid::parse_str(s).ok())
        else {
            continue;
        };
        let ty = element["@type"]
            .as_str()
            .and_then(crate::metaclass_name)
            .unwrap_or("");
        let Some(properties) = element.as_object_mut() else {
            continue;
        };
        for (key, property) in properties.iter_mut() {
            if crate::model::is_payload_usage_flag(ty, key) {
                continue;
            }
            let apply = |slot: String, value: &mut Value| {
                if let Some(target) = bindings.get(&(owner, slot)) {
                    // The retained hint already proves that this exact slot
                    // was spelled as its UUID in the rebuilt source. Repeated
                    // lowering can otherwise resolve a lexical UUID namesake.
                    if value.get("@ref").is_some() || value.get("@id").is_some() {
                        *value = serde_json::json!({"@id": target.to_string()});
                    }
                }
            };
            if let Some(items) = property.as_array_mut() {
                for (index, item) in items.iter_mut().enumerate() {
                    apply(format!("{key}#{index}"), item);
                }
            } else {
                apply(key.clone(), property);
            }
        }
    }
}

fn overlay_explicit_ids_impl(value: &mut Value, explicit_ids: &ExplicitIds, bind_unproven: bool) {
    let text_map: HashMap<String, String> = explicit_ids
        .iter()
        .map(|(d, (g, _))| (d.to_string(), g.to_string()))
        .collect();
    fn remap(v: &mut Value, map: &HashMap<String, String>) {
        match v {
            Value::Object(o) => {
                let ty = o
                    .get("@type")
                    .and_then(Value::as_str)
                    .and_then(crate::metaclass_name)
                    .unwrap_or("");
                for (k, x) in o.iter_mut() {
                    if crate::model::is_payload_usage_flag(ty, k) {
                        continue;
                    }
                    if (k == "@id"
                        || k == "elementId"
                        || k == "memberElementId"
                        || k == "ownedMemberElementId")
                        && x.is_string()
                    {
                        if let Some(n) = map.get(x.as_str().unwrap()) {
                            *x = Value::String(n.clone());
                        }
                    } else {
                        remap(x, map);
                    }
                }
            }
            Value::Array(a) => a.iter_mut().for_each(|x| remap(x, map)),
            _ => {}
        }
    }
    remap(value, &text_map);
    // An id-shaped spelling is a reference by id whether or not its target
    // is in the document (a library element with no library loaded).
    fn bind(v: &mut Value) {
        match v {
            Value::Object(o) => {
                let spelled = o
                    .get("@ref")
                    .and_then(|r| r.as_str())
                    .map(|r| r.trim_matches('\'').to_string());
                if let Some(id) = spelled.filter(|id| Uuid::parse_str(id).is_ok()) {
                    o.clear();
                    o.insert("@id".into(), Value::String(id));
                    return;
                }
                let ty = o
                    .get("@type")
                    .and_then(Value::as_str)
                    .and_then(crate::metaclass_name)
                    .unwrap_or("");
                for (key, value) in o.iter_mut() {
                    if !crate::model::is_payload_usage_flag(ty, key) {
                        bind(value);
                    }
                }
            }
            Value::Array(a) => a.iter_mut().for_each(bind),
            _ => {}
        }
    }
    if bind_unproven {
        bind(value);
    }
}

/// Retain only independently paired owned Boolean fields. UUID equality alone
/// is not a pairing proof, and ambiguous source or payload identities refuse.
fn retain_payload_usage_flags(
    model: &mut Model,
    resolved: &ResolvedModel,
    document: &Value,
    pairs: &ExplicitIds,
    warnings: &mut Vec<String>,
) -> usize {
    let mut source_ids = HashMap::new();
    let mut anchors = HashMap::new();
    for e in resolved.user_elements() {
        source_ids
            .entry(resolved.element_id(e))
            .and_modify(|v| *v = None)
            .or_insert(Some(e));
        if let Some((unit, path)) = resolved.payload_owned_flag_anchor(e) {
            *anchors.entry((unit, path)).or_insert(0usize) += 1;
        }
    }
    let mut input_ids = HashMap::new();
    for row in document.as_array().into_iter().flatten() {
        if let Some(id) = row
            .get("@id")
            .and_then(Value::as_str)
            .and_then(|id| Uuid::parse_str(id).ok())
        {
            input_ids
                .entry(id)
                .and_modify(|v| *v = None)
                .or_insert(Some(row));
        }
    }
    let mut restored = 0;
    let mut declined = 0;
    for (derived, (given, ty)) in pairs {
        if !crate::metaclass::conforms(ty, "Usage") {
            continue;
        }
        let Some(row) = input_ids.get(given).copied().flatten() else {
            declined += 1;
            continue;
        };
        let mut flags = crate::properties::Properties::new();
        let mut present = false;
        for &key in crate::model::PAYLOAD_USAGE_FLAGS {
            let Some((_, Some(spec))) = crate::semantic_catalog::property(ty, key) else {
                continue;
            };
            if spec.derived || spec.target != "Boolean" {
                continue;
            }
            for &name in spec.storage_names {
                if let Some(value) = row.get(name) {
                    flags.insert_payload_flag(name, value.clone());
                    present = true;
                }
            }
        }
        if !present {
            continue;
        }
        let Some(element) = source_ids.get(derived).copied().flatten() else {
            declined += 1;
            continue;
        };
        let Some(anchor) = resolved.payload_owned_flag_anchor(element) else {
            declined += 1;
            continue;
        };
        if resolved.element_type(element) != *ty || anchors.get(&anchor) != Some(&1) {
            declined += 1;
            continue;
        }
        let (unit, path) = anchor;
        model.retain_payload_flags(
            unit,
            path,
            crate::model::PayloadOwnedFlags {
                metaclass: ty,
                flags,
            },
        );
        restored += 1;
    }
    if declined != 0 {
        warnings.push(format!("{declined} Usage payload row(s) could not preserve owned flags because their structural pairing is ambiguous"));
    }
    restored
}

/// Load a compact (or full) interchange document into a fresh model
/// with no library: the lift names references through `names`
/// (id text → qualified-name segments, as [`crate::json::library_name_map`]
/// produces), the text is rebuilt, and the document's ids are kept as
/// explicit ids. Returns the model, its resolved form with the overlay
/// applied, the overlay, and the lift's non-fatal problems.
/// This compatibility entry point rebuilds legacy graphs and reports unpaired
/// rows as warnings. Use [`load_document_with_format`] to enforce a graph contract.
pub fn load_document(
    document: &Value,
    names: &HashMap<String, Vec<String>>,
) -> Result<(Model, ResolvedModel, ExplicitIds, Vec<String>), String> {
    load_document_impl(document, names, crate::model::GraphFormat::LegacyV2)
}

/// Load a document under its explicitly selected authored graph contract.
/// Use the migration API before loading legacy conditional graphs as canonical.
pub fn load_document_with_format(
    document: &Value,
    names: &HashMap<String, Vec<String>>,
    format: crate::model::GraphFormat,
) -> Result<(Model, ResolvedModel, ExplicitIds, Vec<String>), String> {
    crate::migration::validate_conditional_graph_format(document, format)?;
    load_document_impl(document, names, format)
}

fn load_document_impl(
    document: &Value,
    names: &HashMap<String, Vec<String>>,
    format: crate::model::GraphFormat,
) -> Result<(Model, ResolvedModel, ExplicitIds, Vec<String>), String> {
    let mut names = names.clone();
    names.extend(crate::lift::document_reference_name_map(document));
    let docs =
        crate::lift::split_documents(document).unwrap_or_else(|| vec![(None, document.clone())]);
    let mut model = Model::with_graph_format(format);
    let mut warnings = Vec::new();
    for (i, (_, doc)) in docs.iter().enumerate() {
        let lifted = crate::lift::from_compact_json_with_names(doc, &names)?;
        warnings.extend(lifted.errors);
        let ext = match lifted.unit.dialect {
            sysmlv2_syntax::ast::Dialect::Kerml => "kerml",
            _ => "sysml",
        };
        let text = sysmlv2_syntax::print::print_source(&lifted.unit);
        let unit = model.add_payload_source(format!("document-{}.{ext}", i + 1), &text);
        if let Some(d) = unit
            .diagnostics
            .iter()
            .find(|d| d.severity == sysmlv2_syntax::diag::Severity::Error)
        {
            return Err(format!("lifted text does not parse: {}", d.message));
        }
    }
    let mut resolved = ResolvedModel::build(&model);
    let external = |s: &str| names.get(s).and_then(|segs| segs.last().cloned());
    let mut pairing_warnings = Vec::new();
    let (pairs, mut unmatched) = paired_id_map(
        document,
        &resolved.source_compact_json(),
        &external,
        &mut pairing_warnings,
    );
    let restored =
        retain_payload_usage_flags(&mut model, &resolved, document, &pairs, &mut warnings);
    let mut explicit_ids = if restored != 0 {
        // Restore raw owned input before resolution; all future Model builds
        // follow this same path. No already-published inferred bit is patched.
        resolved = ResolvedModel::build(&model);
        pairing_warnings.clear();
        let (pairs, missing) = paired_id_map(
            document,
            &resolved.source_compact_json(),
            &external,
            &mut pairing_warnings,
        );
        unmatched = missing;
        pairs
    } else {
        pairs
    };
    warnings.extend(pairing_warnings);
    explicit_ids.retain(|derived, (given, _)| derived != given);
    if unmatched > 0 {
        warnings.push(format!(
            "{unmatched} element(s) of the document have no structural counterpart in the \
             rebuilt model; their ids are not preserved"
        ));
    }
    let map: HashMap<Uuid, Uuid> = explicit_ids.iter().map(|(d, (g, _))| (*d, *g)).collect();
    let applied = resolved.override_ids(&map);
    explicit_ids.retain(|d, _| applied.iter().any(|(a, _, _)| a == d));
    if warnings
        .iter()
        .any(|w| w.contains("cannot name reference target"))
    {
        resolved.bind_id_spelled_references_with(&mut id_reference_bindings(document));
    } else {
        resolved.bind_id_spelled_references_with(&mut HashMap::new());
    }
    Ok((model, resolved, explicit_ids, warnings))
}

#[cfg(test)]
mod pairing_tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn omitted_naming_edges_do_not_change_authored_pairing_or_root_order() {
        let mut model = Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
        let unit = model.add_source(
            "pairing.kerml",
            "class C { feature base; } class D specializes C { feature redefines base; } feature value = 1/0;",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let emitted = model_to_compact_json(&model);
        let elements = emitted.as_array().unwrap();
        let positions: HashMap<_, _> = elements
            .iter()
            .enumerate()
            .map(|(i, row)| (row["@id"].as_str().unwrap(), i))
            .collect();
        let operator = elements
            .iter()
            .find(|row| row["@type"] == "OperatorExpression")
            .unwrap();
        let membership =
            &elements[positions[operator["ownedRelationship"][0]["@id"].as_str().unwrap()]];
        let argument = positions[membership["ownedRelatedElement"][0]["@id"]
            .as_str()
            .unwrap()];
        let expected: ExplicitIds = elements
            .iter()
            .enumerate()
            .map(|(i, row)| {
                (
                    Uuid::parse_str(row["@id"].as_str().unwrap()).unwrap(),
                    (
                        Uuid::from_u128(1000 + i as u128),
                        crate::metaclass_name(row["@type"].as_str().unwrap()).unwrap(),
                    ),
                )
            })
            .collect();
        let mut document = emitted.clone();
        overlay_explicit_ids(&mut document, &expected);
        let argument_id = document[argument]["@id"].clone();
        let generated = Uuid::from_u128(900);
        let external = Uuid::from_u128(901);
        document[argument]["ownedRelationship"]
            .as_array_mut()
            .unwrap()
            .insert(0, json!({"@id": generated}));
        let elements = document.as_array_mut().unwrap();
        elements.push(json!({
            "@id": generated, "@type": "Redefinition", "isImplied": true,
            "owningRelatedElement": {"@id": argument_id},
            "redefinedFeature": {"@id": external}
        }));
        elements.insert(
            0,
            json!({
                "@id": Uuid::from_u128(902), "@type": "Namespace", "isImplied": true,
                "ownedRelationship": []
            }),
        );
        let name = |id: &str| (id == external.to_string()).then(|| "input".to_owned());
        let authored_paths = crate::ids::segment_paths(&emitted, &name).unwrap();
        assert!(
            authored_paths
                .iter()
                .flatten()
                .any(|(_, path)| path == "::D/::base")
        );
        let mut warnings = Vec::new();
        let (actual, unmatched) = paired_id_map(&document, &emitted, &name, &mut warnings);
        assert!(warnings.is_empty(), "{warnings:?}");
        assert_eq!(unmatched, 0);
        assert_eq!(actual, expected);
    }
}

#[cfg(test)]
mod payload_flag_tests {
    use super::*;
    use serde_json::json;

    fn source() -> Model {
        let mut model = Model::new();
        assert!(
            model
                .add_source("document-1.sysml", "part def P { end part p; }")
                .diagnostics
                .is_empty()
        );
        model
    }
    fn named(resolved: &ResolvedModel) -> crate::json::ElementRef {
        resolved
            .user_elements()
            .find(|&e| {
                resolved
                    .element_properties(e)
                    .get("declaredName")
                    .and_then(Value::as_str)
                    == Some("p")
            })
            .unwrap()
    }
    fn values() -> Vec<Value> {
        vec![
            json!(true),
            json!(false),
            Value::Null,
            json!("malformed"),
            json!(17),
            json!([false,{"@id":"00000000-0000-0000-0000-000000000001"}]),
            json!({"@ref":"'00000000-0000-0000-0000-000000000001'"}),
        ]
    }
    #[test]
    fn full_and_compact_owned_flags_survive_loader_rebuild_and_identity_overlays() {
        for full in [false, true] {
            for &key in crate::model::PAYLOAD_USAGE_FLAGS {
                for value in values() {
                    let original = if key == "isPortion" {
                        let mut m = Model::new();
                        assert!(
                            m.add_source("document-1.sysml", "part def P { part p; }")
                                .diagnostics
                                .is_empty()
                        );
                        m
                    } else {
                        source()
                    };
                    let mut doc = if full {
                        crate::full::model_to_full_json(&original)
                    } else {
                        model_to_compact_json(&original)
                    };
                    let row = doc
                        .as_array_mut()
                        .unwrap()
                        .iter_mut()
                        .find(|e| e["declaredName"] == "p")
                        .unwrap();
                    row[key] = value.clone();
                    let original_id = Uuid::parse_str(row["@id"].as_str().unwrap()).unwrap();
                    let (model, resolved, ids, warnings) = load_document(&doc, &HashMap::new())
                        .unwrap_or_else(|e| panic!("{full} {key} {value}: {e}"));
                    assert!(
                        warnings
                            .iter()
                            .all(|w| w.contains("no structural counterpart")),
                        "{full} {key} {value}: {warnings:?}"
                    );
                    let e = named(&resolved);
                    assert_eq!(resolved.element_id(e), original_id);
                    assert_eq!(
                        resolved.element_properties(e).get(key),
                        Some(&value),
                        "{full} {key}"
                    );
                    let mut rebuilt = ResolvedModel::build(&model);
                    let e = named(&rebuilt);
                    assert_eq!(rebuilt.element_properties(e).get(key), Some(&value));
                    let before = rebuilt.element_id(e);
                    rebuilt.override_ids(&HashMap::from([(before, Uuid::from_u128(93))]));
                    rebuilt.bind_id_spelled_references();
                    assert_eq!(rebuilt.element_properties(e).get(key), Some(&value));
                    let mut emitted = model_to_compact_json(&model);
                    overlay_explicit_ids(&mut emitted, &ids);
                    assert_eq!(
                        emitted
                            .as_array()
                            .unwrap()
                            .iter()
                            .find(|e| e["declaredName"] == "p")
                            .unwrap()
                            .get(key),
                        Some(&value)
                    );
                }
            }
        }
    }
    #[test]
    fn malformed_boolean_reference_shapes_are_literal_across_all_overlay_paths() {
        let old = Uuid::from_u128(1);
        let new = Uuid::from_u128(2);
        let mut p = crate::properties::Properties::new();
        let value = json!({"@id":old,"nested":[{"@ref":format!("'{old}'")}]});
        p.insert_payload_flag("isConstant", value.clone());
        p.insert("target", json!({"@id":old}));
        for atom in p.values_mut() {
            atom.remap(&HashMap::from([(old, new)]));
        }
        let restored: crate::properties::Properties =
            crate::cache_codec::decode(&crate::cache_codec::encode(&p).unwrap()).unwrap();
        assert_eq!(restored.get("isConstant").unwrap().to_json(), value);
        assert_eq!(
            restored.get("target").unwrap().to_json(),
            json!({"@id":new})
        );
        for flag in [
            json!({"@id":old}),
            json!({"@ref":format!("'{old}'")}),
            value,
        ] {
            let doc =
                json!([{"@id":old,"@type":"PartUsage","isConstant":flag,"target":{"@id":old}}]);
            let hints = id_reference_bindings(&doc);
            assert!(!hints.contains_key(&(old, "isConstant".into())));
            assert_eq!(hints.get(&(old, "target".into())), Some(&old));
            let ids = HashMap::from([(old, (new, "PartUsage"))]);
            let mut legacy = doc.clone();
            overlay_explicit_ids(&mut legacy, &ids);
            assert_eq!(legacy[0]["isConstant"], flag);
            assert_eq!(legacy[0]["target"], json!({"@id":new}));
            let mut strict = doc;
            overlay_payload_ids(
                &mut strict,
                &ids,
                &HashMap::from([((new, "isConstant".into()), new)]),
            );
            assert_eq!(strict[0]["isConstant"], flag);
        }
    }
    #[test]
    fn identity_equal_pairing_retains_flags_without_inventing_an_overlay() {
        let mut doc = model_to_compact_json(&source());
        doc.as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|e| e["declaredName"] == "p")
            .unwrap()["isConstant"] = Value::Null;
        let (mut model, resolved, ids, warnings) = load_document(&doc, &HashMap::new()).unwrap();
        assert!(warnings.is_empty());
        assert!(ids.is_empty());
        assert_eq!(
            resolved.element_properties(named(&resolved))["isConstant"],
            Value::Null
        );
        // Adding a library later changes build ordering, not original unit ordinals.
        model.add_library_source("late.kerml", "package Library { class T; }");
        let reordered = ResolvedModel::build(&model);
        assert_eq!(
            reordered.element_properties(named(&reordered))["isConstant"],
            Value::Null
        );
        model.add_source("ordinary.sysml", "part def Q { end part p; }");
        assert!(model.payload_source_flags(1).is_none());
        assert!(model.payload_source_flags(2).is_none());
        let rebuilt = ResolvedModel::build(&model);
        let p: Vec<_> = rebuilt
            .user_elements()
            .filter(|&e| {
                rebuilt
                    .element_properties(e)
                    .get("declaredName")
                    .and_then(Value::as_str)
                    == Some("p")
            })
            .collect();
        assert_eq!(p.len(), 2);
        assert_eq!(rebuilt.element_properties(p[0])["isConstant"], Value::Null);
        assert_eq!(rebuilt.element_properties(p[1])["isConstant"], json!(false));
    }
    #[test]
    fn duplicate_payload_identity_cannot_choose_owned_flags() {
        let mut doc = model_to_compact_json(&source());
        let mut row = doc
            .as_array()
            .unwrap()
            .iter()
            .find(|e| e["declaredName"] == "p")
            .unwrap()
            .clone();
        row["isConstant"] = json!("ambiguous");
        doc.as_array_mut().unwrap().push(row);
        let (model, _, _, _) = load_document(&doc, &HashMap::new()).unwrap();
        assert!(model.payload_source_flags(0).unwrap().is_empty());
    }
    #[test]
    fn payload_flags_are_reapplied_before_fresh_recorded_prepared_and_decoded_builds() {
        let mut library = Model::new();
        library.add_library_source(
            "lib.kerml",
            "package Base { classifier Anything; feature things : Anything; }",
        );
        let prepared =
            std::sync::Arc::new(crate::prepared::PreparedLibrary::build(&library).unwrap());
        let decoded = std::sync::Arc::new(
            crate::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(7).unwrap(), 7)
                .unwrap(),
        );
        let value = json!({"@id":"00000000-0000-0000-0000-000000000001"});
        for mode in 0..4 {
            let mut model = Model::new();
            if mode < 2 {
                model.add_library_source(
                    "lib.kerml",
                    "package Base { classifier Anything; feature things : Anything; }",
                );
            } else {
                model
                    .install_prepared(if mode == 2 {
                        prepared.clone()
                    } else {
                        decoded.clone()
                    })
                    .unwrap();
            }
            let unit = model.unit_count();
            model.add_payload_source("payload.sysml", "part def P { end part p; }");
            let resolved = ResolvedModel::build(&model);
            let e = named(&resolved);
            let (_, path) = resolved.payload_owned_flag_anchor(e).unwrap();
            let mut flags = crate::properties::Properties::new();
            flags.insert_payload_flag("isConstant", value.clone());
            model.retain_payload_flags(
                unit,
                path,
                crate::model::PayloadOwnedFlags {
                    metaclass: "PartUsage",
                    flags,
                },
            );
            if mode == 1 {
                model.record_library_cache();
            }
            let restored = ResolvedModel::build(&model);
            assert_eq!(
                restored.element_properties(named(&restored))["isConstant"],
                value
            );
            if mode == 1 {
                let cache = model.take_recorded_library_cache().unwrap();
                model.set_library_cache(cache);
            }
            let again = ResolvedModel::build(&model);
            assert_eq!(again.element_properties(named(&again))["isConstant"], value);
            assert!(again.payload_owned_flag_anchor(named(&again)).is_some());
        }
    }
}
