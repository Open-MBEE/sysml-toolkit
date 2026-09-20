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
    use crate::ids::segment_paths;
    let emitted = model_to_compact_json(model);
    let (doc_paths, model_paths) = match (
        segment_paths(document, external),
        segment_paths(&emitted, external),
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
    let model_paths = ordinal_paths(model_paths, &emitted);
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
    let mut by_path: HashMap<(usize, String), (Uuid, String)> = HashMap::new();
    for (i, path) in model_paths.into_iter().enumerate() {
        if let (Some(path), Some(id)) = (path, id_at(&emitted, i)) {
            by_path.insert(path, (id, ty_at(&emitted, i)));
        }
    }
    // Elements the lift deliberately drops are not "unpreserved": implied
    // relationships and unresolved-reference recovery annotations (with
    // their memberships) of a full-form document.
    let recovery: std::collections::HashSet<String> = document
        .as_array()
        .map(|a| {
            let mut set = std::collections::HashSet::new();
            for e in a {
                if e["language"] == crate::full::UNRESOLVED_REP_LANGUAGE {
                    if let Some(id) = e["@id"].as_str() {
                        set.insert(id.to_string());
                    }
                    if let Some(m) = e["owningRelationship"]["@id"].as_str() {
                        set.insert(m.to_string());
                    }
                }
            }
            set
        })
        .unwrap_or_default();
    let mut map = HashMap::new();
    let mut unmatched = 0usize;
    for (i, path) in doc_paths.into_iter().enumerate() {
        let Some(given) = id_at(document, i) else {
            continue;
        };
        let el = &document[i];
        if el["isImplied"] == true || recovery.contains(given.to_string().as_str()) {
            continue;
        }
        let doc_ty = ty_at(document, i);
        match path.and_then(|p| by_path.get(&p)) {
            // Positional pairing is only trusted between elements of the
            // same metaclass (a document that lists a feature's typing
            // and value in the other order must not swap their ids). The
            // one sanctioned change is the chain-target membership this
            // toolkit now spells as an OwningMembership.
            Some((derived, model_ty))
                if *model_ty == doc_ty
                    || (doc_ty == "Membership" && model_ty == "OwningMembership") =>
            {
                if *derived != given {
                    let ty = crate::metaclass_name(model_ty).unwrap_or("");
                    map.insert(*derived, (given, ty));
                }
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
    let text_map: HashMap<String, String> = explicit_ids
        .iter()
        .map(|(d, (g, _))| (d.to_string(), g.to_string()))
        .collect();
    fn remap(v: &mut Value, map: &HashMap<String, String>) {
        match v {
            Value::Object(o) => {
                for (k, x) in o.iter_mut() {
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
                o.values_mut().for_each(bind);
            }
            Value::Array(a) => a.iter_mut().for_each(bind),
            _ => {}
        }
    }
    bind(value);
}

/// Load a compact (or full) interchange document into a fresh model
/// with no library: the lift names references through `names`
/// (id text → qualified-name segments, as [`crate::json::library_name_map`]
/// produces), the text is rebuilt, and the document's ids are kept as
/// explicit ids. Returns the model, its resolved form with the overlay
/// applied, the overlay, and the lift's non-fatal problems.
pub fn load_document(
    document: &Value,
    names: &HashMap<String, Vec<String>>,
) -> Result<(Model, ResolvedModel, ExplicitIds, Vec<String>), String> {
    let mut names = names.clone();
    names.extend(crate::lift::document_reference_name_map(document));
    let docs =
        crate::lift::split_documents(document).unwrap_or_else(|| vec![(None, document.clone())]);
    let mut model = Model::new();
    let mut warnings = Vec::new();
    for (i, (_, doc)) in docs.iter().enumerate() {
        let lifted = crate::lift::from_compact_json_with_names(doc, &names)?;
        warnings.extend(lifted.errors);
        let ext = match lifted.unit.dialect {
            sysmlv2_syntax::ast::Dialect::Kerml => "kerml",
            _ => "sysml",
        };
        let text = sysmlv2_syntax::print::print_source(&lifted.unit);
        let unit = model.add_source(format!("document-{}.{ext}", i + 1), &text);
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
    let (mut explicit_ids, unmatched) = explicit_id_map(document, &model, &external, &mut warnings);
    if unmatched > 0 {
        warnings.push(format!(
            "{unmatched} element(s) of the document have no structural counterpart in the \
             rebuilt model; their ids are not preserved"
        ));
    }
    let map: HashMap<Uuid, Uuid> = explicit_ids.iter().map(|(d, (g, _))| (*d, *g)).collect();
    let applied = resolved.override_ids(&map);
    explicit_ids.retain(|d, _| applied.iter().any(|(a, _, _)| a == d));
    resolved.bind_id_spelled_references();
    Ok((model, resolved, explicit_ids, warnings))
}
