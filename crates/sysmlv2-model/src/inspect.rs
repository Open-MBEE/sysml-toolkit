//! The resolved element graph as an ownership tree, for inspection.
//!
//! The abstract syntax is a graph: every element but a document root is
//! owned through a relationship (`Element::owningRelationship`), every
//! relationship is carried by its owner (`Relationship::owningRelatedElement`)
//! and owns the elements written under it
//! (`Relationship::ownedRelatedElement`), and the other ends of a
//! relationship — a typing's `type`, a subclassification's `superclassifier`, an
//! import's `importedNamespace`, an alias membership's `memberElement` —
//! point anywhere, library elements included. [`tree`] reads that graph as
//! a tree: ownership makes the hierarchy, element and relationship alternate
//! level by level, and every other end is a reference, spelled by its
//! target's qualified name and metaclass and never expanded. The walk
//! recurses through `ownedRelatedElement` alone, so it cannot cycle, and a
//! library element is reached only as a reference or as the chosen root.
//!
//! The tree is data ([`TreeNode`], serializable as JSON) with one text
//! rendering ([`render`]) beside it, so a command line, a binding and a host
//! read one walk. The implied relationships (the library specializations of
//! every kind, the positional redefinitions) and the ids are opt-in: the
//! default view is what the text declares, resolved.

use crate::json::{ElementRef, ResolvedModel};
use serde::Serialize;
use serde_json::{Map, Value};

/// What [`tree`] shows.
#[derive(Clone, Debug)]
pub struct TreeOptions {
    /// Ownership levels below the root to expand: `Some(0)` shows the
    /// root alone, `Some(1)` its relationships and their elements but
    /// nothing those own, and so on; `None` expands everything.
    pub depth: Option<usize>,
    /// Spell the non-owning ends of each relationship (`type`,
    /// `superclassifier`, `importedNamespace`, …) as references.
    pub references: bool,
    /// Include the implied relationships: the library specializations
    /// of each kind, a variant's specialization of its variation, the
    /// positional redefinitions, and the elements they generate. They
    /// are materialized for the whole model on first use.
    pub implied: bool,
    /// Carry the interchange id of every element, relationship and
    /// reference target.
    pub ids: bool,
}

impl Default for TreeOptions {
    fn default() -> Self {
        Self {
            depth: None,
            references: true,
            implied: false,
            ids: false,
        }
    }
}

/// An element of the tree: its identity and the relationships it owns.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeNode {
    /// The exact metaclass (`PartDefinition`, `AttributeUsage`, …).
    pub metaclass: &'static str,
    /// The effective name (`Element::name`), else the name lookup finds
    /// the element by (a redefined feature's name as written).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// `Element::qualifiedName`, when every ancestor is named.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_name: Option<String>,
    /// `Element::elementId`, with [`TreeOptions::ids`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// Whether the element was read from a library unit.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub library: bool,
    /// The declaration site, for an element that has one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub site: Option<Site>,
    /// Reference-typed properties the element itself carries, in
    /// property-name order (rare: ends live on relationships).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub references: Vec<TreeReference>,
    /// The relationships the element owns, the explicit ones in
    /// declaration order, then the implied ones when asked for.
    pub relationships: Vec<TreeRelationship>,
    /// The element owns relationships the depth limit left out.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub truncated: bool,
}

/// A relationship an element owns: its kind, its other ends as
/// references, and the elements it owns in turn.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeRelationship {
    /// The exact metaclass (`FeatureMembership`, `FeatureTyping`, …).
    pub metaclass: &'static str,
    /// `Element::elementId`, with [`TreeOptions::ids`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// An implied relationship (never written; see
    /// [`TreeOptions::implied`]).
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub implied: bool,
    /// The ends that are not the carrier and not an owned element, in
    /// property-name order: a typing's `type`, a specialization's
    /// `superclassifier`, an import's `importedNamespace`, …
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub references: Vec<TreeReference>,
    /// `Relationship::ownedRelatedElement`: the elements written under
    /// the relationship, in order.
    pub children: Vec<TreeNode>,
}

/// One reference-typed property and the element it points at.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeReference {
    /// The property, as the compact interchange form spells it.
    pub property: String,
    pub target: TreeTarget,
}

/// The target of a reference: an element of the model, an element
/// outside it known by id alone, or a spelling that did not resolve.
#[derive(Clone, Debug, Default, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeTarget {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metaclass: Option<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_name: Option<String>,
    /// The element's id — always for a target outside the model, else
    /// with [`TreeOptions::ids`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// The target was read from a library unit.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub library: bool,
    /// The target is outside the model (an unloaded library, a foreign
    /// payload): known by its id alone.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub outside: bool,
    /// The written spelling of a reference that did not resolve.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub spelling: Option<String>,
}

/// Where an element is declared: unit name, 1-based line and column.
#[derive(Clone, Debug, Serialize)]
pub struct Site {
    pub file: String,
    pub line: u32,
    pub col: u32,
}

/// The keys of the compact form that spell structure, not ends: the
/// walk follows them itself.
const STRUCTURE: &[&str] = &[
    "@id",
    "@type",
    "elementId",
    "owningRelationship",
    "owningRelatedElement",
    "ownedRelationship",
    "ownedRelatedElement",
];

/// The ownership tree under `root`, or under every top-level element of
/// the user units when `root` is `None`: the owned members of each
/// unit's root namespace, in declaration order.
pub fn tree(
    r: &mut ResolvedModel,
    root: Option<ElementRef>,
    options: &TreeOptions,
) -> Vec<TreeNode> {
    let roots = match root {
        Some(e) => vec![e],
        None => {
            let all: Vec<ElementRef> = r.user_elements().collect();
            let mut tops = Vec::new();
            for e in all {
                if r.element_type(e) == "Namespace" && r.owner(e).is_none() {
                    tops.extend(r.owned_members(e));
                }
            }
            tops
        }
    };
    roots
        .into_iter()
        .map(|e| node(r, e, options.depth, options))
        .collect()
}

fn node(
    r: &mut ResolvedModel,
    e: ElementRef,
    depth: Option<usize>,
    options: &TreeOptions,
) -> TreeNode {
    let mut relationships = r.owned_relationships(e);
    if options.implied {
        // A generated element (an implied result parameter, a binding
        // connector) owns its relationships through the implied view
        // alone, where the explicit list already names them: each row
        // once.
        for rel in r.implied_relationships(e) {
            if !relationships.contains(&rel) {
                relationships.push(rel);
            }
        }
    }
    let truncated = depth == Some(0) && !relationships.is_empty();
    let relationships = if truncated {
        Vec::new()
    } else {
        let below = depth.map(|d| d.saturating_sub(1));
        relationships
            .into_iter()
            .map(|rel| relationship(r, rel, e, below, options))
            .collect()
    };
    TreeNode {
        metaclass: r.element_type(e),
        name: r
            .element_effective_name(e)
            .or_else(|| r.element_lookup_name(e)),
        qualified_name: r.element_qualified_name(e),
        id: options.ids.then(|| r.element_id(e).to_string()),
        library: r.is_library_element(e),
        site: r.declaration_position(e).map(|(file, line, col)| Site {
            file: file.to_string(),
            line,
            col,
        }),
        references: if options.references {
            references(r, e, None, &[], options)
        } else {
            Vec::new()
        },
        relationships,
        truncated,
    }
}

fn relationship(
    r: &mut ResolvedModel,
    rel: ElementRef,
    carrier: ElementRef,
    depth: Option<usize>,
    options: &TreeOptions,
) -> TreeRelationship {
    let owned = r.owned_related_elements(rel);
    TreeRelationship {
        metaclass: r.element_type(rel),
        id: options.ids.then(|| r.element_id(rel).to_string()),
        implied: options.implied && r.is_implied(rel),
        references: if options.references {
            references(r, rel, Some(carrier), &owned, options)
        } else {
            Vec::new()
        },
        children: owned
            .into_iter()
            .map(|child| node(r, child, depth, options))
            .collect(),
    }
}

/// The reference-typed properties of `e` as the compact form spells
/// them, in property-name order, leaving out the structural keys and
/// — for a relationship — the ends that are its carrier or an element
/// it owns, which the tree already shows as its parent and children.
fn references(
    r: &mut ResolvedModel,
    e: ElementRef,
    carrier: Option<ElementRef>,
    owned: &[ElementRef],
    options: &TreeOptions,
) -> Vec<TreeReference> {
    let props: Map<String, Value> = r.element_properties(e);
    let mut out = Vec::new();
    for (key, value) in &props {
        if STRUCTURE.contains(&key.as_str()) {
            continue;
        }
        let values: Vec<&Value> = match value {
            Value::Array(items) => items.iter().collect(),
            other => vec![other],
        };
        for value in values {
            let Value::Object(object) = value else {
                continue;
            };
            let target = if let Some(Value::String(id)) = object.get("@id") {
                match r.element_by_id(id) {
                    Some(t) if Some(t) == carrier || owned.contains(&t) => continue,
                    Some(t) => TreeTarget {
                        metaclass: Some(r.element_type(t)),
                        name: r
                            .element_effective_name(t)
                            .or_else(|| r.element_lookup_name(t)),
                        qualified_name: r.element_qualified_name(t),
                        id: options.ids.then(|| id.clone()),
                        library: r.is_library_element(t),
                        ..TreeTarget::default()
                    },
                    None => TreeTarget {
                        id: Some(id.clone()),
                        outside: true,
                        ..TreeTarget::default()
                    },
                }
            } else if let Some(Value::String(spelling)) = object.get("@ref") {
                TreeTarget {
                    spelling: Some(spelling.clone()),
                    ..TreeTarget::default()
                }
            } else {
                continue;
            };
            out.push(TreeReference {
                property: key.clone(),
                target,
            });
        }
    }
    out
}

/// The tree as text, one line per element, relationship and reference,
/// drawn with box-drawing branches:
///
/// ```text
/// Demo::Vehicle [PartDefinition]
/// └─ FeatureMembership
///    └─ mass [AttributeUsage]
///       └─ FeatureTyping
///          └─ type → ScalarValues::Real [DataType] [library]
/// ```
///
/// A root is labelled by its qualified name, an owned element by its
/// name; `…` after a label marks relationships the depth limit left
/// out; an implied relationship says so; a reference whose target is
/// outside the model or did not resolve says which.
pub fn render(nodes: &[TreeNode]) -> String {
    let mut out = String::new();
    for node in nodes {
        out.push_str(&node_label(node, true));
        out.push('\n');
        render_node(node, "", &mut out);
    }
    out
}

fn render_node(node: &TreeNode, prefix: &str, out: &mut String) {
    let total = node.references.len() + node.relationships.len();
    let mut index = 0;
    let mut branch = |out: &mut String, line: &str| -> String {
        index += 1;
        let last = index == total;
        out.push_str(prefix);
        out.push_str(if last { "└─ " } else { "├─ " });
        out.push_str(line);
        out.push('\n');
        format!("{prefix}{}", if last { "   " } else { "│  " })
    };
    for reference in &node.references {
        branch(out, &reference_label(reference));
    }
    for relationship in &node.relationships {
        let below = branch(out, &relationship_label(relationship));
        render_relationship(relationship, &below, out);
    }
}

fn render_relationship(relationship: &TreeRelationship, prefix: &str, out: &mut String) {
    let total = relationship.references.len() + relationship.children.len();
    let mut index = 0;
    let mut branch = |out: &mut String, line: &str| -> String {
        index += 1;
        let last = index == total;
        out.push_str(prefix);
        out.push_str(if last { "└─ " } else { "├─ " });
        out.push_str(line);
        out.push('\n');
        format!("{prefix}{}", if last { "   " } else { "│  " })
    };
    for reference in &relationship.references {
        branch(out, &reference_label(reference));
    }
    for child in &relationship.children {
        let below = branch(out, &node_label(child, false));
        render_node(child, &below, out);
    }
}

fn node_label(node: &TreeNode, qualified: bool) -> String {
    let name = if qualified {
        node.qualified_name.as_deref().or(node.name.as_deref())
    } else {
        node.name.as_deref()
    };
    let mut label = format!("{} [{}]", name.unwrap_or("(anonymous)"), node.metaclass);
    if node.library {
        label.push_str(" [library]");
    }
    if let Some(id) = &node.id {
        label.push(' ');
        label.push_str(id);
    }
    if node.truncated {
        label.push_str(" …");
    }
    label
}

fn relationship_label(relationship: &TreeRelationship) -> String {
    let mut label = relationship.metaclass.to_string();
    if relationship.implied {
        label.push_str(" (implied)");
    }
    if let Some(id) = &relationship.id {
        label.push(' ');
        label.push_str(id);
    }
    label
}

fn reference_label(reference: &TreeReference) -> String {
    let t = &reference.target;
    let mut label = format!("{} → ", reference.property);
    if let Some(spelling) = &t.spelling {
        label.push_str(spelling);
        label.push_str(" (unresolved)");
        return label;
    }
    if t.outside {
        label.push_str(t.id.as_deref().unwrap_or("?"));
        label.push_str(" (outside the model)");
        return label;
    }
    label.push_str(
        t.qualified_name
            .as_deref()
            .or(t.name.as_deref())
            .unwrap_or("(anonymous)"),
    );
    if let Some(metaclass) = t.metaclass {
        label.push_str(&format!(" [{metaclass}]"));
    }
    if t.library {
        label.push_str(" [library]");
    }
    if let Some(id) = &t.id {
        label.push(' ');
        label.push_str(id);
    }
    label
}

#[cfg(test)]
mod tests;
