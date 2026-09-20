//! The template rendering backend (semantic mode): evaluate
//! an imported component template — the `Root` a `rendering def` owns —
//! over a `view` usage's exposed model slice, and return the resulting
//! DOM tree as values. Nothing is written into the model: inputs bind in
//! the evaluator's environment, blocks iterate and test through the
//! translated `kerml` expressions beside their typed source, and
//! elements, attributes and text project exactly as the construction
//! layer would present them.

use crate::eval::Value;
use crate::json::{ElementRef, ResolvedModel};
use sysmlv2_syntax::ast::{Name, QualifiedName};
use sysmlv2_syntax::parser::parse_expression;
use sysmlv2_syntax::span::Span;

/// One rendered node.
#[derive(Clone, Debug, PartialEq)]
pub enum RenderNode {
    Element {
        name: String,
        namespace: Option<String>,
        /// Reified attributes (`localName`, rendered value), in order.
        attributes: Vec<(String, String)>,
        /// Reflected properties bound on the usage (feature name, value,
        /// whether the evaluated value is Boolean).
        properties: Vec<(String, String, bool)>,
        children: Vec<RenderNode>,
    },
    Text(String),
    Comment(String),
    /// Raw markup (`{@html …}`), not escaped.
    Raw(String),
    /// A component occurrence result, reserved for a project-aware resolver.
    Component {
        name: String,
        children: Vec<RenderNode>,
    },
    /// A block or expression that could not be evaluated (no translation,
    /// or an evaluation error): rendering degrades to a marker so the
    /// rest of the view still renders.
    Error(String),
}

/// Content-attribute names for the reflected properties whose IDL name
/// differs from the attribute; every other property lowercases.
const PROPERTY_ATTRIBUTES: &[(&str, &str)] = &[
    ("className", "class"),
    ("htmlFor", "for"),
    ("httpEquiv", "http-equiv"),
    ("acceptCharset", "accept-charset"),
    ("defaultValue", "value"),
    ("defaultChecked", "checked"),
    ("defaultSelected", "selected"),
    ("valueAsNumber", "value"),
];

/// HTML boolean content attributes serialize by presence/absence. Boolean
/// IDL properties not in this list (for example `draggable`) are enumerated
/// attributes and retain their textual true/false value.
const BOOLEAN_ATTRIBUTES: &[&str] = &[
    "allowfullscreen",
    "async",
    "autofocus",
    "autoplay",
    "checked",
    "controls",
    "default",
    "defer",
    "disabled",
    "formnovalidate",
    "hidden",
    "inert",
    "ismap",
    "itemscope",
    "loop",
    "multiple",
    "muted",
    "nomodule",
    "novalidate",
    "open",
    "playsinline",
    "readonly",
    "required",
    "reversed",
    "selected",
];

fn escape_html(s: &str, out: &mut String) {
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
}

impl RenderNode {
    pub fn to_json(&self) -> serde_json::Value {
        match self {
            RenderNode::Element {
                name,
                namespace,
                attributes,
                properties,
                children,
            } => {
                let mut o = serde_json::Map::new();
                o.insert("kind".into(), "element".into());
                o.insert("name".into(), name.as_str().into());
                if let Some(ns) = namespace {
                    o.insert("namespace".into(), ns.as_str().into());
                }
                o.insert(
                    "attributes".into(),
                    serde_json::Value::Object(
                        attributes
                            .iter()
                            .map(|(k, v)| (k.clone(), v.as_str().into()))
                            .collect(),
                    ),
                );
                o.insert(
                    "properties".into(),
                    serde_json::Value::Object(
                        properties
                            .iter()
                            .map(|(k, v, _)| (k.clone(), v.as_str().into()))
                            .collect(),
                    ),
                );
                o.insert(
                    "children".into(),
                    children.iter().map(RenderNode::to_json).collect(),
                );
                serde_json::Value::Object(o)
            }
            RenderNode::Text(t) => serde_json::json!({"kind": "text", "data": t}),
            RenderNode::Comment(t) => serde_json::json!({"kind": "comment", "data": t}),
            RenderNode::Raw(t) => serde_json::json!({"kind": "raw", "html": t}),
            RenderNode::Component { name, children } => serde_json::json!({
                "kind": "component", "name": name,
                "children": children.iter().map(RenderNode::to_json).collect::<Vec<_>>(),
            }),
            RenderNode::Error(message) => serde_json::json!({"kind": "error", "message": message}),
        }
    }

    pub fn to_html(&self, out: &mut String) {
        match self {
            RenderNode::Element {
                name,
                attributes,
                properties,
                children,
                ..
            } => {
                out.push('<');
                out.push_str(name);
                for (k, v, boolean) in properties {
                    let attr = PROPERTY_ATTRIBUTES
                        .iter()
                        .find(|(p, _)| p == k)
                        .map(|(_, a)| a.to_string())
                        .unwrap_or_else(|| k.to_lowercase());
                    let boolean_attribute = *boolean && BOOLEAN_ATTRIBUTES.contains(&attr.as_str());
                    if boolean_attribute && v == "true" {
                        out.push(' ');
                        out.push_str(&attr);
                        continue;
                    }
                    if boolean_attribute && v == "false" {
                        continue;
                    }
                    out.push(' ');
                    out.push_str(&attr);
                    out.push_str("=\"");
                    escape_html(v, out);
                    out.push('"');
                }
                for (k, v) in attributes {
                    out.push(' ');
                    out.push_str(k);
                    out.push_str("=\"");
                    escape_html(v, out);
                    out.push('"');
                }
                out.push('>');
                for c in children {
                    c.to_html(out);
                }
                if !matches!(
                    name.as_str(),
                    "area"
                        | "base"
                        | "br"
                        | "col"
                        | "embed"
                        | "hr"
                        | "img"
                        | "input"
                        | "link"
                        | "meta"
                        | "source"
                        | "track"
                        | "wbr"
                ) {
                    out.push_str("</");
                    out.push_str(name);
                    out.push('>');
                }
            }
            RenderNode::Text(t) => escape_html(t, out),
            RenderNode::Comment(t) => {
                out.push_str("<!--");
                out.push_str(t);
                out.push_str("-->");
            }
            RenderNode::Raw(t) => out.push_str(t),
            RenderNode::Component { children, .. } => {
                for c in children {
                    c.to_html(out);
                }
            }
            RenderNode::Error(message) => {
                out.push_str("<!-- error: ");
                out.push_str(&message.replace("--", "- -"));
                out.push_str(" -->");
            }
        }
    }
}

/// Serialize rendered nodes as HTML.
pub fn to_html(nodes: &[RenderNode]) -> String {
    let mut out = String::new();
    for n in nodes {
        n.to_html(&mut out);
    }
    out
}

fn qn(name: &str) -> QualifiedName {
    QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: name.to_string(),
            span: Span::default(),
        }],
        span: Span::default(),
    }
}

/// The template kinds the backend distinguishes, resolved once.
struct Kinds {
    node: ElementRef,
    attr: ElementRef,
    root: ElementRef,
    element: ElementRef,
    /// A plain DOM element (`Web::HTML::Elements::*`): renders like a template element.
    dom_element: ElementRef,
    component: ElementRef,
    text: ElementRef,
    comment: ElementRef,
    expression_tag: ElementRef,
    html_tag: ElementRef,
    each: ElementRef,
    if_block: ElementRef,
    await_block: ElementRef,
    snippet_block: ElementRef,
    render_tag: ElementRef,
    attribute: ElementRef,
}

/// Is a bound value "true" for an `{#if}` test?
fn truthy(v: &Value) -> bool {
    match v {
        Value::Boolean(b) => *b,
        Value::Integer(i) => *i != 0,
        Value::Rational(r) => !r.is_zero(),
        Value::Real(f) => *f != 0.0,
        Value::String(s) => !s.is_empty(),
        Value::Sequence(items) => !items.is_empty(),
        Value::Indeterminate => false,
        _ => true,
    }
}

impl ResolvedModel {
    fn kinds(&mut self) -> Result<Kinds, String> {
        let mut get = |q: &str| {
            self.resolve_qualified(q).ok_or_else(|| {
                format!("{q} is not loaded (the Web and Template libraries are required)")
            })
        };
        Ok(Kinds {
            node: get("Web::DOM::Node")?,
            attr: get("Web::DOM::Attr")?,
            root: get("Template::Root")?,
            element: get("Template::Element")?,
            dom_element: get("Web::DOM::Element")?,
            component: get("Template::Component")?,
            text: get("Web::DOM::Text")?,
            comment: get("Web::DOM::Comment")?,
            expression_tag: get("Template::ExpressionTag")?,
            html_tag: get("Template::HtmlTag")?,
            each: get("Template::EachBlock")?,
            if_block: get("Template::IfBlock")?,
            await_block: get("Svelte::AwaitBlock")?,
            snippet_block: get("Svelte::SnippetBlock")?,
            render_tag: get("Svelte::RenderTag")?,
            attribute: get("Template::Attribute")?,
        })
    }

    /// A bound scalar feature of `e` reached by name, as text.
    fn bound_text(&mut self, e: ElementRef, name: &str) -> Option<String> {
        match self.evaluate_chain(e, &[&qn(name)]) {
            Ok(Value::String(s)) => Some(s),
            Ok(
                v @ (Value::Integer(_) | Value::Rational(_) | Value::Real(_) | Value::Boolean(_)),
            ) => Some(self.render_value(&v)),
            _ => None,
        }
    }

    /// Evaluate translated KerML text over `env`, from the root scope.
    fn eval_kerml(&mut self, text: &str, env: &[(String, Value)]) -> Result<Value, String> {
        let parsed = parse_expression(text);
        let expr = parsed.expr.ok_or_else(|| {
            format!(
                "kerml `{text}`: {}",
                parsed
                    .diagnostics
                    .first()
                    .map(|d| d.message.clone())
                    .unwrap_or_default()
            )
        })?;
        let scope = self.root_scope();
        crate::eval::evaluate_query_with_env(&mut self.b, scope.0, &expr, env.to_vec())
            .map_err(|e| format!("kerml `{text}`: {e}"))
    }

    /// The text a value renders as: strings verbatim, elements by name.
    fn value_text(&self, v: &Value) -> String {
        match v {
            Value::String(s) => s.clone(),
            Value::Sequence(items) => items
                .iter()
                .map(|i| self.value_text(i))
                .collect::<Vec<_>>()
                .join(", "),
            other => self.render_value(other),
        }
    }

    /// A part with no typing of its own (only redefinitions): a slot.
    fn is_slot(&mut self, e: ElementRef) -> bool {
        let specs = self.b.explicit_specialization_elems(e.0);
        !specs.is_empty() && specs.iter().all(|(k, _)| *k == "Redefinition")
    }

    /// The named slot of `e` (`part <n> :>> body { … }`): a slot's name
    /// is the feature it redefines, not its own short name.
    fn slot(&mut self, e: ElementRef, name: &str) -> Option<ElementRef> {
        let members = self.owned_members(e);
        for m in members {
            if self.element_type(m) != "PartUsage" || !self.is_slot(m) {
                continue;
            }
            let targets = self.b.redefinition_target_elems(m.0);
            if targets
                .iter()
                .any(|&t| self.b.id_name(t).as_deref() == Some(name))
            {
                return Some(m);
            }
        }
        None
    }

    /// Render the tree a `view` usage presents: its exposed elements bind
    /// the rendering's inputs. Returns the rendered nodes of the root.
    ///
    /// Rendering errors are messages rather than a type throughout this
    /// module: each one names a specific thing the view's own text is
    /// missing or has wrong, for a reader to act on, and every caller
    /// passes it straight to one — a command-line message, a rejected
    /// call in a host binding.
    pub fn render_view(&mut self, view: ElementRef) -> Result<Vec<RenderNode>, String> {
        // Annotations (documentation, comments, textual representations)
        // are members too, but never a template's subject matter.
        let exposed: Vec<Value> = self
            .view_exposed_elements(view)
            .into_iter()
            .filter(|&e| {
                !matches!(
                    self.element_type(e),
                    "Documentation" | "Comment" | "TextualRepresentation"
                )
            })
            .map(Value::Element)
            .collect();
        let root = self.view_template_root(view)?;
        self.render_root(root, &Value::Sequence(exposed))
    }

    /// The `Root` usage of the rendering a view (or its definition) names.
    fn view_template_root(&mut self, view: ElementRef) -> Result<ElementRef, String> {
        let kinds = self.kinds()?;
        // The rendering usage: on the view usage itself, or on its definitions.
        let mut candidates = vec![view];
        candidates.extend(self.typings(view));
        let mut renderings = Vec::new();
        for c in candidates {
            let members = self.owned_members(c);
            for m in members {
                if self.element_type(m) == "RenderingUsage" {
                    renderings.push(m);
                }
            }
        }
        if renderings.is_empty() {
            return Err("the view names no rendering usage".into());
        }
        // A rendering usage (the declared one, or the `render` reference's
        // target) is typed by the rendering definition owning the root — or,
        // for a rendering written in plain DOM parts without a template
        // root, the rendering definition itself is the root: its node parts
        // render directly.
        let mut plain_root = None;
        for r in renderings {
            let mut owners = vec![r];
            owners.extend(self.typings(r));
            for o in owners {
                let members = self.owned_members(o);
                for m in members {
                    if self.element_type(m) == "PartUsage" && self.conforms(m, kinds.root) {
                        return Ok(m);
                    }
                    if plain_root.is_none()
                        && self.element_type(m) == "PartUsage"
                        && self.conforms(m, kinds.node)
                        && !self.conforms(m, kinds.attr)
                    {
                        plain_root = Some(o);
                    }
                }
            }
        }
        plain_root.ok_or_else(|| "the rendering owns no template root and no node parts".into())
    }

    /// Render a template root over `exposed` bound to its declared inputs
    /// (the first input, or `exposed` itself when the environment names
    /// none).
    pub fn render_root(
        &mut self,
        root: ElementRef,
        exposed: &Value,
    ) -> Result<Vec<RenderNode>, String> {
        let kinds = self.kinds()?;
        let mut env: Vec<(String, Value)> = vec![("exposed".into(), exposed.clone())];
        // Inputs: `environment.inputs` — name + optional KerML selection.
        let inputs = match self.evaluate_chain(root, &[&qn("environment"), &qn("inputs")]) {
            Ok(v) => v.items(),
            Err(_) => Vec::new(),
        };
        let mut first = true;
        for input in inputs {
            let (Value::Element(e) | Value::Unbound(e) | Value::UnboundMember(e)) = input else {
                continue;
            };
            let Some(name) = self.bound_text(e, "name") else {
                continue;
            };
            let value = match self.bound_text(e, "selection") {
                Some(sel) => self.eval_kerml(&sel, &env)?,
                None if first => exposed.clone(),
                None => Value::Sequence(Vec::new()),
            };
            first = false;
            env.push((name, value));
        }
        let mut out = Vec::new();
        self.render_children(root, &kinds, &env, &mut out)?;
        Ok(out)
    }

    fn render_children(
        &mut self,
        owner: ElementRef,
        kinds: &Kinds,
        env: &[(String, Value)],
        out: &mut Vec<RenderNode>,
    ) -> Result<(), String> {
        for m in self.owned_members(owner) {
            if self.element_type(m) != "PartUsage" {
                continue;
            }
            if self.is_slot(m) {
                continue; // named slots render on demand (body, fallback, props)
            }
            if self.conforms(m, kinds.attr) || !self.conforms(m, kinds.node) {
                continue; // attributes belong to their element; environments are not nodes
            }
            self.render_node(m, kinds, env, out)?;
        }
        Ok(())
    }

    fn render_node(
        &mut self,
        e: ElementRef,
        kinds: &Kinds,
        env: &[(String, Value)],
        out: &mut Vec<RenderNode>,
    ) -> Result<(), String> {
        if self.conforms(e, kinds.text) {
            out.push(RenderNode::Text(
                self.bound_text(e, "data").unwrap_or_default(),
            ));
        } else if self.conforms(e, kinds.comment) {
            out.push(RenderNode::Comment(
                self.bound_text(e, "data").unwrap_or_default(),
            ));
        } else if self.conforms(e, kinds.expression_tag) {
            out.push(RenderNode::Text(self.expression_text(e, env)?));
        } else if self.conforms(e, kinds.html_tag) {
            out.push(RenderNode::Raw(self.expression_text(e, env)?));
        } else if self.conforms(e, kinds.each) {
            self.render_each(e, kinds, env, out)?;
        } else if self.conforms(e, kinds.if_block) {
            let test = match self.bound_text(e, "kerml") {
                Some(k) => match self.eval_kerml(&k, env) {
                    Ok(v) => truthy(&v),
                    Err(m) => {
                        out.push(RenderNode::Error(m));
                        return Ok(());
                    }
                },
                None => {
                    out.push(RenderNode::Error(format!(
                        "untranslated test `{}`",
                        self.bound_text(e, "test").unwrap_or_default()
                    )));
                    return Ok(());
                }
            };
            let slot = if test {
                self.slot(e, "consequent")
            } else {
                self.slot(e, "alternate")
            };
            if let Some(s) = slot {
                self.render_children(s, kinds, env, out)?;
            }
        } else if self.conforms(e, kinds.component) {
            let name = self.bound_text(e, "name").unwrap_or_default();
            out.push(RenderNode::Error(format!(
                "unresolved component `{name}` (project occurrence resolver required)"
            )));
        } else if self.conforms(e, kinds.snippet_block) {
            // A snippet is a declaration; it renders only through a render tag.
        } else if self.conforms(e, kinds.render_tag) {
            out.push(RenderNode::Error(format!(
                "unsupported render tag `{}`",
                self.bound_text(e, "expression").unwrap_or_default()
            )));
        } else if self.conforms(e, kinds.await_block) {
            out.push(RenderNode::Error(format!(
                "unsupported await block `{}`",
                self.bound_text(e, "expression").unwrap_or_default()
            )));
        } else if self.conforms(e, kinds.element) || self.conforms(e, kinds.dom_element) {
            out.push(self.render_element(e, kinds, env)?);
        } else {
            // Fragments, key blocks and other containers: their content.
            for s in ["body", "consequent"] {
                if let Some(slot) = self.slot(e, s) {
                    self.render_children(slot, kinds, env, out)?;
                    return Ok(());
                }
            }
            self.render_children(e, kinds, env, out)?;
        }
        Ok(())
    }

    /// An expression tag's text: its translated KerML evaluated, else
    /// its typed source in braces (opaque).
    fn expression_text(
        &mut self,
        e: ElementRef,
        env: &[(String, Value)],
    ) -> Result<String, String> {
        if let Some(k) = self.bound_text(e, "kerml") {
            // An evaluation error degrades to the opaque source, like an
            // untranslated expression, rather than failing the view.
            if let Ok(v) = self.eval_kerml(&k, env) {
                return Ok(self.value_text(&v));
            }
        }
        Ok(format!(
            "{{{}}}",
            self.bound_text(e, "expression").unwrap_or_default()
        ))
    }

    fn render_each(
        &mut self,
        e: ElementRef,
        kinds: &Kinds,
        env: &[(String, Value)],
        out: &mut Vec<RenderNode>,
    ) -> Result<(), String> {
        let Some(k) = self.bound_text(e, "kerml") else {
            out.push(RenderNode::Error(format!(
                "untranslated collection `{}`",
                self.bound_text(e, "expression").unwrap_or_default()
            )));
            return Ok(());
        };
        let items = match self.eval_kerml(&k, env) {
            Ok(v) => v.items(),
            Err(m) => {
                out.push(RenderNode::Error(m));
                return Ok(());
            }
        };
        if items.is_empty() {
            if let Some(fb) = self.slot(e, "fallback") {
                self.render_children(fb, kinds, env, out)?;
            }
            return Ok(());
        }
        let context = self.bound_text(e, "kermlContext");
        let index = self.bound_text(e, "index");
        let body = self.slot(e, "body");
        for (i, item) in items.into_iter().enumerate() {
            let mut inner = env.to_vec();
            inner.push(("item".into(), item.clone()));
            if let Some(ctx) = &context {
                // `name = expr, name = expr`: each expression sees `'item'`.
                for binding in split_bindings(ctx) {
                    let (name, expr) = binding
                        .split_once('=')
                        .ok_or_else(|| format!("context binding `{binding}`"))?;
                    let v = self.eval_kerml(expr.trim(), &inner)?;
                    inner.push((name.trim().trim_matches('\'').to_string(), v));
                }
            }
            if let Some(ix) = &index {
                inner.push((ix.clone(), Value::Integer(i as i128)));
            }
            if let Some(b) = body {
                self.render_children(b, kinds, &inner, out)?;
            }
        }
        Ok(())
    }

    fn render_element(
        &mut self,
        e: ElementRef,
        kinds: &Kinds,
        env: &[(String, Value)],
    ) -> Result<RenderNode, String> {
        let name = self.bound_text(e, "localName").unwrap_or_default();
        let namespace = self.bound_text(e, "namespaceURI");
        let mut attributes = Vec::new();
        let mut properties = Vec::new();
        let members = self.owned_members(e);
        for m in members {
            let ty = self.element_type(m);
            if ty == "PartUsage" && self.conforms(m, kinds.attr) {
                if !self.conforms(m, kinds.attribute)
                    && !self.typings(m).is_empty()
                    && !self.conforms(m, kinds.attr)
                {
                    continue;
                }
                // Directives and spreads conform to AttributeLike but are not Attributes: skipped.
                if !self.conforms(m, kinds.attribute) {
                    continue;
                }
                let key = self.bound_text(m, "localName").unwrap_or_default();
                let value = match self.bound_text(m, "value") {
                    Some(v) => v,
                    None => {
                        // Chunks: text and expression tags in order.
                        let mut parts = Vec::new();
                        for c in self.owned_members(m) {
                            if self.element_type(c) != "PartUsage" {
                                continue;
                            }
                            if self.conforms(c, kinds.text) {
                                parts.push(self.bound_text(c, "data").unwrap_or_default());
                            } else if self.conforms(c, kinds.expression_tag) {
                                parts.push(self.expression_text(c, env)?);
                            }
                        }
                        parts.concat()
                    }
                };
                attributes.push((key, value));
            } else if (ty == "ReferenceUsage" || ty == "AttributeUsage") && self.has_value(m) {
                let Some(n) = self.b.id_name(m.0) else {
                    continue;
                };
                if matches!(n.as_str(), "localName" | "namespaceURI") || n.starts_with("kerml") {
                    continue;
                }
                if let Ok(v) = self.evaluate(m) {
                    let boolean = matches!(v, Value::Boolean(_));
                    let text = self.value_text(&v);
                    properties.push((n, text, boolean));
                }
            }
        }
        let mut children = Vec::new();
        self.render_children(e, kinds, env, &mut children)?;
        Ok(RenderNode::Element {
            name,
            namespace,
            attributes,
            properties,
            children,
        })
    }
}

/// Split `a = x, b = f(y, z)` at top-level commas.
fn split_bindings(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    let mut in_str = false;
    for c in s.chars() {
        match c {
            '"' => {
                in_str = !in_str;
                cur.push(c);
            }
            '(' | '[' | '{' if !in_str => {
                depth += 1;
                cur.push(c);
            }
            ')' | ']' | '}' if !in_str => {
                depth -= 1;
                cur.push(c);
            }
            ',' if !in_str && depth == 0 => {
                out.push(cur.trim().to_string());
                cur.clear();
            }
            _ => cur.push(c),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur.trim().to_string());
    }
    out
}
