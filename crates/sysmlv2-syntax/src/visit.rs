//! Syntax-tree traversal: a [`Visit`] trait in the style of `syn`'s
//! visitor — every method defaults to the matching `walk_*` free function,
//! so an implementation overrides only the hooks it cares about and calls
//! the `walk_*` itself to continue (or omits the call to prune).
//!
//! Coverage is *total* over the expression-bearing surface: package and
//! body members, definitions and usages (including every [`UsageDetail`]
//! variant — connector ends, triggers, payloads, control nodes),
//! feature declarations and values, multiplicity bounds, import filters,
//! and full expression recursion including lambda bodies. The corpus gate
//! (`tests/visit.rs`) holds the walk accountable: every reference the
//! parser produced must be reachable.
//!
//! ```
//! use sysmlv2_syntax::ast::QualifiedName;
//! use sysmlv2_syntax::visit::Visit;
//!
//! /// Count every qualified-name reference in a unit.
//! #[derive(Default)]
//! struct Refs(usize);
//! impl<'a> Visit<'a> for Refs {
//!     fn visit_qualified_name(&mut self, _: &'a QualifiedName) {
//!         self.0 += 1;
//!     }
//! }
//! ```

use crate::ast::*;

/// A read-only syntax-tree visitor. Every method defaults to walking the
/// node's children via the matching `walk_*`; override a method to hook a
/// node kind, and call the `walk_*` yourself to keep descending.
pub trait Visit<'a> {
    fn visit_unit(&mut self, n: &'a SourceUnit) {
        walk_unit(self, n)
    }
    fn visit_member(&mut self, n: &'a Member) {
        walk_member(self, n)
    }
    fn visit_package(&mut self, n: &'a Package) {
        walk_package(self, n)
    }
    fn visit_import(&mut self, n: &'a Import) {
        walk_import(self, n)
    }
    fn visit_definition(&mut self, n: &'a Definition) {
        walk_definition(self, n)
    }
    fn visit_usage(&mut self, n: &'a Usage) {
        walk_usage(self, n)
    }
    fn visit_usage_detail(&mut self, n: &'a UsageDetail) {
        walk_usage_detail(self, n)
    }
    fn visit_feature_declaration(&mut self, n: &'a FeatureDeclaration) {
        walk_feature_declaration(self, n)
    }
    fn visit_feature_value(&mut self, n: &'a FeatureValue) {
        walk_feature_value(self, n)
    }
    fn visit_multiplicity(&mut self, n: &'a Multiplicity) {
        walk_multiplicity(self, n)
    }
    fn visit_connector_end(&mut self, n: &'a ConnectorEnd) {
        walk_connector_end(self, n)
    }
    fn visit_payload(&mut self, n: &'a PayloadPart) {
        walk_payload(self, n)
    }
    fn visit_expr(&mut self, n: &'a Expr) {
        walk_expr(self, n)
    }
    fn visit_target_ref(&mut self, n: &'a TargetRef) {
        walk_target_ref(self, n)
    }
    fn visit_qualified_name(&mut self, _n: &'a QualifiedName) {}
}

pub fn walk_unit<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a SourceUnit) {
    for m in &n.members {
        v.visit_member(m);
    }
}

pub fn walk_member<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Member) {
    if let Some(mult) = &n.leading_then_multiplicity {
        v.visit_multiplicity(mult);
    }
    match &n.kind {
        MemberKind::Package(p) => v.visit_package(p),
        MemberKind::Import(i) | MemberKind::Expose(i) => v.visit_import(i),
        MemberKind::Alias(a) => v.visit_qualified_name(&a.target),
        MemberKind::Comment(_) | MemberKind::Doc(_) | MemberKind::TextualRep(_) => {}
        MemberKind::Definition(d) => v.visit_definition(d),
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u) => v.visit_usage(u),
        MemberKind::RequirementConstraint { usage, .. } => v.visit_usage(usage),
        MemberKind::StateSubaction { action, .. } => {
            if let Some(u) = action {
                v.visit_usage(u);
            }
        }
        MemberKind::Filter(e) | MemberKind::Result(e) => v.visit_expr(e),
        MemberKind::Dependency(d) => {
            for qn in d.metadata.iter().chain(&d.clients).chain(&d.suppliers) {
                v.visit_qualified_name(qn);
            }
        }
        MemberKind::InitialNode(qn) => v.visit_qualified_name(qn),
        MemberKind::Relationship(r) => {
            v.visit_target_ref(&r.source);
            v.visit_target_ref(&r.target);
        }
        MemberKind::MultiplicityDecl(m) => {
            if let Some(t) = &m.subsets {
                v.visit_target_ref(t);
            }
            if let Some(range) = &m.range {
                v.visit_multiplicity(range);
            }
            for member in m.body.iter().flatten() {
                v.visit_member(member);
            }
        }
    }
}

pub fn walk_package<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Package) {
    for qn in &n.metadata {
        v.visit_qualified_name(qn);
    }
    for m in n.body.iter().flatten() {
        v.visit_member(m);
    }
}

pub fn walk_import<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Import) {
    v.visit_qualified_name(&n.target);
    for f in &n.filters {
        v.visit_expr(f);
    }
}

pub fn walk_definition<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Definition) {
    for qn in &n.prefix.metadata {
        v.visit_qualified_name(qn);
    }
    for t in n
        .specializes
        .iter()
        .chain(&n.conjugates)
        .chain(&n.disjoint_from)
        .chain(&n.unions)
        .chain(&n.intersects)
        .chain(&n.differences)
    {
        v.visit_target_ref(t);
    }
    if let Some(m) = &n.multiplicity {
        v.visit_multiplicity(m);
    }
    for m in n.body.iter().flatten() {
        v.visit_member(m);
    }
}

pub fn walk_usage<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Usage) {
    for qn in &n.prefix.metadata {
        v.visit_qualified_name(qn);
    }
    if let Some(d) = &n.prefix.end_cross {
        v.visit_feature_declaration(&d.decl);
    }
    v.visit_feature_declaration(&n.declaration);
    v.visit_usage_detail(&n.detail);
    if let Some(val) = &n.value {
        v.visit_feature_value(val);
    }
    for m in n.body.iter().flatten() {
        v.visit_member(m);
    }
}

pub fn walk_feature_declaration<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a FeatureDeclaration) {
    for s in &n.specializations {
        match s {
            FeatureSpecialization::TypedBy(types) => {
                for t in types {
                    v.visit_target_ref(&t.target);
                }
            }
            FeatureSpecialization::Subsets(ts) | FeatureSpecialization::Redefines(ts) => {
                for t in ts {
                    v.visit_target_ref(t);
                }
            }
            FeatureSpecialization::References(t) | FeatureSpecialization::Crosses(t) => {
                v.visit_target_ref(t)
            }
        }
    }
    if let Some(m) = &n.multiplicity {
        v.visit_multiplicity(m);
    }
    for t in [&n.conjugates, &n.chains, &n.inverse_of]
        .into_iter()
        .flatten()
    {
        v.visit_target_ref(t);
    }
    for t in n
        .featured_by
        .iter()
        .chain(&n.disjoint_from)
        .chain(&n.unions)
        .chain(&n.intersects)
        .chain(&n.differences)
    {
        v.visit_target_ref(t);
    }
}

pub fn walk_feature_value<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a FeatureValue) {
    v.visit_expr(&n.expr);
}

pub fn walk_multiplicity<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Multiplicity) {
    if let Some(l) = &n.lower {
        v.visit_expr(l);
    }
    v.visit_expr(&n.upper);
}

pub fn walk_connector_end<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a ConnectorEnd) {
    if let Some(m) = &n.multiplicity {
        v.visit_multiplicity(m);
    }
    v.visit_target_ref(&n.target);
}

pub fn walk_payload<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a PayloadPart) {
    for s in &n.specializations {
        match s {
            FeatureSpecialization::TypedBy(types) => {
                for t in types {
                    v.visit_target_ref(&t.target);
                }
            }
            FeatureSpecialization::Subsets(ts) | FeatureSpecialization::Redefines(ts) => {
                for t in ts {
                    v.visit_target_ref(t);
                }
            }
            FeatureSpecialization::References(t) | FeatureSpecialization::Crosses(t) => {
                v.visit_target_ref(t)
            }
        }
    }
    if let Some(m) = &n.multiplicity {
        v.visit_multiplicity(m);
    }
    if let Some(val) = &n.value {
        v.visit_feature_value(val);
    }
}

pub fn walk_usage_detail<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a UsageDetail) {
    match n {
        UsageDetail::None | UsageDetail::Assert { .. } => {}
        UsageDetail::Connector { ends } | UsageDetail::Binding { ends } => {
            for e in ends {
                v.visit_connector_end(e);
            }
        }
        UsageDetail::Succession { source, target } => {
            if let Some(s) = source {
                v.visit_connector_end(s);
            }
            v.visit_connector_end(target);
        }
        UsageDetail::Flow {
            payload,
            source,
            target,
        } => {
            if let Some(p) = payload {
                v.visit_payload(p);
            }
            for end in [source, target].into_iter().flatten() {
                v.visit_target_ref(&end.target);
            }
        }
        UsageDetail::Metadata { about } => {
            for qn in about {
                v.visit_qualified_name(qn);
            }
        }
        UsageDetail::Satisfy { by, .. } => {
            if let Some(t) = by {
                v.visit_target_ref(t);
            }
        }
        UsageDetail::Accept {
            payload,
            trigger,
            via,
        } => {
            v.visit_payload(payload);
            if let Some(t) = trigger {
                v.visit_expr(&t.expr);
            }
            if let Some(e) = via {
                v.visit_expr(e);
            }
        }
        UsageDetail::Send { payload, via, to } => {
            for e in [payload, via, to].into_iter().flatten() {
                v.visit_expr(e);
            }
        }
        UsageDetail::Assign { target, value } => {
            v.visit_expr(target);
            v.visit_expr(value);
        }
        UsageDetail::Terminate { target } => {
            if let Some(e) = target {
                v.visit_expr(e);
            }
        }
        UsageDetail::IfNode {
            cond,
            then_body,
            else_body,
        } => {
            v.visit_expr(cond);
            v.visit_usage(then_body);
            if let Some(u) = else_body {
                v.visit_usage(u);
            }
        }
        UsageDetail::WhileLoop { cond, body, until } => {
            if let Some(c) = cond {
                v.visit_expr(c);
            }
            v.visit_usage(body);
            if let Some(u) = until {
                v.visit_expr(u);
            }
        }
        UsageDetail::ForLoop { var, seq, body } => {
            v.visit_feature_declaration(var);
            v.visit_expr(seq);
            v.visit_usage(body);
        }
        UsageDetail::Transition {
            source,
            trigger,
            guard,
            effect,
            target,
            ..
        } => {
            if let Some(t) = source {
                v.visit_target_ref(t);
            }
            if let Some(t) = trigger {
                v.visit_usage_detail(t);
            }
            if let Some(e) = guard {
                v.visit_expr(e);
            }
            if let Some(u) = effect {
                v.visit_usage(u);
            }
            if let Some(t) = target {
                v.visit_connector_end(t);
            }
        }
    }
}

pub fn walk_target_ref<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a TargetRef) {
    match n {
        TargetRef::Name(qn) => v.visit_qualified_name(qn),
        TargetRef::Chain(links) => {
            for qn in links {
                v.visit_qualified_name(qn);
            }
        }
    }
}

pub fn walk_expr<'a, V: Visit<'a> + ?Sized>(v: &mut V, n: &'a Expr) {
    match &n.kind {
        ExprKind::Literal(_) | ExprKind::Null | ExprKind::BodyTerminator => {}
        ExprKind::Ref(qn) | ExprKind::MetadataAccess { target: qn } => v.visit_qualified_name(qn),
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            v.visit_expr(cond);
            v.visit_expr(then_branch);
            v.visit_expr(else_branch);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            v.visit_expr(lhs);
            v.visit_expr(rhs);
        }
        ExprKind::Unary { operand, .. } => v.visit_expr(operand),
        ExprKind::Classification { operand, ty, .. } => {
            if let Some(o) = operand {
                v.visit_expr(o);
            }
            v.visit_target_ref(ty);
        }
        ExprKind::Extent { ty } => v.visit_target_ref(ty),
        ExprKind::ChainStep { target, member } => {
            v.visit_expr(target);
            v.visit_target_ref(member);
        }
        ExprKind::Index { target, index } => {
            v.visit_expr(target);
            v.visit_expr(index);
        }
        ExprKind::Bracket { target, arg } => {
            v.visit_expr(target);
            v.visit_expr(arg);
        }
        ExprKind::Arrow { target, ty, args } => {
            v.visit_expr(target);
            v.visit_target_ref(ty);
            match args {
                ArrowArgs::Body(b) => v.visit_expr(b),
                ArrowArgs::FunctionRef(qn) => v.visit_qualified_name(qn),
                ArrowArgs::List(list) => {
                    for a in list {
                        v.visit_expr(&a.value);
                    }
                }
            }
        }
        ExprKind::Collect { target, body } | ExprKind::Select { target, body } => {
            v.visit_expr(target);
            v.visit_expr(body);
        }
        ExprKind::Invocation { ty, args } | ExprKind::Constructor { ty, args } => {
            v.visit_target_ref(ty);
            for a in args {
                if let Some(name) = &a.name {
                    v.visit_qualified_name(name);
                }
                v.visit_expr(&a.value);
            }
        }
        ExprKind::Body { members } => {
            for m in members {
                v.visit_member(m);
            }
        }
        ExprKind::Sequence(items) => {
            for e in items {
                v.visit_expr(e);
            }
        }
    }
}
