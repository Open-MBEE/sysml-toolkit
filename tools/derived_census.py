#!/usr/bin/env python3
"""Census of the metamodel's derived properties against the toolkit.

Reads the vendored normative metamodel XMI (spec-refs/KerML.xmi +
spec-refs/SysML.xmi, 20250201), the full-form emitter
(crates/sysmlv2-model/src/full.rs) and the corpus baseline the
`full_baseline` test maintains
(crates/sysmlv2-parser/tests/fixtures/full-form-baseline.tsv), and writes

- spec-refs/derived-properties.json — one record per derived property
  name: declaring metaclasses, target type, multiplicity, subsetted and
  redefined properties, the OCL derivation rule, the class the toolkit
  computes it in, and its implementation status;
- spec-refs/derived-properties.md — the same as tables, with counts.

The class is computed from the rules, not hand-listed: a property is a
*closure* when it is one of the four inheritance/import closures, an
*inheritance-aware* property when its derivation rule (transitively)
reads a closure or another inheritance-aware property, and *structural*
otherwise. Implementation status combines two evidence sources, because
neither alone is reliable: whether the emitter names the property (code
inspection) and how often the corpus emits a non-empty value for it
(fill rate). A name the emitter never mentions is *absent* whatever the
catalog default; a mentioned name with no non-empty corpus value is
*unexercised* and needs adjudication by hand.

Usage: python3 tools/derived_census.py   (from the workspace root)
"""

import html
import json
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from collections import defaultdict
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from xmi_props import SOURCES, XMI_ID, XMI_IDREF, XMI_TYPE, closure, load, ref_of  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
EMITTER = ROOT / "crates/sysmlv2-model/src/full.rs"
BASELINE = ROOT / "crates/sysmlv2-parser/tests/fixtures/full-form-baseline.tsv"
OUT_JSON = ROOT / "spec-refs/derived-properties.json"
OUT_MD = ROOT / "spec-refs/derived-properties.md"
OUT_RS = ROOT / "crates/sysmlv2-model/src/derived_names.rs"
OUT_COMPOSITIONS = ROOT / "crates/sysmlv2-model/src/json/derived_compositions.rs"

# Bases the XMI spells that this metamodel version does not carry under
# that name, or misspells.
BASE_ALIASES = {"usages": "usage", "ownedGeneralization": "ownedSpecialization"}
# A rule whose left-hand side is misspelled (`ownedNested = nestedUsage->…`
# for `nestedEnumeration`): the rule is attributed to its property by
# constraint name already, so the left-hand side is only a guard.
LHS_ALIASES = {"ownedNested": "nestedEnumeration"}

CLOSURES = {"inheritedMembership", "inheritedFeature", "importedMembership", "featuringType"}

# Hand adjudications the mechanical rule cannot make. `subsets` does not
# propagate a class in general (`owningMembership` subsets `membership`
# structurally), but `Function::expression` — "the Expressions that are
# steps", subsetting `step`, no OCL rule — is a kind filter over the
# inheritance-aware `step`, the same shape as `calculation` over `action`.
CLASS_OVERRIDES = {"expression": "inheritance-aware"}


def strip_html(text):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", html.unescape(text or ""))).strip()


def read_xmi():
    """Derived attributes with their facts, keyed by name, plus the rules."""
    ids = {}  # xmi id -> element name (classes and properties)
    derived = defaultdict(lambda: {"declaring": [], "types": set(), "rules": {}})
    rules_by_class = defaultdict(dict)  # class name -> rule name -> body
    roots = [(src, ET.parse(src).getroot()) for src in SOURCES]
    for _, root in roots:
        for el in root.iter():
            if el.get(XMI_ID) and el.get("name"):
                ids[el.get(XMI_ID)] = el.get("name")
    for _, root in roots:
        for cls in root.iter("packagedElement"):
            if cls.get(XMI_TYPE) != "uml:Class":
                continue
            cname = cls.get("name")
            for rule in cls.findall("ownedRule"):
                spec = rule.find("specification")
                if spec is not None and spec.get("body"):
                    rules_by_class[cname][rule.get("name")] = html.unescape(spec.get("body"))
            for a in cls.findall("ownedAttribute"):
                if a.get(XMI_TYPE) != "uml:Property" or a.get("isDerived") != "true":
                    continue
                name = a.get("name")
                rec = derived[name]
                lower = a.find("lowerValue")
                upper = a.find("upperValue")
                lo = int(lower.get("value") or 0) if lower is not None else 1
                up = (upper.get("value") or "1") if upper is not None else "1"
                up = "*" if up == "-1" else up
                tref = a.find("type")
                tid = ref_of(tref) if tref is not None else None
                # Primitive types live in PrimitiveTypes.xmi, outside `ids`.
                tname = ids.get(tid, tid or "?")
                comment = a.find("ownedComment")
                raw_doc = html.unescape(comment.get("body") or "") if comment is not None else ""
                rec["declaring"].append(
                    {
                        "metaclass": cname,
                        "type": tname,
                        "multiplicity": f"{lo}..{up}",
                        "ordered": a.get("isOrdered") == "true",
                        "subsets": sorted(ids.get(ref_of(s), "?") for s in a.findall("subsettedProperty")),
                        "redefines": sorted(ids.get(ref_of(r), "?") for r in a.findall("redefinedProperty")),
                        "doc": strip_html(raw_doc),
                        # The names the normative prose marks as code — the
                        # only tokens that stand for properties in a doc.
                        "doc_refs": sorted(set(re.findall(r"<code>([A-Za-z_][A-Za-z0-9_]*)</code>", raw_doc))),
                    }
                )
                rec["types"].add(tname)
    # Attach derivation rules: every `derive<Class><Prop>` rule, on the
    # declaring class or on a subclass that refines the derivation
    # (`deriveInvocationExpressionArgument` for InstantiationExpression's
    # `argument`), plus any `derive*` rule whose body assigns the property.
    for cname, rules in rules_by_class.items():
        for rname, body in rules.items():
            if not rname.startswith("derive"):
                continue
            assigned = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*=[^=]", body)
            for name, rec in derived.items():
                cap = name[0].upper() + name[1:]
                if rname == f"derive{cname}{cap}" or (assigned and assigned.group(1) == name):
                    rec["rules"][cname] = body
    return derived


def emitter_mentions():
    """Property names the emitter *writes*. A literal that only ever
    appears as a read (`get("x")`, `contains_key("x")`) is the owned
    spelling being consulted, not a derivation."""
    text = EMITTER.read_text()
    written = set()
    for m in re.finditer(r'"([a-z][A-Za-z]+)"', text):
        before = text[max(0, m.start() - 16) : m.start()]
        if re.search(r'(?:get|get_mut|contains_key|remove)\(&?$|\[$', before):
            continue
        written.add(m.group(1))
    return written


def ancestors(classes):
    """class name -> {names of its superclasses}, transitively."""
    by_id = {cid: c["name"] for cid, c in classes.items()}
    gens = {c["name"]: [by_id[g] for g in c["generals"]] for c in classes.values()}
    out = {}

    def walk(n):
        if n in out:
            return out[n]
        acc = set()
        for g in gens.get(n, ()):
            acc.add(g)
            acc |= walk(g)
        out[n] = acc
        return acc

    for n in gens:
        walk(n)
    return out


def descendants(classes):
    """class name -> {names of it and every subclass}."""
    by_id = {cid: c["name"] for cid, c in classes.items()}
    down = defaultdict(set)
    for cid, c in classes.items():
        for g in c["generals"]:
            down[by_id[g]].add(c["name"])
    out = {}

    def walk(n):
        if n in out:
            return out[n]
        acc = {n}
        for d in down.get(n, ()):
            acc |= walk(d)
        out[n] = acc
        return acc

    for n in by_id.values():
        walk(n)
    return out


def baseline_fill(derived_on):
    """name -> (elements, nonempty) summed over the metaclasses on which
    the name is *derived*; None if the baseline is absent. A name can be
    owned on one metaclass and derived on another (`importedMembership`
    is owned on MembershipImport, derived on Namespace), so the owned
    spellings must not count as derived fill."""
    if not BASELINE.exists():
        return None
    fill = defaultdict(lambda: [0, 0])
    per_class = defaultdict(dict)  # prop -> metaclass -> [elements, nonempty]
    for line in BASELINE.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        metaclass, prop, _, elements, nonempty = line.split("\t")
        if (metaclass, prop) not in derived_on:
            continue
        fill[prop][0] += int(elements)
        fill[prop][1] += int(nonempty)
        per_class[prop][metaclass] = [int(elements), int(nonempty)]
    return fill, per_class


def classify(derived, derived_on, ancestors_of):
    """closure / inheritance-aware / structural. A rule's references
    propagate transitively (`usage = feature->…` inherits `feature`'s
    class). A property without a rule counts only a *direct* reference to
    a closure in its code-marked documentation, and only where that
    closure is derived on the declaring metaclass (`MembershipImport`'s
    `importedMembership` is the owned spelling): prose references to
    ordinary properties are back-references as often as derivations."""
    ident = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
    # Iterator and let-bound variables (`select(f | …)`, `let t : Type =`)
    # are not property navigations, whatever they are called.
    bound = re.compile(r"(?:\(|,)\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?::\s*[A-Za-z_][A-Za-z0-9_()]*\s*)?\||let\s+([A-Za-z_][A-Za-z0-9_]*)")
    known = set(derived)

    def canon(tok):
        # `importedMemberships` (an operation, or prose plural) names the
        # property `importedMembership`.
        if tok not in known and tok.endswith("s") and tok[:-1] in known:
            return tok[:-1]
        return tok

    refs = {}
    for name, rec in derived.items():
        toks = set()
        for cname, body in rec["rules"].items():
            vars_ = {v for pair in bound.findall(body) for v in pair if v}
            for t in ident.findall(body):
                if t in vars_:
                    continue
                t = canon(t)
                # A closure name counts only where it is the derived
                # property, not an owned spelling of the same name.
                if t in CLOSURES and (cname, t) not in derived_on:
                    continue
                toks.add(t)
        if not rec["rules"]:
            # No OCL rule: the normative documentation is the only
            # statement of the derivation (`membership` = "the union of
            # ownedMemberships and importedMemberships").
            for decl in rec["declaring"]:
                toks.update(
                    canon(t)
                    for t in decl["doc_refs"]
                    if canon(t) in CLOSURES and (decl["metaclass"], canon(t)) in derived_on
                )
                # A UML redefinition is the redefined property under a
                # narrower name (`parameter` redefines `directedFeature`),
                # so it takes that property's class. A mere `subsets` does
                # not: `owningType` subsets `featuringType` structurally.
                toks.update(decl["redefines"])
        refs[name] = toks - {name}
    cls = {n: "closure" for n in CLOSURES}
    changed = True
    while changed:
        changed = False
        for name in derived:
            if name in cls:
                continue
            if any(t in cls and cls[t] in ("closure", "inheritance-aware") for t in refs[name]):
                cls[name] = "inheritance-aware"
                changed = True
    for name in derived:
        cls.setdefault(name, "structural")
    for name, forced in CLASS_OVERRIDES.items():
        cls[name] = forced
    # Per declaration: the same name can be several properties, and only
    # the declarations whose own rule (or the rule of a refining subclass),
    # redefinition or documentation reaches a closure are inheritance-aware
    # (`Connector::targetFeature` is, `FeatureChainExpression::targetFeature`
    # is not).
    decl_cls = {}
    for name, rec in derived.items():
        for decl in rec["declaring"]:
            cname = decl["metaclass"]
            if name in CLOSURES:
                decl_cls[(name, cname)] = "closure"
                continue
            if name in CLASS_OVERRIDES:
                decl_cls[(name, cname)] = CLASS_OVERRIDES[name]
                continue
            toks = set(decl["redefines"])
            for rule_class, body in rec["rules"].items():
                if rule_class == cname or cname in ancestors_of.get(rule_class, set()):
                    vars_ = {v for pair in bound.findall(body) for v in pair if v}
                    for t in ident.findall(body):
                        if t in vars_:
                            continue
                        t = canon(t)
                        # Same guard as the name-level pass: a closure name
                        # counts only where it is the derived property.
                        if t in CLOSURES and (rule_class, t) not in derived_on:
                            continue
                        toks.add(t)
            if not rec["rules"]:
                toks.update(canon(t) for t in decl["doc_refs"] if canon(t) in CLOSURES and (cname, canon(t)) in derived_on)
            aware = any(t != name and cls.get(t) in ("closure", "inheritance-aware") for t in toks)
            decl_cls[(name, cname)] = "inheritance-aware" if aware else "structural"
    # The two computations must agree: a name's class is the strongest of
    # its declarations' classes.
    rank = {"structural": 0, "inheritance-aware": 1, "closure": 2}
    for name, rec in derived.items():
        strongest = max((decl_cls[(name, d["metaclass"])] for d in rec["declaring"]), key=rank.get)
        assert cls[name] == strongest, f"{name}: name class {cls[name]} vs declarations {strongest}"
    return cls, decl_cls


def concrete_carriers(classes, prop_names):
    """(name -> number of concrete metaclasses whose closure carries it as
    derived, {(metaclass, name)} where it is derived, {name} that is owned
    on some metaclass and derived on another)."""
    carriers = defaultdict(int)
    derived_on = set()
    owned_on = set()
    for cid, c in classes.items():
        for pname, (flags, _) in closure(classes, prop_names, cid, {}).items():
            if flags & 1:
                derived_on.add((c["name"], pname))
                if not c["abstract"]:
                    carriers[pname] += 1
            else:
                owned_on.add(pname)
    dual = {p for (_, p) in derived_on} & owned_on
    return carriers, derived_on, dual


def write_compositions(records):
    """The kind-filtered compositions: every derived property whose OCL
    rule is `name = base->selectByKind(Kind)` (or `selectAsKind`), plus
    the rule-less `*Definition` back-references, which the normative
    documentation defines as the usage's definitions of the property's
    declared type (`definition->selectByKind(<type>)`). Single-valued
    properties (upper bound 1) take the first match."""
    # `name = base->selectByKind(Kind)`, or the same without the left-hand
    # side (a few rules spell the expression alone).
    pat = re.compile(r"^\s*(?:(\w+)\s*=\s*)?(\w+)\s*->\s*select(?:By|As)Kind\(\s*(\w+)\s*\)\s*$")
    rows = {}
    for r in records:
        name = r["name"]
        single = all(d["multiplicity"].endswith("..1") for d in r["declaring"])
        for body in r["rules"].values():
            m = pat.match(body.replace("\n", " "))
            lhs = LHS_ALIASES.get(m.group(1), m.group(1)) if m else None
            if m and lhs in (None, name):
                base = BASE_ALIASES.get(m.group(2), m.group(2))
                rows.setdefault(name, (base, m.group(3), single))
        # A `*Definition` back-reference declared on a usage without a rule
        # on that usage (per declaration: `PortUsage::portDefinition` has
        # no rule although `ConjugatedPortTyping::portDefinition` does).
        if name.endswith("Definition") and name not in ("owningDefinition", "originalPortDefinition"):
            decls = [
                d
                for d in r["declaring"]
                if d["metaclass"].endswith("Usage") and d["metaclass"] not in r["rules"]
            ]
            if decls and name not in rows:
                kinds = sorted({d["type"] for d in decls})
                if len(kinds) == 1:
                    rows.setdefault(name, ("definition", kinds[0], single))
    lines = [
        "//! Generated from `spec-refs/{KerML,SysML}.xmi` (normative metamodel",
        "//! 20250201) by `tools/derived_census.py` — do not edit.",
        "//!",
        "//! Kind-filtered compositions among the derived properties: `name =",
        "//! base->selectByKind(kind)` per the OCL derivation rules, and the",
        "//! rule-less `*Definition` back-references, which the normative",
        "//! documentation defines as the usage's `definition`s of the",
        "//! property's declared type. `single` marks an upper bound of 1 (the",
        "//! first match, else null). A composition is computable exactly when",
        "//! its base is.",
        "",
        "/// `(name, base, kind, single)`, sorted by name.",
        "pub(crate) static COMPOSITIONS: &[(&str, &str, &str, bool)] = &[",
    ]
    for name in sorted(rows):
        base, kind, single = rows[name]
        lines.append(f'    ("{name}", "{base}", "{kind}", {str(single).lower()}),')
    lines += ["];", ""]
    OUT_COMPOSITIONS.write_text("\n".join(lines))
    subprocess.run(["rustfmt", "--edition", "2024", str(OUT_COMPOSITIONS)], check=False)
    return len(rows)


def write_rust_table(classes, prop_names, derived_names, dual):
    """The model crate's derived-name table: every derived name, the
    metaclasses (abstract ones included — the schema catalog carries a
    few) on which a dual-spelled name is *owned*, and the abstract
    metaclasses themselves."""
    owned_on = defaultdict(list)
    for cid, c in classes.items():
        for pname, (flags, _) in closure(classes, prop_names, cid, {}).items():
            if pname in dual and not flags & 1:
                owned_on[pname].append(c["name"])
    lines = [
        "//! Generated from `spec-refs/{KerML,SysML}.xmi` (normative metamodel",
        "//! 20250201) by `tools/derived_census.py` — do not edit.",
        "//!",
        "//! The abstract syntax's derived property names, for the derived-property",
        "//! read API: a property is derived on a concrete metaclass when the",
        "//! schema catalog declares it, its name is in [`DERIVED_NAMES`], and the",
        "//! metaclass is not listed under that name in [`OWNED_ON`] (a few names",
        "//! are owned on one metaclass and derived on another).",
        "",
        "/// Every `isDerived` property name, sorted.",
        "pub(crate) static DERIVED_NAMES: &[&str] = &[",
    ]
    lines += [f'    "{n}",' for n in sorted(derived_names)]
    lines += [
        "];",
        "",
        "/// Names that are derived somewhere but *owned* on these metaclasses",
        "/// (abstract ones included).",
        "pub(crate) static OWNED_ON: &[(&str, &[&str])] = &[",
    ]
    for pname in sorted(owned_on):
        cls_list = ", ".join(f'"{c}"' for c in sorted(owned_on[pname]))
        lines.append(f'    ("{pname}", &[{cls_list}]),')
    lines += [
        "];",
        "",
        "/// The abstract metaclasses of the abstract syntax, sorted: no element",
        "/// has one, and the property catalog skips them.",
        "pub(crate) static ABSTRACT_METACLASSES: &[&str] = &[",
    ]
    lines += [f'    "{c["name"]}",' for c in sorted(classes.values(), key=lambda c: c["name"]) if c["abstract"]]
    lines += ["];", ""]
    OUT_RS.write_text("\n".join(lines))
    subprocess.run(["rustfmt", "--edition", "2024", str(OUT_RS)], check=False)


def main():
    derived = read_xmi()
    classes, prop_names = {}, {}
    for src in SOURCES:
        classes.update(load(src, prop_names))
    carriers, derived_on, dual = concrete_carriers(classes, prop_names)
    mentioned = emitter_mentions()
    fill, per_class = baseline_fill(derived_on) if BASELINE.exists() else (None, None)
    below = descendants(classes)
    ancestors_of = ancestors(classes)
    cls, decl_cls = classify(derived, derived_on, ancestors_of)

    records = []
    for name in sorted(derived):
        rec = derived[name]
        elements, nonempty = (fill.get(name, [0, 0]) if fill is not None else [None, None])
        # Corpus fill is the primary evidence: a non-empty value proves the
        # emitter derives the name whether or not a literal names it
        # (membership required-reference aliases write under every
        # redefining name). A literal without fill is unexercised.
        if fill is not None and nonempty:
            status = "derived"
        elif name in mentioned:
            status = "unexercised" if fill is not None else "derived"
        else:
            status = "absent"
        # Fill per declaration: summed over the declaring metaclass and its
        # subclasses, since one name can be several properties (`action` on
        # StateSubactionMembership vs. ActionDefinition).
        if per_class is not None:
            for decl in rec["declaring"]:
                sub = below.get(decl["metaclass"], {decl["metaclass"]})
                e = sum(v[0] for c, v in per_class.get(name, {}).items() if c in sub)
                n = sum(v[1] for c, v in per_class.get(name, {}).items() if c in sub)
                decl["corpus_elements"], decl["corpus_nonempty"] = e, n
        for decl in rec["declaring"]:
            decl["class"] = decl_cls[(name, decl["metaclass"])]
        records.append(
            {
                "name": name,
                "class": cls[name],
                "status": status,
                "declaring": rec["declaring"],
                "concrete_carriers": carriers.get(name, 0),
                "also_owned_elsewhere": name in dual,
                "rules": rec["rules"],
                "corpus_elements": elements,
                "corpus_nonempty": nonempty,
            }
        )

    write_rust_table(classes, prop_names, set(derived), dual)
    n_comp = write_compositions(records)
    OUT_JSON.write_text(json.dumps({"source": "spec-refs/{KerML,SysML}.xmi 20250201", "generator": "tools/derived_census.py", "properties": records}, indent=1) + "\n")

    by_class = defaultdict(list)
    by_status = defaultdict(list)
    for r in records:
        by_class[r["class"]].append(r["name"])
        by_status[r["status"]].append(r["name"])
    lines = [
        "# Derived properties — census",
        "",
        "Generated by `tools/derived_census.py` from `spec-refs/{KerML,SysML}.xmi` (20250201), the full-form emitter and the corpus baseline. Do not edit; regenerate after changing the emitter and refreshing the baseline. The JSON twin `derived-properties.json` carries the per-declaration facts (type, multiplicity, subsets, redefines, OCL rule).",
        "",
        f"{len(records)} distinct derived property names. Status: **derived** = the corpus emits a non-empty value for it on a metaclass where it is derived (the primary evidence — the emitter writes some names without a literal, through the membership required-reference alias); **unexercised** = the emitter writes the name but the corpus never emits a non-empty value (a placeholder such as the `result` self-reference, or a shape only foreign payloads carry); **absent** = never written, so it falls to the catalog's type-correct empty default.",
        "",
        "| Class | Total | derived | unexercised | absent |",
        "|---|---|---|---|---|",
    ]
    for c in ("structural", "inheritance-aware", "closure"):
        names = by_class[c]
        counts = {s: sum(1 for n in names if next(r for r in records if r["name"] == n)["status"] == s) for s in ("derived", "unexercised", "absent")}
        lines.append(f"| {c} | {len(names)} | {counts['derived']} | {counts['unexercised']} | {counts['absent']} |")
    lines.append(f"| **all** | {len(records)} | {len(by_status['derived'])} | {len(by_status['unexercised'])} | {len(by_status['absent'])} |")
    lines += [
        "",
        "A *closure* is one of the four inheritance/import closures; an *inheritance-aware* property is one whose derivation rule (or, for a property without an OCL rule, the property it redefines, or its normative documentation's direct closure reference) transitively reads a closure, so its passthrough-level value is an owned-only approximation until the closure policy is on; everything else is *structural*. Hand adjudications: " + ", ".join(f"`{n}` → {c}" for n, c in sorted(CLASS_OVERRIDES.items())) + ". A name's class is the strongest over its declarations; names whose declarations disagree: " + (", ".join(f"`{r['name']}`" for r in records if len({d['class'] for d in r['declaring']}) > 1) or "(none)") + ".",
        "",
        "Names that are derived on one metaclass and owned on another (corpus fill counts only the derived carriers, and an emitter mention of such a name may be a read of the owned spelling): " + (", ".join(f"`{n}`" for n in sorted(dual)) or "(none)") + ".",
        "",
        "## Inheritance-aware names",
        "",
        ", ".join(f"`{n}`" for n in sorted(by_class["inheritance-aware"])) or "(none)",
        "",
        "## Every derived name",
        "",
        "| Name | Class | Status | Declared by | Carriers | Type | Corpus non-empty / elements |",
        "|---|---|---|---|---|---|---|",
    ]
    for r in records:
        decl = ", ".join(d["metaclass"] for d in r["declaring"])
        types = ", ".join(sorted({d["type"] for d in r["declaring"]}))
        fillcol = "—" if r["corpus_elements"] is None else f"{r['corpus_nonempty']} / {r['corpus_elements']}"
        lines.append(f"| `{r['name']}` | {r['class']} | {r['status']} | {decl} | {r['concrete_carriers']} | {types} | {fillcol} |")
    lines.append("")
    OUT_MD.write_text("\n".join(lines))

    print(f"wrote {OUT_JSON.relative_to(ROOT)}, {OUT_MD.relative_to(ROOT)} and {OUT_RS.relative_to(ROOT)}")
    print(f"{len(records)} derived names: " + ", ".join(f"{s}={len(by_status[s])}" for s in ("derived", "unexercised", "absent")))
    print("classes: " + ", ".join(f"{c}={len(by_class[c])}" for c in ("structural", "inheritance-aware", "closure")))
    missing_rules = [r["name"] for r in records if not r["rules"]]
    print(f"names without a matched derivation rule: {len(missing_rules)}")
    print(f"names owned on one metaclass and derived on another: {sorted(dual)}")
    print(f"kind-filtered compositions generated: {n_comp}")
    if fill is None:
        print("baseline fixture absent: statuses use emitter mentions only")


if __name__ == "__main__":
    main()
