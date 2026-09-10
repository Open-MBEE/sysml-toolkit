#!/usr/bin/env python3
"""Generate the XMI property table for the per-metaclass property audit.

Reads the vendored normative metamodel XMI (spec-refs/KerML.xmi +
spec-refs/SysML.xmi, 20250201) and writes
crates/sysmlv2-testkit/src/xmi_props.rs: for every metaclass, the full
inherited closure of its properties with the `isDerived` flag — the
authoritative owned-vs-derived split that the compact interchange form
must honor (KerML 10.4) and the JSON schemas do not carry.

SysML.xmi generalizes into KerML.xmi via `<general href="…KerML.xmi#id"/>`;
both files resolve into one class table here. A subclass attribute that
reuses an inherited name (a UML redefinition) wins in the closure.

Usage: python3 tools/xmi_props.py   (from the workspace root)
"""

import xml.etree.ElementTree as ET
from pathlib import Path

XMI_ID = "{http://www.omg.org/spec/XMI/20161101}id"
XMI_IDREF = "{http://www.omg.org/spec/XMI/20161101}idref"
XMI_TYPE = "{http://www.omg.org/spec/XMI/20161101}type"

ROOT = Path(__file__).resolve().parent.parent
SOURCES = [ROOT / "spec-refs" / "KerML.xmi", ROOT / "spec-refs" / "SysML.xmi"]
OUT = ROOT / "crates" / "sysmlv2-testkit" / "src" / "xmi_props.rs"

FLAG_DERIVED = 1
FLAG_DEFAULT = 2
FLAG_OPTIONAL = 4  # lower multiplicity bound 0


def ref_of(el):
    """Target id of an idref- or href-based reference element."""
    ref = el.get(XMI_IDREF)
    if ref is None and el.get("href"):
        ref = el.get("href").split("#", 1)[1]
    return ref


def load(path, prop_names):
    """id → class record for every uml:Class in one XMI file.

    `prop_names` accumulates property-id → name across files so
    `redefinedProperty` idrefs/hrefs can be resolved to names later.
    """
    classes = {}
    root = ET.parse(path).getroot()
    for p in root.iter("ownedAttribute"):
        if p.get(XMI_TYPE) == "uml:Property":
            prop_names[p.get(XMI_ID)] = p.get("name")
    for el in root.iter("packagedElement"):
        if el.get(XMI_TYPE) != "uml:Class":
            continue
        generals = [ref_of(g) for g in el.iter("general")]
        attrs = []
        for a in el.findall("ownedAttribute"):
            flags = 0
            if a.get("isDerived") == "true":
                flags |= FLAG_DERIVED
            if a.find("defaultValue") is not None:
                flags |= FLAG_DEFAULT
            # UML default multiplicity is 1..1; a lowerValue element
            # without a value attribute is LiteralInteger 0.
            lv = a.find("lowerValue")
            if lv is not None and int(lv.get("value") or 0) == 0:
                flags |= FLAG_OPTIONAL
            redefined = [ref_of(r) for r in a.findall("redefinedProperty")]
            attrs.append((a.get("name"), flags, redefined))
        classes[el.get(XMI_ID)] = {
            "name": el.get("name"),
            "abstract": el.get("isAbstract") == "true",
            "generals": generals,
            "attrs": attrs,
        }
    return classes


def closure(classes, prop_names, cid, out):
    """Union of own + inherited attrs; nearer (redefining) names win."""
    for name, flags, redefined in classes[cid]["attrs"]:
        names = tuple(sorted(prop_names[r] for r in redefined))
        out.setdefault(name, (flags, names))
    for g in classes[cid]["generals"]:
        closure(classes, prop_names, g, out)
    return out


def main():
    classes = {}
    prop_names = {}
    for src in SOURCES:
        classes.update(load(src, prop_names))
    rows = []
    for cid, c in classes.items():
        props = sorted(closure(classes, prop_names, cid, {}).items())
        rows.append((c["name"], c["abstract"], props))
    rows.sort()
    dupes = {n for i, (n, _, _) in enumerate(rows) if i and rows[i - 1][0] == n}
    if dupes:
        raise SystemExit(f"metaclass name collision across files: {dupes}")

    lines = [
        "//! Generated from `spec-refs/{KerML,SysML}.xmi` (normative metamodel",
        "//! 20250201) by `tools/xmi_props.py` — do not edit. Per-metaclass",
        "//! property closure (own + inherited) with the normative",
        "//! owned-vs-derived split, for the property-audit gate.",
        "",
        "/// The property is derived (`isDerived=\"true\"` in the XMI): it",
        "/// belongs to the full interchange form only, never the compact form.",
        "pub const XMI_DERIVED: u8 = 1;",
        "/// The property declares a default value in the metamodel.",
        "pub const XMI_HAS_DEFAULT: u8 = 2;",
        "/// The property's lower multiplicity bound is 0.",
        "pub const XMI_OPTIONAL: u8 = 4;",
        "",
        "/// `(property, flags, redefined property names)`.",
        "pub type XmiProp = (&'static str, u8, &'static [&'static str]);",
        "",
        "/// `(metaclass, is_abstract, property closure)`.",
        "pub type XmiClass = (&'static str, bool, &'static [XmiProp]);",
        "",
        "/// Every metaclass in the merged KerML + SysML metamodel, sorted by name.",
        "pub static XMI_PROPS: &[XmiClass] = &[",
    ]
    for name, is_abstract, props in rows:
        lines.append(f'    ("{name}", {str(is_abstract).lower()}, &[')
        for pname, (flags, redefined) in props:
            rd = ", ".join(f'"{r}"' for r in redefined)
            lines.append(f'        ("{pname}", {flags}, &[{rd}]),')
        lines.append("    ]),")
    lines.append("];")
    lines.append("")
    OUT.write_text("\n".join(lines))
    n_props = sum(len(p) for _, _, p in rows)
    print(f"wrote {OUT.relative_to(ROOT)}: {len(rows)} metaclasses, {n_props} closure entries")


if __name__ == "__main__":
    main()
