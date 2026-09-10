#!/usr/bin/env python3
"""Generate the CBOR codec tables for the compact interchange form.

Reads the vendored normative metamodel XMI (spec-refs/KerML.xmi +
spec-refs/SysML.xmi, 20250201) for the owned-vs-derived property split
and declared boolean defaults, and the normative JSON schemas
(spec-refs/{KerML,SysML}.schema.json) for value shapes and enum
vocabularies, and writes crates/sysmlv2-model/src/cbor_tables.rs:

- the concrete-metaclass type index (sorted; position = wire type code),
- per-metaclass field lists (lexicographic; position = wire ordinal),
  each field carrying its value kind, enum table, and default,
- the closed enum vocabularies (`*Kind`, schema declaration order).

Usage: python3 tools/gen_cbor_tables.py   (from the workspace root)
"""

import json
import xml.etree.ElementTree as ET
from pathlib import Path

import xmi_props as XP

ROOT = Path(__file__).resolve().parent.parent
SCHEMAS = [ROOT / "spec-refs" / "SysML.schema.json",
           ROOT / "spec-refs" / "KerML.schema.json"]
OUT = ROOT / "crates" / "sysmlv2-model" / "src" / "cbor_tables.rs"

K_BOOL, K_STR, K_STR_LIST, K_REF, K_REF_LIST, K_ENUM, K_LITERAL, K_ELEMENT_ID = range(8)
NO_ENUM = 255
NULL_DEFAULT = 255


def load_classes_with_defaults():
    """name → (attrs {prop: (derived, bool_default)}, generals, abstract)."""
    classes = {}
    prop_names = {}
    for src in XP.SOURCES:
        classes.update(XP.load(src, prop_names))
    # Re-scan for boolean defaults (xmi_props keeps only a flag).
    defaults = {}
    for src in XP.SOURCES:
        root = ET.parse(src).getroot()
        for el in root.iter("packagedElement"):
            if el.get(XP.XMI_TYPE) != "uml:Class":
                continue
            for a in el.findall("ownedAttribute"):
                dv = a.find("defaultValue")
                if dv is not None and dv.get("value") == "true":
                    defaults[(el.get("name"), a.get("name"))] = True
    return classes, defaults


def closure_props(classes, defaults, cid, out, cname):
    """Nearest-first (redefining wins) closure of (derived, default)."""
    c = classes[cid]
    for name, flags, _ in c["attrs"]:
        if name not in out:
            out[name] = (bool(flags & XP.FLAG_DERIVED),
                         defaults.get((c["name"], name), False))
    for g in c["generals"]:
        closure_props(classes, defaults, g, out, cname)
    return out


def schema_block(defs_list, cls):
    for defs in defs_list:
        if cls in defs:
            d = defs[cls]
            return (d.get("anyOf") or [d])[0]
    raise SystemExit(f"metaclass {cls} missing from both schemas")


def classify(cls, prop, sch, enum_ids, bool_default):
    """(kind, enum table index, default byte) for one property schema."""
    if prop == "elementId":
        return K_ELEMENT_ID, NO_ENUM, 0
    variants = sch.get("oneOf") or sch.get("anyOf") or [sch]
    identified = enum = arr = None
    prims = set()
    for v in variants:
        if v.get("type") == "null":
            continue
        if "$ref" in v:
            tail = v["$ref"].rsplit("/", 1)[-1]
            if tail == "Identified":
                identified = True
            elif tail in enum_ids:
                enum = tail
            else:
                raise SystemExit(f"{cls}.{prop}: unexpected $ref {tail}")
        elif v.get("type") == "array":
            item = v.get("items", {})
            if item.get("$ref", "").endswith("/Identified"):
                arr = K_REF_LIST
            elif item.get("type") == "string":
                arr = K_STR_LIST
            else:
                raise SystemExit(f"{cls}.{prop}: unexpected array items")
        elif v.get("type") in ("boolean", "string", "number", "integer"):
            prims.add(v["type"])
        else:
            raise SystemExit(f"{cls}.{prop}: unmappable variant {v}")
    if identified:
        return K_REF, NO_ENUM, 0
    if enum:
        default = NULL_DEFAULT
        if prop == "visibility":  # normative VisibilityKind default
            default = enum_ids[enum].index("public")
        return K_ENUM, sorted(enum_ids).index(enum), default
    if arr is not None:
        return arr, NO_ENUM, 0
    if prims == {"boolean"}:
        return K_BOOL, NO_ENUM, int(bool_default)
    if prims == {"string"}:
        return K_STR, NO_ENUM, 0
    if prims:  # polymorphic literal value
        return K_LITERAL, NO_ENUM, 0
    raise SystemExit(f"{cls}.{prop}: empty shape")


def main():
    classes, defaults = load_classes_with_defaults()
    defs_list = [json.load(p.open())["$defs"] for p in SCHEMAS]

    enum_ids = {}
    for defs in defs_list:
        for name, d in defs.items():
            if name.endswith("Kind") and d.get("type") == "string":
                vals = d["enum"]
                assert enum_ids.get(name, vals) == vals, name
                enum_ids[name] = vals

    rows = []
    for cid, c in classes.items():
        if c["abstract"]:
            continue
        props = closure_props(classes, defaults, cid, {}, c["name"])
        fields = sorted(n for n, (derived, _) in props.items() if not derived)
        block = schema_block(defs_list, c["name"])
        sprops = block.get("properties", {})

        def spec_for(f):
            assert f in sprops, f"{c['name']}.{f} not in schema"
            kind, etbl, dflt = classify(
                c["name"], f, sprops[f], enum_ids, props.get(f, (0, False))[1]
            )
            return (f, kind, etbl, dflt)

        specs = [spec_for(f) for f in fields]
        assert len(specs) <= 64, f"{c['name']}: presence mask exceeds u64"
        # Full form: the emitter materializes the complete schema
        # property set, so the full field list is every schema property.
        full_fields = sorted(k for k in sprops if k not in ("@id", "@type"))
        full_specs = [spec_for(f) for f in full_fields]
        assert len(full_specs) <= 192, f"{c['name']}: full presence bitmap cap"
        rows.append((c["name"], specs, full_specs))
    rows.sort()
    dupes = {n for i, (n, _, _) in enumerate(rows) if i and rows[i - 1][0] == n}
    if dupes:
        raise SystemExit(f"metaclass name collision: {dupes}")

    enum_names = sorted(enum_ids)
    lines = [
        "//! Generated from `spec-refs/{KerML,SysML}.xmi` +",
        "//! `spec-refs/{KerML,SysML}.schema.json` (normative, 20250201) by",
        "//! `tools/gen_cbor_tables.py` — do not edit. Field tables for the",
        "//! CBOR encoding of the compact interchange form: concrete",
        "//! metaclasses sorted by name (position = wire type code), fields",
        "//! sorted by name (position = wire ordinal), closed enum",
        "//! vocabularies in schema declaration order.",
        "",
        "/// Table layout version carried in the payload header; decoders",
        "/// refuse a version they were not generated for.",
        "pub const CBOR_TABLES_VERSION: u16 = 1;",
        "",
        "/// Boolean; default byte is 0 or 1.",
        "pub const K_BOOL: u8 = 0;",
        "/// Nullable text; presence bit means present-as-null.",
        "pub const K_STR: u8 = 1;",
        "/// Array of text; presence bit means present-and-empty.",
        "pub const K_STR_LIST: u8 = 2;",
        "/// Nullable element reference; presence bit means present-as-null.",
        "pub const K_REF: u8 = 3;",
        "/// Array of element references; presence bit means present-and-empty.",
        "pub const K_REF_LIST: u8 = 4;",
        "/// Closed vocabulary via `ENUM_TABLES`; default byte indexes the",
        "/// table, 255 = null.",
        "pub const K_ENUM: u8 = 5;",
        "/// Polymorphic literal value (bool/int/float/text); no default.",
        "pub const K_LITERAL: u8 = 6;",
        "/// UUID text; presence bit means it mirrors the element `@id`.",
        "pub const K_ELEMENT_ID: u8 = 7;",
        "",
        "/// `(property, kind, enum table index or 255, default byte)`.",
        "pub type CborField = (&'static str, u8, u8, u8);",
        "",
        "/// Enum vocabulary names, index-aligned with `ENUM_TABLES`.",
        f"pub static ENUM_NAMES: &[&str] = &{enum_names!r};".replace("'", '"'),
        "",
        "/// Enum vocabularies (values in schema declaration order).",
        "pub static ENUM_TABLES: &[&[&str]] = &[",
    ]
    for n in enum_names:
        vals = ", ".join(f'"{v}"' for v in enum_ids[n])
        lines.append(f"    &[{vals}], // {n}")
    lines += [
        "];",
        "",
        "/// Concrete metaclasses (sorted; position = wire type code) with",
        "/// their **compact-form** field tables (sorted; position = wire",
        "/// ordinal): the non-derived property closure.",
        "pub static METACLASS_FIELDS: &[(&str, &[CborField])] = &[",
    ]
    for name, specs, _ in rows:
        lines.append(f'    ("{name}", &[')
        for f, kind, etbl, dflt in specs:
            lines.append(f'        ("{f}", {kind}, {etbl}, {dflt}),')
        lines.append("    ]),")
    lines += [
        "];",
        "",
        "/// **Full-form** field tables, index-aligned with",
        "/// `METACLASS_FIELDS`: the complete schema property set (derived",
        "/// properties included) in its own ordinal space. Classes exceed",
        "/// 64 properties here, so full-form presence travels as a byte",
        "/// string when the field count requires it.",
        "pub static FULL_METACLASS_FIELDS: &[(&str, &[CborField])] = &[",
    ]
    for name, _, full_specs in rows:
        lines.append(f'    ("{name}", &[')
        for f, kind, etbl, dflt in full_specs:
            lines.append(f'        ("{f}", {kind}, {etbl}, {dflt}),')
        lines.append("    ]),")
    lines += ["];", ""]
    OUT.write_text("\n".join(lines))
    n_fields = sum(len(s) for _, s, _ in rows)
    n_full = sum(len(s) for _, _, s in rows)
    print(f"wrote {OUT.relative_to(ROOT)}: {len(rows)} metaclasses, "
          f"{n_fields} compact + {n_full} full fields, {len(enum_names)} enums")


if __name__ == "__main__":
    main()
