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
- the closed enum vocabularies (`*Kind`, schema declaration order),

and the same tables as data, spec-refs/cbor-tables.json, for readers
generated in other languages.

The tables are a pure function of the four spec inputs, so a reader
built from one toolkit release decodes every payload of another as long
as those inputs did not change. The generated file records a digest of
the inputs beside `CBOR_TABLES_VERSION`; a regeneration whose digest
differs from the committed one is refused unless it also bumps the
version (`--tables-version N`), so the header check stays honest.

Usage (from the workspace root):
  python3 tools/gen_cbor_tables.py                      regenerate both outputs
  python3 tools/gen_cbor_tables.py --tables-version 2   regenerate after a spec change
  python3 tools/gen_cbor_tables.py --check              fail when the outputs are stale (CI)
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import xmi_props as XP

ROOT = Path(__file__).resolve().parent.parent
SCHEMAS = [ROOT / "spec-refs" / "SysML.schema.json",
           ROOT / "spec-refs" / "KerML.schema.json"]
OUT = ROOT / "crates" / "sysmlv2-model" / "src" / "cbor_tables.rs"
OUT_JSON = ROOT / "spec-refs" / "cbor-tables.json"
KIND_NAMES = ["bool", "string", "stringList", "ref", "refList", "enum", "literal", "elementId"]

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


def source_digest():
    """SHA-256 over the four spec inputs, each folded to LF line ends and
    prefixed by its workspace-relative name, in name order."""
    h = hashlib.sha256()
    for path in sorted(list(XP.SOURCES) + SCHEMAS, key=lambda p: p.relative_to(ROOT).as_posix()):
        h.update(path.relative_to(ROOT).as_posix().encode())
        h.update(b"\0")
        h.update(path.read_bytes().replace(b"\r\n", b"\n"))
        h.update(b"\0")
    return h.hexdigest()


def committed_version_and_digest():
    """(version, digest) recorded in the committed Rust file, either None
    when the file or the constant is absent."""
    if not OUT.exists():
        return None, None
    text = OUT.read_text()
    version = re.search(r"pub const CBOR_TABLES_VERSION: u16 = (\d+);", text)
    digest = re.search(r'pub const CBOR_TABLES_SOURCE_DIGEST: &str = "([0-9a-f]+)";', text)
    return (int(version.group(1)) if version else None, digest.group(1) if digest else None)


def build_tables():
    """(rows, enum_ids): the metaclass rows `(name, compact specs, full
    specs)` sorted by name and the enum vocabularies."""
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
    return rows, enum_ids


def rustfmt(text):
    """The text as `cargo fmt` would leave it (the workspace's rustfmt.toml
    applies), so the committed file passes the formatting gate and `--check`
    compares like with like."""
    return subprocess.run(
        ["rustfmt", "--edition", "2021"],
        input=text,
        capture_output=True,
        text=True,
        check=True,
        cwd=ROOT,
    ).stdout


def render_rust(rows, enum_ids, version, digest):
    enum_names = sorted(enum_ids)
    lines = [
        "//! Generated from `spec-refs/{KerML,SysML}.xmi` +",
        "//! `spec-refs/{KerML,SysML}.schema.json` (normative, 20250201) by",
        "//! `tools/gen_cbor_tables.py` — do not edit. Field tables for the",
        "//! CBOR encoding of the compact interchange form: concrete",
        "//! metaclasses sorted by name (position = wire type code), fields",
        "//! sorted by name (position = wire ordinal), closed enum",
        "//! vocabularies in schema declaration order. The same tables as",
        "//! data: `spec-refs/cbor-tables.json`.",
        "",
        "/// Table layout version carried in the payload header; decoders",
        "/// refuse a version they were not generated for. The tables are a",
        "/// pure function of the spec inputs, so this changes only when they",
        "/// do: the generator refuses to keep it over a changed",
        "/// `CBOR_TABLES_SOURCE_DIGEST` without `--tables-version`.",
        f"pub const CBOR_TABLES_VERSION: u16 = {version};",
        "",
        "/// SHA-256 over the four spec inputs the tables were generated from",
        "/// (CRLF folded to LF; see `source_digest` in the generator).",
        f'pub const CBOR_TABLES_SOURCE_DIGEST: &str = "{digest}";',
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
    return rustfmt("\n".join(lines))


def render_json(rows, enum_ids, version, digest):
    """The tables as data. Field entries are `[name, kind, enum, default]`
    with `kind` a name from `kinds`, `enum` an index into `enums` or null,
    and `default` the default byte (an enum index, 255 = null, for enum
    fields; 0/1 for booleans; 0 otherwise). Metaclass position is the wire
    type code; field position is the wire ordinal."""
    enum_names = sorted(enum_ids)

    def field(f, kind, etbl, dflt):
        return json.dumps([f, KIND_NAMES[kind], None if etbl == NO_ENUM else etbl, dflt])

    out = [
        "{",
        '  "generator": "tools/gen_cbor_tables.py",',
        f'  "tablesVersion": {version},',
        f'  "sourceDigest": "{digest}",',
        '  "sources": ' + json.dumps(sorted(p.relative_to(ROOT).as_posix() for p in list(XP.SOURCES) + SCHEMAS)) + ",",
        '  "kinds": ' + json.dumps(KIND_NAMES) + ",",
        '  "enums": [',
    ]
    for i, n in enumerate(enum_names):
        out.append(f'    {{"name": {json.dumps(n)}, "values": {json.dumps(enum_ids[n])}}}' + ("," if i + 1 < len(enum_names) else ""))
    out += ["  ],", '  "metaclasses": [']
    for i, (name, specs, full_specs) in enumerate(rows):
        out.append("    {")
        out.append(f'      "name": {json.dumps(name)},')
        out.append(f'      "typeCode": {i},')
        out.append('      "compactFields": [')
        out += [f"        {field(*s)}" + ("," if j + 1 < len(specs) else "") for j, s in enumerate(specs)]
        out.append("      ],")
        out.append('      "fullFields": [')
        out += [f"        {field(*s)}" + ("," if j + 1 < len(full_specs) else "") for j, s in enumerate(full_specs)]
        out.append("      ]")
        out.append("    }" + ("," if i + 1 < len(rows) else ""))
    out += ["  ]", "}", ""]
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="compare the outputs with the committed files and exit 1 when they differ")
    ap.add_argument("--tables-version", type=int, help="the CBOR_TABLES_VERSION to write; required when the spec inputs changed")
    args = ap.parse_args()

    for path in list(XP.SOURCES) + SCHEMAS:
        XP.require(path)
    committed_version, committed_digest = committed_version_and_digest()
    digest = source_digest()
    rows, enum_ids = build_tables()

    if args.check:
        if args.tables_version is not None:
            raise SystemExit("--check takes no --tables-version")
        version = committed_version if committed_version is not None else 1
        stale = []
        if (OUT.read_text() if OUT.exists() else None) != render_rust(rows, enum_ids, version, digest):
            stale.append(OUT.relative_to(ROOT).as_posix())
        if (OUT_JSON.read_text() if OUT_JSON.exists() else None) != render_json(rows, enum_ids, version, digest):
            stale.append(OUT_JSON.relative_to(ROOT).as_posix())
        if stale:
            hint = ""
            if committed_digest is not None and committed_digest != digest:
                hint = "; the spec inputs changed, so regenerate with --tables-version " + str(version + 1)
            print(f"stale: {', '.join(stale)} (regenerate with tools/gen_cbor_tables.py{hint})", file=sys.stderr)
            return 1
        print("cbor tables are fresh")
        return 0

    if args.tables_version is not None:
        if committed_version is not None and args.tables_version <= committed_version:
            raise SystemExit(f"--tables-version must exceed the committed version {committed_version}")
        version = args.tables_version
    else:
        version = committed_version if committed_version is not None else 1
        if committed_digest is not None and committed_digest != digest:
            raise SystemExit(
                "the spec inputs changed since the committed tables were generated "
                f"(digest {committed_digest[:12]}… → {digest[:12]}…); decoders key on "
                f"CBOR_TABLES_VERSION, so rerun with --tables-version {version + 1}"
            )

    OUT.write_text(render_rust(rows, enum_ids, version, digest))
    OUT_JSON.write_text(render_json(rows, enum_ids, version, digest))
    n_fields = sum(len(s) for _, s, _ in rows)
    n_full = sum(len(s) for _, _, s in rows)
    print(f"wrote {OUT.relative_to(ROOT)} and {OUT_JSON.relative_to(ROOT)}: {len(rows)} metaclasses, "
          f"{n_fields} compact + {n_full} full fields, {len(enum_ids)} enums, "
          f"tables version {version}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
