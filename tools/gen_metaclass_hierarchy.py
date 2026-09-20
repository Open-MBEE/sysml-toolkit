#!/usr/bin/env python3
"""Generate metaclass conformance from the pinned KerML/SysML XMI.

The output is a sorted name table plus one ancestor bit set per metaclass, so
a conformance test is two generated name dispatches and a bit test. The same ancestor
sets are also emitted as name lists under `cfg(test)` for the differential
test that pins the bit table against them.
"""
import argparse
import subprocess
import sys
from pathlib import Path
sys.dont_write_bytecode = True
from xmi_props import load, SOURCES

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "crates/sysmlv2-model/src/metaclass.rs"


def hierarchy():
    """Sorted `(name, sorted strict-ancestor names)` pairs."""
    classes = {}
    for source in SOURCES:
        classes.update(load(source, {}))
    def ancestors(cid, active):
        if cid in active:
            raise ValueError(f"cyclic metaclass inheritance: {cid}")
        row = classes[cid]
        out = {row["name"]}
        for parent in row["generals"]:
            out.update(ancestors(parent, active | {cid}))
        return out
    rows = []
    for cid, row in sorted(classes.items(), key=lambda item: item[1]["name"]):
        rows.append((row["name"], sorted(ancestors(cid, set()) - {row["name"]})))
    names = [name for name, _ in rows]
    if len(set(names)) != len(names):
        raise ValueError("metaclass name collision across files")
    return rows


def generate():
    rows = hierarchy()
    index = {name: i for i, (name, _) in enumerate(rows)}
    n = len(rows)
    words = (n + 63) // 64
    lines = [
        "//! Generated from the pinned `spec-refs/{KerML,SysML}.xmi` by",
        "//! `tools/gen_metaclass_hierarchy.py`; do not edit.",
        "//!",
        "//! Abstract-syntax inheritance, distinct from a model element's declared",
        "//! specializations. Used to validate the kinds of explicit typing targets.",
        "//!",
        "//! `NAMES` holds every metaclass in sorted order and `ANCESTORS[i]` the",
        "//! bit set, over that same order, of the metaclasses `NAMES[i]` strictly",
        "//! specializes; a conformance test is two generated name dispatches and a bit test.",
        "",
        f"const COUNT: usize = {n};",
        f"const WORDS: usize = {words};",
        "",
        "/// Every metaclass name, in stable index order.",
        "const NAMES: [&str; COUNT] = [",
    ]
    lines += [f'    "{name}",' for name, _ in rows]
    lines += [
        "];",
        "",
        "/// Strict ancestors of `NAMES[i]`, as a bit set in `NAMES` order.",
        "const ANCESTORS: [[u64; WORDS]; COUNT] = [",
    ]
    for _, parents in rows:
        bits = [0] * words
        for parent in parents:
            j = index[parent]
            bits[j // 64] |= 1 << (j % 64)
        lines.append("    [" + ", ".join(f"0x{b:016x}" for b in bits) + "],")
    lines += [
        "];",
        "",
        "fn index(name: &str) -> Option<usize> {",
        "    match name {",
    ]
    lines += [f'        "{name}" => Some({i}),' for i, (name, _) in enumerate(rows)]
    lines += [
        "        _ => None,",
        "    }",
        "}",
        "",
        "pub(crate) fn conforms(specific: &str, general: &str) -> bool {",
        "    if specific == general {",
        "        return true;",
        "    }",
        "    let (Some(s), Some(g)) = (index(specific), index(general)) else {",
        "        return false;",
        "    };",
        "    ANCESTORS[s][g / 64] >> (g % 64) & 1 == 1",
        "}",
        "",
        "pub(crate) fn canonical_name(name: &str) -> Option<&'static str> {",
        "    index(name).map(|i| NAMES[i])",
        "}",
        "",
        "/// The same hierarchy as name lists: `(metaclass, strict ancestors)`,",
        "/// for the test that pins the bit table.",
        "#[cfg(test)]",
        "pub(crate) const ANCESTOR_NAMES: [(&str, &[&str]); COUNT] = [",
    ]
    for name, parents in rows:
        listed = ", ".join(f'"{p}"' for p in parents)
        lines.append(f'    ("{name}", &[{listed}]),')
    lines += ["];", ""]
    source = "\n".join(lines)
    return subprocess.run(["rustfmt", "--edition", "2021"], input=source,
                          text=True, capture_output=True, check=True).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = generate()
    if args.check:
        if OUTPUT.read_text() != text:
            raise SystemExit(f"stale generated file: {OUTPUT}")
    else:
        OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
