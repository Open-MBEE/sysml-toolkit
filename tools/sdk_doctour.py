#!/usr/bin/env python3
"""Run SDK.md's worked tour.

Extracts every ```pycon block from SDK.md and executes them as a single
doctest over one shared namespace, so each output shown in the document
is checked against the real one. Requires the `sysmlv2` module (build
with `maturin develop` in crates/sysmlv2-py).
"""

import doctest
import pathlib
import re
import sys


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    text = (root / "SDK.md").read_text(encoding="utf-8")
    blocks = re.findall(r"```pycon\n(.*?)```", text, re.S)
    if not blocks:
        print("SDK.md: no pycon blocks found", file=sys.stderr)
        return 2
    parser = doctest.DocTestParser()
    test = parser.get_doctest("\n".join(blocks), {}, "SDK.md", "SDK.md", 0)
    runner = doctest.DocTestRunner()
    runner.run(test)
    summary = runner.summarize(verbose=False)
    print(f"SDK.md tour: {summary.attempted} examples, {summary.failed} failed")
    return 1 if summary.failed else 0


if __name__ == "__main__":
    sys.exit(main())
