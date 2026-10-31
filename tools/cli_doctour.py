#!/usr/bin/env python3
"""Run CLI.md's worked tour.

Walks CLI.md in order. A ```sysml block whose info string names a file
(```sysml rig.sysml) writes that file, so later commands read what the
reader was shown. Every ```console block runs: each `$ ` line (with the
lines a here-document, an open quote or a trailing backslash carry) is
one command, and its output, stdout and stderr together, must match the
lines that follow it up to the next command. `...` in the expected
output matches any text, across lines, as in a doctest; trailing spaces
and trailing blank lines are not compared. A block tagged
```console ignore is shown, not run: it needs something the tour cannot
provide (another tool, the network, a step done by hand).

All blocks share one shell session, so variables, exports and files
carry from block to block as they would for a reader typing along. The
session runs in a fresh directory where `spec-refs` points at this
checkout's and `target/release/sysmlv2` at the binary under test, and
the tour's own `cargo build` command is skipped. The library cache goes
to a temporary directory, and no SYSMLV2_* setting of the caller's
leaks in.

Needs bash, python3, jq and xxd, and z3 for the solver example.
"""

import argparse
import difflib
import doctest
import os
import pathlib
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading

MARK = "__cli_doctour_done__"
FENCE = re.compile(r"^```(\S*)\s*(.*?)\s*$")
HEREDOC = re.compile(r"<<-?\s*(['\"]?)([A-Za-z_][A-Za-z0-9_]*)\1")


def blocks(text):
    """(kind, info, first body line number, body lines) for each fence."""
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if m and m.group(1):
            start = i + 1
            j = start
            while j < len(lines) and lines[j].rstrip() != "```":
                j += 1
            yield m.group(1), m.group(2).split(), start + 1, lines[start:j]
            i = j
        i += 1


def incomplete(command):
    """Whether bash would still be waiting for more of `command`."""
    if command.endswith("\\"):
        return True
    check = subprocess.run(["bash", "-n", "-c", command], capture_output=True, text=True)
    # Bash words an unclosed quote either way, depending on its version.
    return check.returncode != 0 and ("unexpected EOF" in check.stderr or "unexpected end of file" in check.stderr)


def commands(body, first_line):
    """(line number, command, expected output, its first line number) per `$ ` line."""
    out = []
    i = 0
    while i < len(body):
        if not body[i].startswith("$ "):
            if body[i].strip():
                raise SyntaxError(f"CLI.md:{first_line + i}: output before any command")
            i += 1
            continue
        line_no = first_line + i
        command = body[i][2:]
        i += 1
        heredoc = HEREDOC.search(command)
        if heredoc:
            terminator = heredoc.group(2)
            while i < len(body):
                command += "\n" + body[i]
                i += 1
                if body[i - 1].strip() == terminator:
                    break
        else:
            while incomplete(command) and i < len(body):
                command += "\n" + body[i]
                i += 1
        expected = []
        expected_line = first_line + i
        while i < len(body) and not body[i].startswith("$ "):
            expected.append(body[i])
            i += 1
        out.append((line_no, command, expected, expected_line))
    return out


def normalize(lines):
    lines = [line.rstrip() for line in lines]
    while lines and not lines[-1]:
        lines.pop()
    return "".join(line + "\n" for line in lines)


class Shell:
    """One bash session; `run` returns a command's combined output."""

    def __init__(self, cwd, env):
        self.proc = subprocess.Popen(
            ["bash", "--noprofile", "--norc"],
            cwd=cwd,
            env=env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        self.lines = queue.Queue()
        threading.Thread(target=self._pump, daemon=True).start()

    def _pump(self):
        for raw in self.proc.stdout:
            self.lines.put(raw.decode("utf-8", errors="replace"))
        self.lines.put(None)

    def run(self, command, timeout):
        # A comment alone is no command (and inside the braces below, a
        # syntax error, which ends a non-interactive shell).
        if command.lstrip().startswith("#") and "\n" not in command:
            return []
        # Braces keep assignments and exports in this session; stdin from
        # /dev/null keeps a command from reading the rest of the script.
        # The marker restores `$?` so a following `echo $?` sees it.
        script = (
            "{\n" + command + "\n} </dev/null\n"
            f"__rc=$?; printf '\\n{MARK}\\n'; (exit $__rc)\n"
        )
        self.proc.stdin.write(script.encode("utf-8"))
        self.proc.stdin.flush()
        got = []
        while True:
            try:
                line = self.lines.get(timeout=timeout)
            except queue.Empty:
                raise TimeoutError(f"no result within {timeout} s") from None
            if line is None:
                raise RuntimeError("the shell exited")
            if line.rstrip("\n") == MARK:
                break
            got.append(line)
        text = "".join(got)
        # The marker's own leading newline ends the command's output.
        if text.endswith("\n"):
            text = text[:-1]
        return text.split("\n") if text else []


def main():
    root = pathlib.Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--bin", type=pathlib.Path, default=root / "target/release/sysmlv2", help="the sysmlv2 binary under test")
    parser.add_argument("--keep", action="store_true", help="keep the tour's working directory")
    parser.add_argument("--timeout", type=float, default=300, help="seconds one command may take")
    parser.add_argument("--accept", type=int, action="append", default=[], metavar="LINE", help="write the real output of the command on this CLI.md line into the document (repeatable); review the diff first")
    args = parser.parse_args()
    if not args.bin.is_file():
        print(f"{args.bin}: no such binary (cargo build --release -p sysmlv2-cli)", file=sys.stderr)
        return 2

    work = pathlib.Path(tempfile.mkdtemp(prefix="cli-tour-"))
    (work / "spec-refs").symlink_to(root / "spec-refs")
    (work / "target/release").mkdir(parents=True)
    (work / "target/release/sysmlv2").symlink_to(args.bin.resolve())
    cache = work / ".cache"
    cache.mkdir()
    env = {k: v for k, v in os.environ.items() if not k.startswith("SYSMLV2_")}
    env.update(SYSMLV2_CACHE_DIR=str(cache), LC_ALL="C.UTF-8", NO_COLOR="1")
    shell = Shell(work, env)

    text = (root / "CLI.md").read_text(encoding="utf-8")
    checker = doctest.OutputChecker()
    ran = failed = ignored = 0
    accepted = {}
    for kind, info, first_line, body in blocks(text):
        if kind == "sysml" and info:
            path = work / info[0]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("\n".join(body) + "\n", encoding="utf-8")
            continue
        if kind != "console":
            continue
        if "ignore" in info:
            ignored += 1
            continue
        for line_no, command, expected, expected_line in commands(body, first_line):
            if command.startswith("cargo build"):
                continue
            ran += 1
            try:
                got = normalize(shell.run(command, args.timeout))
            except (TimeoutError, RuntimeError) as e:
                print(f"CLI.md:{line_no}: $ {command.splitlines()[0]}\n    {e}")
                print(f"working directory kept: {work}")
                return 1
            want = normalize(expected)
            if checker.check_output(want, got, doctest.ELLIPSIS):
                continue
            if line_no in args.accept:
                accepted[expected_line] = (expected, got)
                continue
            failed += 1
            print(f"CLI.md:{line_no}: $ {command.splitlines()[0]}")
            diff = difflib.unified_diff(want.splitlines(), got.splitlines(), "expected", "got", lineterm="")
            print("\n".join("    " + d for d in diff) + "\n")

    if accepted:
        # Bottom up, so earlier line numbers stay valid; the blank lines
        # that separate one command's output from the next stay.
        lines = text.split("\n")
        for start in sorted(accepted, reverse=True):
            expected, got = accepted[start]
            blanks = len(expected) - len(normalize(expected).splitlines())
            lines[start - 1 : start - 1 + len(expected)] = got.splitlines() + [""] * blanks
        (root / "CLI.md").write_text("\n".join(lines), encoding="utf-8")
        print(f"accepted the real output of {len(accepted)} command(s) into CLI.md")
    if args.keep or failed:
        print(f"working directory kept: {work}")
    else:
        shutil.rmtree(work)
    print(f"CLI.md tour: {ran} commands, {failed} failed, {ignored} block(s) ignored")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
