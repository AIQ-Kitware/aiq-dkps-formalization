#!/usr/bin/env python3
"""Make source docstrings lead the Lean Source tab, open but collapsible.

This is a narrow source transformation so it composes with upstream viewer work.
It refuses to rewrite an unknown layout rather than replacing the whole viewer.
"""
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys


def repo_root() -> pathlib.Path:
    return pathlib.Path(
        subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
    )


OLD = """return `<pre>${leanHl(declaration)}</pre>`
             + `<details><summary>source docstring</summary><pre>${leanHl(doc)}</pre></details>`;"""
NEW = """return `<details class=\"source-docstring\" open><summary>source docstring</summary><pre>${leanHl(doc)}</pre></details>`
             + `<pre>${leanHl(declaration)}</pre>`;"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "viewer",
        nargs="?",
        default="submodules/aiq-lean-formalization-tools/src/aiq_lean_tools/assets/alignment_viewer.html",
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    path = pathlib.Path(args.viewer)
    if not path.is_absolute():
        path = root / path
    text = path.read_text(encoding="utf-8")

    if NEW in text:
        print(f"already current: {path}")
        return 0
    count = text.count(OLD)
    if count != 1:
        raise RuntimeError(
            f"expected exactly one known source-docstring layout in {path}; found {count}. "
            "The viewer changed upstream, so re-read it instead of replacing it wholesale."
        )
    updated = text.replace(OLD, NEW, 1)
    if args.dry_run:
        import difflib
        sys.stdout.writelines(
            difflib.unified_diff(
                text.splitlines(True), updated.splitlines(True),
                fromfile=str(path), tofile=str(path) + " (updated)",
            )
        )
        return 0
    path.write_text(updated, encoding="utf-8")
    print(f"updated source-docstring layout: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
