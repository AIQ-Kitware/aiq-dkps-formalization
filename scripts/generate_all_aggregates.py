#!/usr/bin/env python3
"""Regenerate the import-only `All.lean` aggregate of every production directory.

Each directory's aggregate imports every module in that directory plus the
aggregate of each immediate subdirectory, so that `DavisKahan.All` reaches the
whole production tree by construction rather than by hand-maintained lists.

Experimental directories are left alone: their aggregates are curated by hand
because they must keep tracking which obligations remain open.
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / "DavisKahan"
SKIP_DIRS = {"Experimental"}

HEADER = """/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
"""


def module_of(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def is_skipped(d: pathlib.Path) -> bool:
    return any(part in SKIP_DIRS for part in d.relative_to(ROOT).parts)


def regenerate(d: pathlib.Path, check: bool = False) -> str | None:
    """Rewrite `d/All.lean` if it differs from the generated form.

    With `check`, report the difference without writing, so that CI can fail on
    an aggregate that a module addition left stale.
    """
    # `Audit.lean` imports its directory's aggregate in order to `#check` and
    # `#print axioms` the whole surface, so it can never be a member of that
    # aggregate without creating an import cycle.
    modules = sorted(module_of(p) for p in d.glob("*.lean")
                     if p.name not in ("All.lean", "Experimental.lean",
                                       "Audit.lean"))
    subs = sorted(module_of(s / "All.lean") for s in d.iterdir()
                  if s.is_dir() and not is_skipped(s)
                  and any(s.rglob("*.lean")))
    # the curated public root is the entry point of the developer umbrella
    head = ["DavisKahan"] if d == BASE else []
    imports = head + subs + modules
    if not imports:
        return None
    title = d.relative_to(ROOT).as_posix()
    text = (HEADER + "".join(f"import {m}\n" for m in imports)
            + f"\n/-! # `{title}` -/\n")
    out = d / "All.lean"
    if not out.exists() or out.read_text() != text:
        if not check:
            out.write_text(text)
        return module_of(out)
    return None


def main() -> None:
    check = "--check" in sys.argv[1:]
    changed = []
    # a directory needs an aggregate whenever anything beneath it is a module,
    # even if it holds no `.lean` file of its own
    dirs = [d for d in BASE.rglob("*")
            if d.is_dir() and not is_skipped(d) and any(d.rglob("*.lean"))]
    for d in sorted(dirs, key=lambda p: -len(p.parts)):
        c = regenerate(d, check)
        if c:
            changed.append(c)
    c = regenerate(BASE, check)
    if c:
        changed.append(c)
    verb = "stale" if check else "regenerated"
    for m in changed:
        print(f"  {verb} {m}")
    if check:
        if changed:
            print(f"{len(changed)} aggregate(s) stale; run without --check")
            raise SystemExit(1)
        print("aggregates up to date")
        return
    print(f"{len(changed)} aggregate(s) regenerated")


if __name__ == "__main__":
    main()
