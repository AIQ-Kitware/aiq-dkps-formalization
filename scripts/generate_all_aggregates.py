#!/usr/bin/env python3
"""Regenerate the import-only `All.lean` aggregate of every production directory.

Each directory's aggregate imports every module in that directory plus the
aggregate of each immediate subdirectory, so that `DavisKahan.All` reaches the
whole production tree by construction rather than by hand-maintained lists.

Experimental directories are left alone: their aggregates are curated by hand
because they must keep tracking which obligations remain open.

**Cross-library re-exports are preserved.** Since the Tau Ceti migration an
aggregate legitimately imports modules that no longer live under `DavisKahan/` —
when a module moves to `ForTauCeti`, its import is repointed in place so the
aggregate keeps reaching the same mathematics. Those lines cannot be derived
from the directory contents, so they are read back out of the existing file and
merged in. Regenerating without them silently drops migrated modules from the
default build: 21 such imports across 9 aggregates as of 2026-07-29, and
nothing downstream would have reported their loss, because an aggregate that
imports less still compiles.

A preserved re-export whose target file has since disappeared is reported rather
than copied forward, so a deleted module cannot hide behind this rule.
"""
from __future__ import annotations

import argparse
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / "DavisKahan"
SKIP_DIRS = {"Experimental"}
OWN_LIBRARY = "DavisKahan"
IMPORT_RE = re.compile(r"^import\s+(\S+)\s*$", re.MULTILINE)

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


def module_path(module: str) -> pathlib.Path:
    """The source file a module name resolves to, within this repository."""
    return ROOT / (module.replace(".", "/") + ".lean")


def foreign_imports(out: pathlib.Path, dangling: list[str]) -> list[str]:
    """Cross-library imports to carry forward from an existing aggregate.

    Anything not under this library is a re-export of migrated mathematics and
    is not derivable from the directory listing, so it must be preserved. A
    preserved import whose file no longer exists is collected into `dangling`
    and dropped, rather than propagated.
    """
    if not out.exists():
        return []
    kept = []
    for module in IMPORT_RE.findall(out.read_text()):
        if module == OWN_LIBRARY or module.startswith(OWN_LIBRARY + "."):
            continue
        if module_path(module).exists():
            kept.append(module)
        else:
            dangling.append(f"{module_of(out)} -> {module}")
    return kept


def regenerate(d: pathlib.Path, check: bool = False,
               dangling: list[str] | None = None) -> str | None:
    """Rewrite `d/All.lean` if it differs from the generated form.

    With `check`, report the difference without writing, so that CI can fail on
    an aggregate that a module addition left stale.
    """
    out = d / "All.lean"
    modules = [module_of(p) for p in d.glob("*.lean")
               if p.name not in ("All.lean", "Experimental.lean")]
    # migrated modules re-exported from another library — see the module docstring
    modules += foreign_imports(out, dangling if dangling is not None else [])
    # sort on the leaf name so a re-export keeps the slot of the module it replaced
    modules.sort(key=lambda m: (m.rsplit(".", 1)[-1], m))
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
    if not out.exists() or out.read_text() != text:
        if not check:
            out.write_text(text)
        return module_of(out)
    return None


def main() -> None:
    # argparse, not a substring test on argv: the previous `"--check" in argv`
    # form treated every unrecognised argument -- `--help` included -- as
    # "not a check", so asking this tool for its usage rewrote 21 aggregates.
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="report stale aggregates without writing; exit 1 if any")
    args = parser.parse_args()
    check = args.check

    changed: list[str] = []
    dangling: list[str] = []
    # a directory needs an aggregate whenever anything beneath it is a module,
    # even if it holds no `.lean` file of its own
    dirs = [d for d in BASE.rglob("*")
            if d.is_dir() and not is_skipped(d) and any(d.rglob("*.lean"))]
    for d in sorted(dirs, key=lambda p: -len(p.parts)):
        c = regenerate(d, check, dangling)
        if c:
            changed.append(c)
    c = regenerate(BASE, check, dangling)
    if c:
        changed.append(c)
    verb = "stale" if check else "regenerated"
    for m in changed:
        print(f"  {verb} {m}")
    for d in dangling:
        print(f"  DANGLING re-export (dropped): {d}")
    if check:
        if changed or dangling:
            if changed:
                print(f"{len(changed)} aggregate(s) stale; run without --check")
            if dangling:
                print(f"{len(dangling)} cross-library re-export(s) name a missing file")
            raise SystemExit(1)
        print("aggregates up to date")
        return
    print(f"{len(changed)} aggregate(s) regenerated")


if __name__ == "__main__":
    main()
