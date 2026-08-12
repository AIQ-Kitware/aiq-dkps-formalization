#!/usr/bin/env python3
"""Fail if any production file declares into Spectra's namespace.

A DKPS theorem parked in `namespace Spectra.*` is indistinguishable from donor
material by name.  That is survivable while `import Spectra` is still in the
build and the file path says `Interop/Spectra/` — and it stops being survivable
the moment the dependency is removed, because then nothing at all points at the
donor and the attribution ledger silently credits Spectra for our work.

`AGENTS.md` ("Spectra collaboration and dependency policy")
both record the rule; this is the gate that enforces it.  Two files violated it
until 2026-07-28 — see phase S0 of `dev/tauceti/spectra-removal-plan.md`.

`namespace SpectraBridge` is the *correct* pattern and is not a violation: it is
a DKPS namespace whose name merely mentions Spectra.  Only `Spectra` itself and
its sub-namespaces are forbidden.

Usage:  python3 scripts/check_spectra_namespace.py [--repo PATH]
Exit 0 when clean, 1 with a per-occurrence report otherwise.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# `namespace Spectra`, `namespace Spectra.Foo.Bar` — but not `namespace SpectraBridge`.
FORBIDDEN = re.compile(r"^\s*namespace\s+(Spectra)(\.[A-Za-z0-9_.'₀-₉]+)?\s*$")

# Historical/recovery roots are exempt from the production namespace rule. The
# maintained tree no longer contains a vendored or external Spectra source tree,
# but keeping these prefixes explicit makes the checker safe on recovered old
# snapshots and on retirement artifacts without weakening production checks.
EXEMPT_PREFIXES = ("vendor/", "external/", "retired/")


def in_hidden_dir(rel: str) -> bool:
    """Is any component of `rel` a dot-directory?

    Structural, not a hand-list, because the hand-list was wrong the moment the
    tree grew a directory nobody had thought of.  This gate carried `.lake/` in
    `EXEMPT_PREFIXES`; when a subagent worktree appeared at `.claude/worktrees/`
    it brought ~1259 `.lean` files -- a second full checkout of this repo -- and
    the gate reported violations at paths like
    `.claude/worktrees/aiq-gpu-docs/retired/Spectra/...`, i.e. inside *another
    agent's* working copy, on a commit that changed no Lean source at all.

    Every dot-directory at the repo root is tooling state (`.lake`, `.git`,
    `.claude`), never submission surface, so the rule covers the next one too.
    """
    return any(part.startswith(".") for part in Path(rel).parts)


def strip_block_comments(text: str) -> list[str]:
    """Blank out `/- ... -/` regions, preserving line numbering.

    Needed because `namespace` occurs as an ordinary English word inside
    docstrings ("...the namespace from outside."), and a scanner that believes
    those reports phantom violations.
    """
    out, depth = [], 0
    for line in text.splitlines():
        rebuilt, i = [], 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if depth == 0:
                    rebuilt.append(line[i])
                i += 1
        out.append("".join(rebuilt))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    args = ap.parse_args()
    repo = args.repo

    violations: list[tuple[str, int, str]] = []
    for path in sorted(repo.rglob("*.lean")):
        rel = path.relative_to(repo).as_posix()
        if rel.startswith(EXEMPT_PREFIXES) or in_hidden_dir(rel):
            continue
        for lineno, line in enumerate(strip_block_comments(path.read_text(errors="ignore")), 1):
            m = FORBIDDEN.match(line)
            if m:
                violations.append((rel, lineno, line.strip()))

    if violations:
        print("Declarations into Spectra's namespace from production code:", file=sys.stderr)
        for rel, lineno, text in violations:
            print(f"  {rel}:{lineno}: {text}", file=sys.stderr)
        print(
            "\nMove them into a DKPS namespace.  File the declaration by what it is --\n"
            "spectral theory under `DavisKahan/SpectralTheory/`, geometry under\n"
            "`DavisKahan/Geometry/` -- not under a donor's name: `DavisKahan/Interop/Spectra/`\n"
            "was dissolved on 2026-07-30 for exactly that reason (lane DK-INTEROP).",
            file=sys.stderr,
        )
        return 1

    print("no declarations into Spectra's namespace in production code")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
