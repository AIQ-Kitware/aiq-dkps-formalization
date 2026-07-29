#!/usr/bin/env python3
"""Fail if any file outside `vendor/` declares into Spectra's namespace.

A DKPS theorem parked in `namespace Spectra.*` is indistinguishable from donor
material by name.  That is survivable while `import Spectra` is still in the
build and the file path says `Interop/Spectra/` — and it stops being survivable
the moment the dependency is removed, because then nothing at all points at the
donor and the attribution ledger silently credits Spectra for our work.

`AGENTS.md` ("Spectra collaboration and dependency policy") and `dev/LANES.md`
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

# Directories that are allowed to declare into the donor namespace: the vendored
# snapshot itself and the read-only upstream reference checkouts.
EXEMPT_PREFIXES = ("vendor/", "external/", ".lake/")


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
        if rel.startswith(EXEMPT_PREFIXES):
            continue
        for lineno, line in enumerate(strip_block_comments(path.read_text(errors="ignore")), 1):
            m = FORBIDDEN.match(line)
            if m:
                violations.append((rel, lineno, line.strip()))

    if violations:
        print("Declarations into Spectra's namespace from outside vendor/:", file=sys.stderr)
        for rel, lineno, text in violations:
            print(f"  {rel}:{lineno}: {text}", file=sys.stderr)
        print(
            "\nMove them into a DKPS namespace -- `TauCeti.DavisKahan.Experimental.SpectraBridge`\n"
            "is the convention used throughout DavisKahan/Interop/Spectra/.  See phase S0 of\n"
            "dev/tauceti/spectra-removal-plan.md.",
            file=sys.stderr,
        )
        return 1

    print("no declarations into Spectra's namespace outside vendor/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
