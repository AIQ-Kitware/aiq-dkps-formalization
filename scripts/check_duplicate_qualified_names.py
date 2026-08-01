#!/usr/bin/env python3
"""One fully-qualified declaration name must come from one module.

**This gate exists because the repository already contained the defect it checks for, and
nothing else could see it.**  On 2026-08-01, `ForTauCeti` held **two** structures called
`TauCeti.SymmetricGauge` -- `Analysis/OperatorIdeal/SymmetricGauge.lean` (1141 lines) and
`Analysis/Normed/SymmetricGauge.lean` (831 lines) -- field-for-field identical down to
their docstrings, differing only in primed against unprimed field names.  Fourteen
fully-qualified names were declared twice, including the structure itself, `extend`,
`ofFin` and `truncate`.

**It compiled, and would have gone on compiling.**  `ForTauCeti` is glob-built, so both
modules are built; nothing forces them into one file, and no module happened to import
both.  The first module that imports both finds `TauCeti.SymmetricGauge` ambiguous -- and
that failure surfaces at a call site far from either definition.

Nothing else looks: `check_private_shadows_public` skips it because both are public, and
the name-drift and merge-loss gates compare against history rather than across the tree.
Two agents building the same abstraction in parallel is exactly what the lane protocol is
for, and the protocol did not prevent it, so a mechanical check is the backstop.

**Comments must be stripped before parsing**, or prose supplies false positives: an
un-stripped scan reported `TauCeti.needs` from the sentences *"instance needs
`CompleteSpace E`"* and *"lemma needs; ..."*.

`private` declarations are exempt: they are module-local by construction, and
`check_private_shadows_public` already owns the question of a private shadowing a public.

    python3 scripts/check_duplicate_qualified_names.py
    python3 scripts/check_duplicate_qualified_names.py --check   # exit 1 ABOVE the baseline
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

#: `Experimental/` is open research and duplicates production names on purpose; the
#: `DK-EXPDUP` lane tracks those separately and by a different rule.
EXCLUDED_PARTS = {"Experimental"}

#: Libraries whose declarations share one namespace tree and must not collide.
SCOPES = ("ForTauCeti", "DavisKahan")

#: **Zero, since 2026-08-01.**  It was 14 for one day: `ForTauCeti` held two structures
#: called `TauCeti.SymmetricGauge`, and the ratchet existed so that a SECOND collision would
#: fail the suite while that one was being resolved.  It was resolved by renaming the
#: orphaned module's structure to `TruncationGauge` -- the gate's own advice, "qualify them
#: into distinct namespaces" -- which was safe because nothing imported that module and
#: because `check_roadmap_delivered` indexes final components, so its 163/191 was unchanged.
#:
#: **The number may only fall, and it has reached the floor.**  Any finding now is a new
#: collision, and it fails immediately.
DUPLICATE_BASELINE = 0

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*?$", re.M)

NAMESPACE = re.compile(r"^\s*(namespace|end)\s+([A-Za-z_][\w.'′]*)\s*$")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(private)\s+)?(?:protected\s+|noncomputable\s+|public\s+|scoped\s+|partial\s+)*"
    r"(theorem|lemma|def|structure|instance|abbrev|class|inductive)\s+"
    r"([A-Za-z_][\w.'′!?]*)")


def strip_comments(text: str) -> str:
    """Block comments FIRST: a docstring may contain `--`, and removing line comments
    first would eat the `-/` that closes it."""
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def declarations(path: pathlib.Path) -> set[str]:
    """Fully-qualified, non-private declaration names in `path`."""
    stack: list[str] = []
    out: set[str] = set()
    for line in strip_comments(path.read_text(errors="ignore")).splitlines():
        ns = NAMESPACE.match(line)
        if ns:
            if ns.group(1) == "namespace":
                stack.append(ns.group(2))
            elif stack and stack[-1] == ns.group(2):
                stack.pop()
            # An `end` for a `section` name, or a mismatched one, is left alone rather
            # than guessed at: popping on a name we never pushed corrupts every later
            # qualification in the file.
            continue
        d = DECL.match(line)
        if d and not d.group(1):
            out.add(".".join(stack + [d.group(3)]))
    return out


def lean_files(scope: str) -> list[pathlib.Path]:
    return sorted(p for p in (ROOT / scope).rglob("*.lean")
                  if not EXCLUDED_PARTS & set(p.relative_to(ROOT).parts))


def offenders() -> dict[str, list[str]]:
    where: dict[str, set[str]] = collections.defaultdict(set)
    for scope in SCOPES:
        for path in lean_files(scope):
            rel = path.relative_to(ROOT).as_posix()
            for name in declarations(path):
                where[name].add(rel)
    return {n: sorted(fs) for n, fs in where.items() if len(fs) > 1}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the count rises above DUPLICATE_BASELINE")
    args = ap.parse_args(argv)

    found = offenders()
    for name in sorted(found):
        print(f"  DUPLICATE  {name}")
        for rel in found[name]:
            print(f"               {rel}")
    modules = sorted({m for fs in found.values() for m in fs})
    print(f"\nduplicate qualified names: {len(found)} across {len(modules)} module(s)"
          f" (baseline {DUPLICATE_BASELINE})")
    if len(found) < DUPLICATE_BASELINE:
        print(f"  BELOW the baseline -- lower DUPLICATE_BASELINE to {len(found)}.")
    if found:
        print("  A name declared in two modules compiles only while nothing imports both.")
        print("  The first module that does gets an ambiguous name, at a call site far")
        print("  from either definition. Retire one, or qualify them into distinct")
        print("  namespaces -- do not rename one field and leave both.")
    if len(found) > DUPLICATE_BASELINE:
        print(f"  ABOVE the baseline of {DUPLICATE_BASELINE}: a NEW collision was added.")
    return 1 if (args.check and len(found) > DUPLICATE_BASELINE) else 0


if __name__ == "__main__":
    sys.exit(main())
