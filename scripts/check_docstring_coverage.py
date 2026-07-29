#!/usr/bin/env python3
"""Gate: every public declaration on the submission surface carries a docstring.

Docstrings are a Tau Ceti reviewer gate, and until now they were the only quality
invariant in this repository without a check.  Measured 2026-07-29: two sweep lanes
drove `ForTauCeti/**` and production `DavisKahan/**` to zero undocumented, and other
agents' merges put the count back to six within the hour.  A sweep cannot hold that
line; this can.

Three things this check gets right that a naive scan does not.  Each cost a real
mistake before it was written down:

1.  **Block-comment depth is tracked.**  A module docstring whose prose wraps so that
    a line begins with `theorem`, `instance`, `structure` or `lemma` at column 0 is
    NOT a declaration.  Ignoring this inflated the reported `ForTauCeti` figure from
    46 to 96 -- roughly 50% -- and those inflated numbers were published before the
    cause was found.

2.  **Anonymous instances are reported.**  `instance : Foo Bar := ...` has no name, so
    any scan that keys on declaration names silently skips it.  Six of the 91
    declarations in one lane were anonymous.

3.  **Exclusions are by rule, not by hand-list**, so they stay correct as the tree
    moves.  In particular `SpectralTheory/Compatibility.lean` is deliberately
    excluded: it is a migration shim of `abbrev` re-exports kept so literature
    scaffolds keep compiling, and documenting its 45 declarations would entrench a
    file that is scheduled for deletion.

Usage:
    python3 scripts/check_docstring_coverage.py            # gate; exit 1 on findings
    python3 scripts/check_docstring_coverage.py --list     # show each finding
    python3 scripts/check_docstring_coverage.py --json     # machine-readable
    python3 scripts/check_docstring_coverage.py --write-baseline
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
BASELINE = REPO / "dev" / "docstring-coverage-baseline.json"

# Trees on the submission surface.  Anything not listed here is out of scope.
ROOTS = ["ForTauCeti", "DavisKahan"]

# Excluded by rule.  Each entry is a reason, not a convenience.
EXCLUDED = [
    # Outside `defaultTargets`; deliberately parked (see dev/LANES.md).
    (re.compile(r"^DavisKahan/Experimental/"), "outside defaultTargets, parked"),
    # Being deleted wholesale by the Spectra-removal campaign.
    (re.compile(r"^DavisKahan/Interop/Spectra/"), "Spectra removal deletes this tree"),
    # Migration shim: documenting it would entrench a file scheduled for deletion.
    (re.compile(r"^DavisKahan/SpectralTheory/Compatibility\.lean$"),
     "migration shim of abbrev re-exports; delete, do not document"),
]

KEYWORDS = "theorem|lemma|def|abbrev|instance|structure|class|opaque|axiom"
# 4.  **An inline attribute prefix is matched.**  `@[simp] theorem foo ...` on a
#     single line is the dominant style in this repository, and an attribute
#     bracket is not a modifier -- so anchoring the keyword after modifiers alone
#     made the scanner skip such lines ENTIRELY rather than report them.  That is
#     the worst failure mode available to a gate: it reported `OK` over 158
#     undocumented declarations across 59 files, including ones in modules that
#     had landed the same day.  A gate that reports green stops people looking.
DECL = re.compile(
    r"^(?P<attr>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:noncomputable\s+|partial\s+|protected\s+|scoped\s+|unsafe\s+)*)"
    r"(?P<private>private\s+)?"
    rf"(?P<kw>{KEYWORDS})\b"
    r"\s*(?P<name>[^\s({\[:]*)"
)
# Lines that may sit between a docstring and the declaration it documents.
SKIP = re.compile(r"^\s*(@\[|omit\b|set_option\b|open\b|variable\b|attribute\b|--|$)")


def excluded(rel: str) -> str | None:
    for pat, why in EXCLUDED:
        if pat.search(rel):
            return why
    return None


def comment_mask(lines: list[str]) -> list[bool]:
    """True where a line sits strictly inside a `/- ... -/` block.

    `/--` counts as one `/-`, so a one-line docstring nets to zero and the
    declaration beneath it is never masked.
    """
    depth, mask = 0, []
    for line in lines:
        mask.append(depth > 0)
        depth += line.count("/-") - line.count("-/")
        depth = max(depth, 0)
    return mask


def module_docstring(lines: list[str], end: int) -> bool:
    """Does the comment block ending at `lines[end]` open with `/-!` ?

    Lean distinguishes a *declaration* docstring `/-- ... -/` from a *module or
    section* docstring `/-! ... -/`.  The latter documents the file or the
    section, **not** whatever declaration happens to follow it, so treating it as
    documentation is a false negative: a declaration written directly under a
    `/-! ## Heading -/` was silently counted as documented.  Seven declarations
    in the submission surface were passing for that reason.
    """
    depth, k = 0, end
    while k >= 0:
        depth += lines[k].count("-/") - lines[k].count("/-")
        if depth <= 0:
            return lines[k].lstrip().startswith("/-!")
        k -= 1
    return False


def scan(path: pathlib.Path, rel: str) -> list[dict]:
    lines = path.read_text().split("\n")
    mask = comment_mask(lines)
    out = []
    for i, line in enumerate(lines):
        if mask[i]:
            continue
        m = DECL.match(line)
        if not m or m.group("private"):
            continue
        j = i - 1
        while j >= 0 and SKIP.match(lines[j]) and not lines[j].rstrip().endswith("-/"):
            j -= 1
        if j >= 0 and lines[j].rstrip().endswith("-/") and not module_docstring(lines, j):
            continue
        name = m.group("name") or ""
        out.append({
            "file": rel,
            "line": i + 1,
            "kind": m.group("kw"),
            # An unnamed instance is legal and is exactly the case a name-based
            # scan misses, so report it explicitly rather than dropping it.
            "name": name if name else "<anonymous>",
        })
    return out


def collect() -> list[dict]:
    findings = []
    for root in ROOTS:
        for path in sorted((REPO / root).rglob("*.lean")):
            rel = path.relative_to(REPO).as_posix()
            if excluded(rel):
                continue
            findings.extend(scan(path, rel))
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--list", action="store_true", help="print every finding")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--write-baseline", action="store_true",
                    help="record the current findings as tolerated")
    args = ap.parse_args()

    findings = collect()

    if args.write_baseline:
        BASELINE.parent.mkdir(parents=True, exist_ok=True)
        BASELINE.write_text(json.dumps(
            {"tolerated": [f"{f['file']}:{f['name']}" for f in findings]},
            indent=2) + "\n")
        print(f"baseline written: {len(findings)} tolerated -> "
              f"{BASELINE.relative_to(REPO)}")
        return 0

    tolerated = set()
    if BASELINE.exists():
        tolerated = set(json.loads(BASELINE.read_text()).get("tolerated", []))

    new = [f for f in findings if f"{f['file']}:{f['name']}" not in tolerated]

    if args.json:
        print(json.dumps({"findings": findings, "new": new,
                          "tolerated": len(tolerated)}, indent=2))
        return 1 if new else 0

    if args.list or new:
        for f in (new if new else findings):
            print(f"  {f['file']}:{f['line']}  {f['kind']} {f['name']}")

    anon = sum(1 for f in findings if f["name"] == "<anonymous>")
    print(f"docstring-coverage check: {len(findings)} undocumented "
          f"({anon} anonymous), {len(tolerated)} tolerated by baseline, "
          f"{len(new)} new")
    if new:
        print("Undocumented public declarations above are not in the baseline. "
              "Document them, mark them `private`, or -- if the file should not be "
              "documented at all -- add an exclusion rule with a reason.")
        return 1
    print("docstring-coverage check: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
