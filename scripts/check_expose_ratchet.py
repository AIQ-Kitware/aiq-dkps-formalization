#!/usr/bin/env python3
"""Ratchet the number of `ForTauCeti` modules that expose every body.

Tau Ceti's `api-design` rubric rejects exposing definition bodies to compensate
for missing lemmas: *"Do not expose bodies to compensate for missing lemmas: keep
bodies unexposed (no `@[expose]`) where possible unless a consumer must unfold or
compute, and ask for the missing lemma instead."*  Jon adopted that over this
repository's own former house rule on 2026-07-30, so `ForTauCeti/README.md` now
asks for a plain `public section` with `@[expose]` only on the individual
declarations a consumer must genuinely unfold.

Conversion is staged across lanes `FTC-EXPOSE-a` … `FTC-EXPOSE-e`.  **This gate is
not the conversion.**  It is the ratchet that stops the count rising while the
conversion happens — which is a live risk, not a hypothetical: the count was 68
during one audit pass and 70 during the next, because the old rule was telling
every new file to add one.

    python3 scripts/check_expose_ratchet.py            # report
    python3 scripts/check_expose_ratchet.py --check    # gate; exit 1 if above baseline
    python3 scripts/check_expose_ratchet.py --list     # name the files

**Lowering the baseline is the point.**  Each conversion slice edits `BASELINE`
down to the count it leaves behind, in the same commit as the conversion, so the
gate can never drift upward unnoticed.  `FTC-EXPOSE-ENFORCE` sets it to 0.

Lane FTC-EXPOSE-GATE, 2026-07-30.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "ForTauCeti"

#: The highest number of blanket-exposing modules the tree may contain.
#: Measured on 2026-07-30, the day the convention was adopted.  Only ever lower it.
BASELINE = 51

BLANKET = re.compile(r"^@\[expose\]\s*public\s+section", re.M)

#: Per-declaration `@[expose]`.  The blanket ratchet alone has an obvious failure mode:
#: convert a module off `@[expose] public section` and then sprinkle `@[expose]` over its
#: definitions, which satisfies the count while defeating the point.  This second ratchet
#: closes that.  It is NOT zero, and should not be: `api-design` explicitly permits
#: exposure where "a consumer must unfold or compute".  Every one of these carries a
#: comment naming the reason.  Raising it is allowed; doing so silently is not.
PER_DECL_BASELINE = 4

PER_DECL = re.compile(r"^@\[expose\]\s*$", re.M)


def offenders() -> list[Path]:
    """Modules opening a file-wide `@[expose] public section`."""
    return [p for p in sorted(LIB.rglob("*.lean")) if BLANKET.search(p.read_text())]


def per_declaration() -> list[tuple[Path, int]]:
    """(module, count) for each module carrying standalone `@[expose]` attributes."""
    out = []
    for p in sorted(LIB.rglob("*.lean")):
        k = len(PER_DECL.findall(p.read_text()))
        if k:
            out.append((p, k))
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if the count exceeds the recorded baseline")
    parser.add_argument("--list", action="store_true", help="name every offending module")
    args = parser.parse_args(argv)

    found = offenders()
    n = len(found)
    total = sum(1 for _ in LIB.rglob("*.lean"))

    if args.list:
        for p in found:
            print(f"  {p.relative_to(ROOT)}")

    if n > BASELINE:
        print(f"expose-ratchet check: {n} modules expose every body, above the "
              f"baseline of {BASELINE}")
        print("  A new module used `@[expose] public section`. `ForTauCeti/README.md` §4")
        print("  asks for a plain `public section`, with `@[expose]` on the individual")
        print("  declarations a consumer must unfold — and a docstring saying why.")
        print("  Run with --list to see them.")
        return 1 if args.check else 0

    if n < BASELINE:
        print(f"expose-ratchet check: {n} of {total} modules, BELOW the baseline of "
              f"{BASELINE} — lower `BASELINE` to {n} in this script, in the commit that "
              f"did the conversion.")
        return 0

    print(f"expose-ratchet check: OK ({n} of {total} modules at the baseline of {BASELINE})")

    per = per_declaration()
    m = sum(k for _, k in per)
    if args.list:
        for path, k in per:
            print(f"  per-declaration x{k}: {path.relative_to(ROOT)}")
    if m > PER_DECL_BASELINE:
        print(f"  per-declaration @[expose]: {m} across {len(per)} modules, ABOVE the "
              f"baseline of {PER_DECL_BASELINE}")
        print("  Converting a module off the blanket and then exposing its definitions one")
        print("  by one satisfies the blanket count while defeating the point. If the new")
        print("  exposure is genuinely the api-design carve-out, raise PER_DECL_BASELINE in")
        print("  the same commit and say why at the declaration.")
        return 1 if args.check else 0
    print(f"  per-declaration @[expose]: {m} across {len(per)} modules, at or below the "
          f"baseline of {PER_DECL_BASELINE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
