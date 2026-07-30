#!/usr/bin/env python3
"""Enforce `ForTauCeti/README.md` §2: which namespaces a staging module may declare into.

§2 permits exactly two forms:

1. **an extension of the canonical Mathlib namespace of the object being
   extended** — `ContinuousLinearMap.opNorm_…` is a fact about a
   `ContinuousLinearMap`, so it belongs in `ContinuousLinearMap`; and
2. **`TauCeti`** (or a namespace below it), for everything the library owns.

Nothing checked §2 until 2026-07-29, and four files had drifted into namespaces
that are Mathlib's but are *not* the namespace of the object being extended: a
spectral functional calculus and a Moore--Penrose inverse are not facts about
`FiniteDimensional`.  That is what this gate exists to catch — it is a *misuse*
of form 1, not a third form, so an allowlist of root namespaces with a stated
reason for each is the right shape: adding an entry is cheap and forces the
author to say which object is being extended.

The test to apply when adding an entry is the one the audit used: **would the
declaration read naturally as a fact about that object?**  `ENNReal.tsum_…`
stated for arbitrary `f g : ι → ℝ≥0∞` passes.  `FiniteDimensional.moorePenrose…`
does not.

Usage:

    python3 scripts/check_namespace_policy.py           # report
    python3 scripts/check_namespace_policy.py --check   # exit 1 on a violation

Lane NS-SPREAD, 2026-07-29.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "ForTauCeti"

# Root namespaces a `ForTauCeti` module may open, other than `TauCeti`.
# Each is a canonical Mathlib namespace, and the reason names the object the
# declarations there extend.  Keep the reasons: they are the review the gate
# cannot perform.
ALLOWED: dict[str, str] = {
    "Cardinal": "lifts and inequalities of Mathlib `Cardinal`s",
    "ContinuousLinearMap": "facts about a `ContinuousLinearMap` — norms, adjoints, composition",
    "ENNReal": "inequalities between `ℝ≥0∞`-valued functions, e.g. Minkowski at p = 2 for `tsum`",
    "HilbertBasis": "Parseval-type identities for a Mathlib `HilbertBasis`",
    "IsPartialIsometry": "facts about Mathlib's `IsPartialIsometry` predicate",
    "LinearMap": "facts about a `LinearMap`, including its `IsPositive` / `IsSymmetric` predicates",
    "MeasureTheory": "additions to Mathlib's measure theory, stated for its own objects",
    "OrthonormalBasis": "facts about a Mathlib `OrthonormalBasis`",
    "Real": "facts about `Real`-valued functions, e.g. `Real.abs_sin_…`",
    "Submodule": "facts about a `Submodule` — projections, gaps, block decompositions",
}

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"^\s*--.*$", re.M)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)")


def declared_namespaces(text: str) -> list[str]:
    """Fully-qualified namespaces a file declares into, comments stripped.

    The stack matters: `namespace TauCeti` followed by `namespace HilbertSchmidt`
    declares into `TauCeti.HilbertSchmidt`, which is form 2 and fine.  Only the
    *outermost* name decides, so a naive scan of `namespace` lines reports almost
    every file in the library.  `end <name>` pops only when it matches what is
    open — an `end` closing a `section` must not pop a namespace.
    """
    stripped = LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))
    stack: list[str] = []
    out: list[str] = []
    for line in stripped.splitlines():
        m = NAMESPACE.match(line)
        if m:
            stack.append(m.group(1))
            out.append(".".join(stack))
            continue
        m = END.match(line)
        if m and stack and m.group(1) in (stack[-1], ".".join(stack)):
            stack.pop()
    return out


def scan() -> list[tuple[str, str]]:
    findings: list[tuple[str, str]] = []
    for path in sorted(LIB.rglob("*.lean")):
        for ns in declared_namespaces(path.read_text()):
            root = ns.split(".")[0]
            if root == "TauCeti" or root in ALLOWED:
                continue
            findings.append((str(path.relative_to(ROOT)), ns))
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if any module declares into a namespace §2 does not permit")
    args = parser.parse_args(argv)

    findings = scan()
    n_files = sum(1 for _ in LIB.rglob("*.lean"))
    if findings:
        for path, ns in findings:
            print(f"  NAMESPACE  {path}: declares into `{ns}`")
        print(f"namespace-policy check: {len(findings)} violation(s) over {n_files} modules")
        print("  Permitted: `TauCeti.*`, or one of " + ", ".join(f"`{k}`" for k in ALLOWED))
        print("  If the declarations really are facts about that object, add the root to")
        print("  ALLOWED in this script with the reason; otherwise move them to `TauCeti`.")
        return 1 if args.check else 0
    print(f"namespace-policy check: OK ({n_files} modules, "
          f"{len(ALLOWED)} allowlisted Mathlib namespaces)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
