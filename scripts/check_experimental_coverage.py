#!/usr/bin/env python3
"""Refuse an `Experimental` tree whose root does not reach every module in it.

`check_experimental_root_status.py` runs `lake build DavisKahan.Experimental` and
prints CLEAN when it succeeds.  Its registry says in so many words that
*"omitted failures cannot be certified by an empty registry"* — because the
build is supposed to cover the tree.

**On 2026-07-31 that build reached 46 of the 118 files under
`DavisKahan/Experimental/`, and six of the other 72 did not compile.**  The
oldest of them, `InfiniteDimensional/Core/Unbounded.lean`, projects five fields
off `ClosedOperator` that exist nowhere in the repository.  Nothing reported it,
because nothing built it: it is not in `defaultTargets`, not in the experimental
root's closure, and `Experimental/All.lean` is curated by hand
(`generate_all_aggregates.py` skips the directory by design).

The failure mode is worth naming because it is not "a module is broken".  It is
**a gate reporting CLEAN over a third of the tree it names**, which is worse than
having no gate, because the green is believed.  The same shape turned up the same
day in `FinishTanTwoTheta`, which has no `globs` in `lakefile.toml`: a module
there had stopped compiling and a promotion four hours earlier had silently
broken another.

    python3 scripts/check_experimental_coverage.py           # report
    python3 scripts/check_experimental_coverage.py --check   # exit 1 on a finding

## Why an exception list and not a count

Every module under `Experimental/` must be reachable from the root, *or* named
here with the reason it cannot be.  A count would let one module leave the
closure as another joins it; a named list makes each absence a deliberate,
reviewable line.  Adding a name here is a claim that the module cannot build and
that somebody knows why — not a way to quiet the gate.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPERIMENTAL = ROOT / "DavisKahan/Experimental"
ROOT_MODULE = "DavisKahan.Experimental"
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)\s*$", re.M)

#: Modules deliberately outside the root's closure, each with the reason.
#:
#: All twenty-seven are one connected failure: six modules do not compile, and
#: the rest reach one of the six.  Until they are repaired or retired, they are excluded here rather than
#: imported, because importing them would make `lake build DavisKahan.Experimental`
#: red for everyone without telling anybody anything new.
EXCLUDED: dict[str, str] = {
    # The six that do not compile.
    "DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded":
        "projects adjointDomain, adjointVector, adjointVector_inner, "
        "adjointDomain_dense, adjoint_graph_closed, resolvent, subScalar and "
        "symmetric off ClosedOperator; none of them is declared anywhere in the "
        "repository.  The module's own docstring says it 'retains only the "
        "declarations that are still unresolved' -- the interface it was written "
        "against left ClosedOperator/Basic.lean and took the fields with it.",
    "DavisKahan.Experimental.InfiniteDimensional.OperatorBlocks.OffDiagonal":
        "**CLASS: written against an interface that was never built.**  19 errors, and the "
        "reason recorded here until 2026-07-31 -- 'a drifted block API' -- was wrong in the "
        "way that matters, because 'drifted' invites a repair.  The file references "
        "`riccatiEquation_of_graph_reduces`, `diagonalBlock`, `offDiagonalBlock`, "
        "`ContinuedSpectralDatum`, `twoAngleTransform` and "
        "`exists_continuedSpectralDatum_of_offDiagonal`; **six of those seven names are "
        "absent from the entire repository** (only `tanTwoAngleOperator` exists), and "
        "`git log --all -S` over each shows the only file that has ever contained them is "
        "this one.  Nothing moved out from under it.  Delete-or-rewrite is a decision for "
        "an owner, not a repair -- same disposition as `Core/Unbounded` below.",
    "DavisKahan.Experimental.MathAhead.HiddenFoundations.KyFanBochner":
        "**blocked on absent Mathlib, not on this repository.**  Narrowed from 8 errors to "
        "4 on 2026-07-31: the universe mismatch and the `Seminorm` fields are fixed, and "
        "what is left is two things pinned Mathlib does not have -- `Seminorm.integral_le`, "
        "which is the Bochner--Minkowski inequality the module exists to apply, and the "
        "`†` adjoint notation.  **Corrected 2026-07-31 by lane DK-EXPCOVER's own follow-up, "
        "EXP-BUILD-ADJ: the notation is Mathlib's, localized in `LinearPMap`, so that half "
        "needs `open scoped LinearPMap` and not a definition.**  What is genuinely absent "
        "is `Seminorm.integral_le` alone -- same category as `compactOperatorNorm` and "
        "Schauder's theorem: the chain leaves the repository.  "
        "**CLASS: one external blocker plus two local errors, re-measured 2026-07-31.**  Of "
        "the 7 errors, exactly one is external (`Seminorm.integral_le` at :71).  The other "
        "two roots are local and neither needs Mathlib: a type mismatch at :62, and at :77 "
        "the `\u2020` adjoint notation applied to a `ContinuousLinearMap` -- `\u2020` is "
        "Mathlib\'s and is scoped to `LinearPMap`, so it is not merely out of scope here, "
        "it is the wrong notation for a bounded operator.  The two errors at :122/:123 are "
        "cascade: :77 fails, so the theorem it heads never registers, and its own use "
        "below reports an unknown identifier.  **So this module is nearer to building than "
        "an error count suggests** -- but it cannot reach green while :71 stands.",
    "DavisKahan.Experimental.MathAhead.HiddenFoundations.CircleContourGeometry":
        "**CLASS: a Mathlib-era migration, not a rename sweep.**  21 errors.  This entry "
        "said on 2026-07-31 that 'every unknown name has a live successor'; that was "
        "measured by grepping Mathlib for similar names and **it does not survive trying "
        "them** -- each substitution clears its own error and exposes the next, which is the "
        "same cascade at lemma level that `ContourReuseBridge` showed at module level.  "
        "**The blocker is `Complex.abs`**: the bundled `AbsoluteValue` is gone from pinned "
        "Mathlib and only the `Complex.abs_*` lemmas remain, the idiom now being the norm.  "
        "Two other files in this repository (`Geometry/Polar/DirectRotationSquare.lean`, "
        "`ForTauCeti/.../LinearPMap/SpectralMeasure.lean`) use the *lemmas* and build; this "
        "module uses the *bundle* (`map_sub Complex.abs`) and cannot.  Measured "
        "substitutions: `circleIntegral_def` -> `circleIntegral_def_Icc` clears that error "
        "and exposes `intervalIntegral.integral_comp_mul_deriv_Icc`, also absent; "
        "`HasDerivAt.ofReal`/`Continuous.ofReal` need restructuring rather than renaming, "
        "because `HasDerivAt.ofReal_comp` has a different shape.  Other names that do have "
        "successors: "
        "`Complex.circleIntegral_eq_zero_of_differentiable_on_ball` -> "
        "`circleIntegral_eq_zero_of_differentiable_on_off_countable` (generalised, so the "
        "argument list changes); `Complex.abs.map_sub` -> renamed with the `Complex.abs` "
        "restructuring.  Also `Continuous.ofReal` and `HasFDerivAtFilter.ofReal`.  "
        "**Newly visible on 2026-07-31**: it inherited its exclusion from "
        "`ContourReuseBridge` until that was repaired, and repairing one module is what "
        "exposed the next.",
    "DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex":
        "KyFanDominantIdealFamily.gaugeReal no longer exists.",
    "DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport":
        "type mismatches against a changed ideal-family signature.",
}

#: Subtrees the root deliberately does not aggregate, each with the reason.
#:
#: `Experimental/All.lean`'s own docstring states the `InfiniteDimensional` one:
#: those modules are *"older ambient facades, kept for historical reference"* and
#: are *"deliberately not aggregated here"*.  **The other three subtrees are
#: excluded too and nothing says so** — which is the finding this gate exists to
#: stop repeating.  A prefix here is a decision about a subtree; a name in
#: `EXCLUDED` is a broken module.  The two must not be confused, because the first
#: is permanent and the second is a bug.
EXCLUDED_PREFIXES: dict[str, str] = {
    "DavisKahan.Experimental.InfiniteDimensional.":
        "deliberately not aggregated -- `Experimental/All.lean` says these are older "
        "ambient facades kept for historical reference, and that the live development "
        "is `DavisKahan.All`.  Documented, and the only one of the four that is.",
    "DavisKahan.Experimental.Frontier.":
        "not aggregated, and no module says why.  Recorded here so the absence is at "
        "least visible; deciding whether it should be aggregated is lane "
        "`{lane:DK-EXPCOVER-REPAIR}`.",
    "DavisKahan.Experimental.MathAhead.":
        "not aggregated, and no module says why -- same as `Frontier`.",
    "DavisKahan.Experimental.Scratch.":
        "not aggregated; the directory name is the reason, but it was nowhere written "
        "down that nothing compiles it.",
}

#: Filled in below: every module that reaches an excluded one inherits the
#: exclusion, because it cannot build either.  Listing them explicitly would go
#: stale the moment an import changes, so they are derived.
_INHERITED = "reaches an excluded module, so it cannot compile either"


def imports_of(module: str) -> list[str]:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        return []
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def closure(start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(imports_of(module))
    return seen


def experimental_modules() -> list[str]:
    return sorted(
        str(p.relative_to(ROOT))[:-5].replace("/", ".")
        for p in EXPERIMENTAL.rglob("*.lean")
    )


def inherited_exclusions(modules: list[str]) -> dict[str, str]:
    """Modules that reach an excluded one, and so cannot compile either."""
    out: dict[str, str] = {}
    for module in modules:
        if module in EXCLUDED:
            continue
        hit = closure(module) & set(EXCLUDED)
        if hit:
            out[module] = f"{_INHERITED}: {sorted(hit)[0]}"
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 on a finding")
    args = parser.parse_args()

    modules = experimental_modules()
    covered = closure(ROOT_MODULE)
    inherited = inherited_exclusions(modules)
    excused = set(EXCLUDED) | set(inherited)

    by_prefix = {m for m in modules
                 if any(m.startswith(p) for p in EXCLUDED_PREFIXES)}
    excused |= by_prefix
    uncovered = [m for m in modules if m not in covered and m not in excused]
    stale = sorted(m for m in EXCLUDED if m not in modules)

    print(
        f"experimental coverage: {len(modules)} modules, "
        f"{len([m for m in modules if m in covered])} reached by {ROOT_MODULE}, "
        f"{len([m for m in modules if m not in covered])} not reached, of which "
        f"{len([m for m in by_prefix if m not in covered])} are excluded by subtree "
        f"and {len([m for m in EXCLUDED if m not in covered])} are named as broken"
    )
    for module in uncovered:
        print(f"-> not reachable and not excluded: {module}")
    for module in stale:
        print(f"?? excluded module no longer exists: {module}")

    if uncovered:
        print(
            f"\nexperimental coverage: {len(uncovered)} finding(s).\n"
            "  Import them from `DavisKahan/Experimental/All.lean` -- which is curated by\n"
            "  hand, `generate_all_aggregates.py` skips this directory -- or add them to\n"
            "  EXCLUDED with the reason they cannot build.  A module in neither place is\n"
            "  one that nothing compiles and nothing reports."
        )
        return 1 if args.check else 0
    if stale:
        print(
            f"\nexperimental coverage: {len(stale)} stale exclusion(s).\n"
            "  Remove them: an exclusion naming a module that no longer exists silently\n"
            "  excuses the next module to take that name."
        )
        return 1 if args.check else 0
    print("experimental coverage: OK -- every module is reached or excluded with a reason")
    return 0


if __name__ == "__main__":
    sys.exit(main())
