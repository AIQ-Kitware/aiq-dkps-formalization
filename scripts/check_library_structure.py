#!/usr/bin/env python3
"""Structural checks for the Davis--Kahan library layout.

These are the five checks required by
`dev/flawless-sine-theta-reorganization-overnight-plan-2026-07-20.md`:

1. every production module is reachable from `DavisKahan.All` or the
   `ForMathlib` root;
2. no production module imports an Experimental module;
3. every Experimental module has an admission in its dependency closure;
4. every source facade is reachable from the curated `DavisKahan` root;
5. the full-paper audit still points at existing paths and has not silently
   dropped audited targets.

Checks 1 and 2 are expected to fail until the admitted foundational modules are
split; see `dev/sine-theta-move-manifest-2026-07-20.md`. Reporting those
violations precisely is the point of this script, so it exits nonzero while they
stand.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB_DIRS = ("DavisKahan", "ForMathlib")
EXPERIMENTAL = ".Experimental."
EXPERIMENTAL_ROOT = "DavisKahan.Experimental"
CURATED_ROOT = "DavisKahan"
DEV_ROOT = "DavisKahan.All"
FORMATHLIB_ROOT = "ForMathlib"
AUDIT_SCRIPT = ROOT / "scripts/audit_full_paper_sine_theta.py"
AUDIT_MODULE = ROOT / "DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullPaperSineThetaAudit.lean"
# Audited endpoints: 38 at the first clean run (cc7a7fc), plus the five
# finite-multiplicity reports. Raise this whenever endpoints are added; never
# lower it.
AUDITED_TARGET_FLOOR = 43

# Modules deliberately kept out of every root, with the reason. These are not
# claimed proofs: each one documents its own exclusion in its file header.
DELIBERATELY_UNBUILT = {
    "ForMathlib.Analysis.InnerProductSpace.RectangularSingularValuesDkVariant":
        "preserved comparison variant; its header records that it does not "
        "elaborate on the pinned toolchain and must not be imported",
}

IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*?$", re.M)
ADMISSION = re.compile(r"\b(?:sorry|admit)\b")



def is_experimental(module: str) -> bool:
    return module == EXPERIMENTAL_ROOT or EXPERIMENTAL in module

def load() -> tuple[dict[str, pathlib.Path], dict[str, list[str]], dict[str, bool]]:
    files: dict[str, pathlib.Path] = {}
    for directory in LIB_DIRS:
        for path in ROOT.glob(f"{directory}/**/*.lean"):
            files[str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")] = path
        root_file = ROOT / f"{directory}.lean"
        if root_file.exists():
            files[directory] = root_file
    imports: dict[str, list[str]] = {}
    admitted: dict[str, bool] = {}
    for module, path in files.items():
        text = path.read_text()
        imports[module] = [m for m in IMPORT.findall(text) if m in files]
        body = LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))
        admitted[module] = bool(ADMISSION.search(body))
    return files, imports, admitted


def reachable(imports: dict[str, list[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = [r for r in roots if r in imports]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(imports.get(module, []))
    return seen


def in_admission_closure(
    module: str, imports: dict[str, list[str]], admitted: dict[str, bool],
    memo: dict[str, bool], stack: frozenset[str] = frozenset()
) -> bool:
    if module in memo:
        return memo[module]
    if module in stack:
        return False
    result = admitted.get(module, False) or any(
        in_admission_closure(dep, imports, admitted, memo, stack | {module})
        for dep in imports.get(module, [])
    )
    memo[module] = result
    return result


def report(name: str, violations: list[str], limit: int = 12) -> bool:
    if not violations:
        print(f"  ok    {name}")
        return True
    print(f"  FAIL  {name}: {len(violations)} violation(s)")
    for item in violations[:limit]:
        print(f"          {item}")
    if len(violations) > limit:
        print(f"          ... and {len(violations) - limit} more")
    return False


def main() -> None:
    files, imports, admitted = load()
    production = [m for m in files if not is_experimental(m)]
    memo: dict[str, bool] = {}

    print(f"Library structure check over {len(files)} modules "
          f"({len(production)} production, {len(files) - len(production)} experimental)")

    covered = reachable(imports, [DEV_ROOT, FORMATHLIB_ROOT])
    check1 = report(
        "1. production modules reachable from DavisKahan.All / ForMathlib",
        sorted(m for m in production
               if m not in covered and m not in DELIBERATELY_UNBUILT),
    )
    for module, reason in DELIBERATELY_UNBUILT.items():
        if module in covered:
            print(f"  note  {module} is now reachable but is marked "
                  f"deliberately unbuilt ({reason})")

    crossing = sorted(
        f"{m} -> {dep}"
        for m in production
        for dep in imports.get(m, [])
        if is_experimental(dep)
    )
    check2 = report("2. no production module imports Experimental", crossing)

    check3 = report(
        "3. every Experimental module has an admission in its closure",
        sorted(
            m for m in files
            if is_experimental(m)
            and not in_admission_closure(m, imports, admitted, memo)
        ),
    )

    curated = reachable(imports, [CURATED_ROOT])
    facades = [m for m in files if m.startswith("DavisKahan.Sources.")
               and not m.endswith(".All")]
    check4 = report(
        "4. source facades reachable from the curated DavisKahan root",
        sorted(m for m in facades if m not in curated),
    )

    audit_problems: list[str] = []
    if not AUDIT_SCRIPT.exists():
        audit_problems.append(f"missing audit script {AUDIT_SCRIPT.name}")
    if not AUDIT_MODULE.exists():
        audit_problems.append("audit module path no longer exists")
    else:
        printed = sum(
            1 for line in AUDIT_MODULE.read_text().splitlines()
            if line.strip().startswith("#print axioms")
        )
        if printed < AUDITED_TARGET_FLOOR:
            audit_problems.append(
                f"audit dropped targets: {printed} < {AUDITED_TARGET_FLOOR}"
            )
    check5 = report("5. full-paper audit paths and target count intact", audit_problems)

    if all((check1, check2, check3, check4, check5)):
        print("Library structure: CLEAN")
        return
    print("Library structure: violations remain "
          "(see dev/sine-theta-move-manifest-2026-07-20.md)")
    raise SystemExit(1)


if __name__ == "__main__":
    main()
