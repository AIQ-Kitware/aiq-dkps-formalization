#!/usr/bin/env python3
"""Structural checks for the Davis--Kahan production/Experimental boundary.

The checker enforces durable repository invariants that originated in the July
2026 sine-theta reorganization and are now part of the maintained architecture:

1. production modules are reachable from `DavisKahan.All` or the curated root;
2. production modules do not import staging or diagnostic modules;
2c. production source does not declare or reference staging/scratch namespaces;
3. Experimental scratch health is delegated to its dedicated checker;
4. source facades are reachable from the curated root; and
5. the full-paper sine-theta audit still points at existing endpoints.

`Experimental`, `MathAhead`, and `Audits` are outside the production build
closure.  `MathAhead` is a proof-staging tree and `Audits` is an explicit
diagnostic tree; neither is a library dependency.  Production declarations also
do not live under a `Scratch` namespace.

Historical migration details live in
`dev/flawless-sine-theta-reorganization-overnight-plan-2026-07-20.md`; current
behavior is defined by this script and the present module graph.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
# Only DavisKahan uses this reachability policy; ForTauCeti is glob-built.
LIB_DIRS = ("DavisKahan",)
EXPERIMENTAL = ".Experimental."
EXPERIMENTAL_ROOT = "DavisKahan.Experimental"
NONPRODUCTION_SEGMENTS = {"Experimental", "MathAhead", "Audits"}
CURATED_ROOT = "DavisKahan"
DEV_ROOT = "DavisKahan.All"
AUDIT_SCRIPT = ROOT / "scripts/audit_full_paper_sine_theta.py"
AUDIT_MODULE = ROOT / "DavisKahan/Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean"
# Audited endpoints: 38 at the first clean run (cc7a7fc), plus the five
# finite-multiplicity reports. Raise this whenever endpoints are added; never
# lower it.
AUDITED_TARGET_FLOOR = 43

# Modules deliberately kept out of every root, with the reason. These are not
# claimed proofs: each one documents its own exclusion in its file header.
DELIBERATELY_UNBUILT = {}

IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*?$", re.M)
ADMISSION = re.compile(r"\b(?:sorry|admit)\b")
# A module with no declaration of its own is an aggregate: a pure import list.
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|unsafe\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b",
    re.MULTILINE)

STAGING_NAMESPACE_REF = re.compile(
    r"\b(?:Experimental|MathAhead|HiddenFoundations|Scratch)\b"
    r"|^\s*namespace\s+(?:Experimental|MathAhead|HiddenFoundations|Scratch)\b",
    re.MULTILINE,
)



def is_experimental(module: str) -> bool:
    return module == EXPERIMENTAL_ROOT or EXPERIMENTAL in module


def is_nonproduction(module: str) -> bool:
    """Whether a module belongs to staging, scratch, or diagnostic source."""
    return any(part in NONPRODUCTION_SEGMENTS for part in module.split("."))

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


def supports_admitted(module: str, consumers: dict[str, set[str]],
                      admitted: dict[str, bool], memo: dict[str, bool],
                      stack: frozenset[str] = frozenset()) -> bool:
    """Does anything transitively importing `module` still rest on an admission?

    This is the *upward* question, and it is the one that decides whether a
    module belongs in `Experimental/`.  Rule 3 originally asked the downward
    one — whether the module's own import closure contains an admission — which
    flags every fully proved Experimental module, including proved scaffolding
    whose only purpose is to support unfinished work.  Those are correctly
    placed, so the rule could never be satisfied by moving files: measured
    2026-07-29, 17 of its 74 findings were modules that should not move.
    See `docs/planning/historical/tauceti-experimental-scratch-rule3-audit-2026-07-29.md`
    for the historical rationale behind this rule.
    """
    if module in memo:
        return memo[module]
    if module in stack:
        return False
    result = any(
        admitted.get(consumer, False)
        or supports_admitted(consumer, consumers, admitted, memo,
                             stack | {module})
        for consumer in consumers.get(module, ())
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
    production = [m for m in files if not is_nonproduction(m)]
    memo: dict[str, bool] = {}

    print(f"Library structure check over {len(files)} modules "
          f"({len(production)} production, {len(files) - len(production)} nonproduction)")

    covered = reachable(imports, [DEV_ROOT])
    check1 = report(
        "1. production modules reachable from DavisKahan.All",
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
        if is_nonproduction(dep)
    )
    check2 = report(
        "2. no production module imports Experimental/MathAhead/Audits", crossing)

    leaked = sorted(m for m in covered if is_nonproduction(m))
    check2b = report(
        "2b. DavisKahan.All reaches no staging or diagnostic modules", leaked)

    staging_namespace_refs: list[str] = []
    for module in production:
        text = files[module].read_text()
        body = LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))
        if STAGING_NAMESPACE_REF.search(body):
            staging_namespace_refs.append(module)
    check2c = report(
        "2c. production source uses only stable namespaces (no Scratch)",
        sorted(staging_namespace_refs),
    )

    consumers: dict[str, set[str]] = {}
    for module, deps in imports.items():
        for dep in deps:
            consumers.setdefault(dep, set()).add(module)
    up_memo: dict[str, bool] = {}
    rule3 = sorted(
        m for m in files
        if is_experimental(m)
        and not in_admission_closure(m, imports, admitted, memo)
        and not supports_admitted(m, consumers, admitted, up_memo)
    )
    if rule3:
        print(f"  note  3. Experimental scratch hygiene: {len(rule3)} module(s) are "
              "outside the admission-support closure; run "
              "`aiq-lean source module-coverage dev/policy/experimental-coverage.yaml` for scratch-tree policy")
    else:
        print("  ok    3. Experimental scratch hygiene has no residual findings")
    check3 = True

    curated = reachable(imports, [CURATED_ROOT])
    facades = [m for m in files if m.startswith("DavisKahan.Sources.")
               and not m.endswith(".All") and not is_nonproduction(m)]
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

    if all((check1, check2, check2b, check2c, check3, check4, check5)):
        print("Library structure: CLEAN")
        return
    print("Library structure: violations remain "
          "(see dev/davis-kahan-1970-source-correspondence-matrix.md)")
    raise SystemExit(1)


if __name__ == "__main__":
    main()
