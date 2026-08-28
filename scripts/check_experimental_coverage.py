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
having no gate, because the green is believed.

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
#: Empty since 2026-08-27, and that is the intended steady state: an entry here
#: is a module that does not compile, which is a bug with a name, not a policy.
#: The last two were the ideal-family scratch pair; they were promoted to
#: `DavisKahan/SharedFoundations/Ideal/{Modulus,Reflection}Transport.lean` and
#: compile there.
EXCLUDED: dict[str, str] = {}

#: Subtrees the root deliberately does not aggregate, each with the reason.
#:
#: A prefix here is a decision about a subtree; a name in `EXCLUDED` is a broken
#: module.  The two must not be confused, because the first is permanent and the
#: second is a bug.  On 2026-08-27 the `InfiniteDimensional` prefix was removed
#: with its subtree: every one of its seventeen modules had stopped elaborating,
#: and being excluded here is exactly why nothing said so.  That is the failure
#: this gate exists to name, so a subtree exclusion should be read as a standing
#: bet that nobody is checking the modules inside it.
#: Empty since 2026-08-27, when the last scratch subtree was drained.  A future
#: scratch drop under `Experimental/Scratch/**` may want an entry again; read the
#: paragraph above before adding one.
EXCLUDED_PREFIXES: dict[str, str] = {}

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
