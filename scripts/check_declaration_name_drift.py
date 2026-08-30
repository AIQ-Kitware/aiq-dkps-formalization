#!/usr/bin/env python3
"""Static gate against declaration-name drift in non-Lean-checked assertions.

Most of this repository is checked by the compiler. Two places are not, and both
have silently broken during namespace migrations:

1. ``comparator/*.json`` restates declaration names as **data** (the
   ``theorem_names`` list). A renamed or re-namespaced declaration leaves the
   config pointing at nothing, and
   ``scripts/check_comparator_signatures.py`` then reports ``unknown constant``
   for every entry rather than a mismatch -- so the conformance gate degrades to
   *vacuous* instead of failing loudly. After the Wave-1 CourantFischer dedup
   (``1fbd391``) this was the state of 20 of the 23 configs, for days.

2. ``Challenge/**`` is outside ``defaultTargets``, so ``lake build`` does not
   compile it. The 9.2 sorted-eigenvalue rename passed a green 9272-job default
   build and still left
   ``Challenge.RankPsdRealization.Leaderboard`` failing with
   ``Unknown constant``.

Section 13 of ``dev/tauceti-signature-polish-todo.md`` asks for "a grep gate for
old fully qualified names" after each rename. This is that gate. It is
deliberately **build-free** -- it resolves names by parsing declarations out of
the Lean sources rather than by asking Lean -- so it is fast enough to run on
every commit, and it can be run when the tree does not compile.

Checks
------

``pinned-name-resolves``
    Every name in a ``comparator/*.json`` ``theorem_names`` list, and every name
    on a ``#print axioms`` line in a ``Challenge/**/Leaderboard.lean``, must
    correspond to a declaration that exists somewhere in the tree.

``pinned-name-in-challenge``
    Every name pinned by a comparator config must also be declared by that
    config's challenge module. This is the check that catches the
    ``ForMathlib``-vs-``TauCeti`` namespace mismatch class: the mass namespace
    flip rewrote several ``Conformance`` modules to ``namespace TauCeti`` while
    the declarations they mirror stayed in ``ForMathlib``, which compiles fine on
    both sides and fails only in the comparator's export comparison.

``pinned-name-unaudited``
    Every name a comparator config pins should also be audited by the paired
    leaderboard with ``#print axioms``. A pinned statement whose axioms nobody
    audits is compared but not certified.  A config may explicitly list
    ``expected_missing_solution_theorems`` for source-faithfulness obligations
    that are intentionally stated by the challenge but have no solution yet;
    those remain red in the real signature/comparator check and are informational
    rather than failures of this name-drift tripwire.

    The converse -- a leaderboard auditing *more* names than the config pins --
    is **not** a failure and is reported only as a note: a leaderboard may
    legitimately audit supporting results alongside the pinned leaves.

Limitations, stated rather than hidden
--------------------------------------

Name resolution is *syntactic*: this script computes the fully-qualified name of
each declaration from the ``namespace``/``end``/``section`` structure of the file
and from ``_root_.`` prefixes. It does not expand ``export``, ``open ... in``
abbreviations, or ``alias`` targets beyond the alias's own name, and it does not
know about ``protected``/``private``. So a *failure* is strong evidence of drift
and a *pass* is not a proof of resolvability -- the compiler and
``check_comparator_signatures.py`` remain ground truth. It is a cheap tripwire
for the specific failure mode that has actually occurred here, not a type
checker.

Usage
-----

::

    python3 scripts/check_declaration_name_drift.py
    python3 scripts/check_declaration_name_drift.py --json

Exit status is nonzero if any check fails.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

try:
    from aiq_lean_tools.lean_source import scan_lean_project
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

PRINT_AXIOMS_RE = re.compile(r"^#print[ \t]+axioms[ \t]+(\S+)[ \t]*$", re.MULTILINE)


def git_root() -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        )
        return out.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return os.getcwd()


def module_to_path(module: str) -> str:
    return module.replace(".", os.sep) + ".lean"


def source_index(root: str):
    """The structural declaration index, from `aiq_lean_tools`.

    Name resolution is *syntactic*: fully-qualified names are computed from the
    `namespace`/`section`/`end` structure and `_root_.` prefixes, with comments
    stripped.  `export`, `open ... in` abbreviations, and `alias` targets beyond
    the alias's own name are not expanded.  So a *failure* here is strong evidence
    of drift and a *pass* is not proof of resolvability; the compiler and
    `check_comparator_signatures.py` remain ground truth.
    """
    return scan_lean_project(root)


def declarations_by_module(index) -> dict[str, set[str]]:
    out: dict[str, set[str]] = defaultdict(set)
    for row in index.named_declarations:
        out[row.module].add(row.name)
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="emit machine-readable findings"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="also print informational notes that do not fail the gate",
    )
    args = parser.parse_args()

    root = git_root()
    os.chdir(root)
    scan = source_index(root)
    index = scan.by_name
    by_module = declarations_by_module(scan)

    findings: list[dict[str, str]] = []
    notes: list[dict[str, str]] = []

    configs = sorted(glob.glob(os.path.join(root, "comparator", "*.json")))
    for config_path in configs:
        rel_config = os.path.relpath(config_path, root)
        try:
            with open(config_path, encoding="utf-8") as handle:
                config = json.load(handle)
        except (OSError, json.JSONDecodeError) as exc:
            findings.append(
                {
                    "check": "config-readable",
                    "where": rel_config,
                    "detail": f"cannot parse: {exc}",
                }
            )
            continue

        pinned = config.get("theorem_names", [])
        expected_missing = set(config.get("expected_missing_solution_theorems", []))
        challenge_module = config.get("challenge_module", "")
        solution_module = config.get("solution_module", "")

        for name in sorted(expected_missing - set(pinned)):
            findings.append(
                {
                    "check": "expected-missing-not-pinned",
                    "where": rel_config,
                    "detail": (
                        f"`{name}` is marked as an expected missing solution but is "
                        "not listed in theorem_names"
                    ),
                }
            )

        challenge_decls = by_module.get(challenge_module, set())

        for name in pinned:
            if name not in index:
                findings.append(
                    {
                        "check": "pinned-name-resolves",
                        "where": rel_config,
                        "detail": (
                            f"`{name}` is pinned but no declaration with that "
                            "fully-qualified name exists in the tree"
                        ),
                    }
                )
            elif challenge_decls and name not in challenge_decls:
                findings.append(
                    {
                        "check": "pinned-name-in-challenge",
                        "where": rel_config,
                        "detail": (
                            f"`{name}` exists (in "
                            f"{', '.join(sorted({row.module for row in index[name]}))}) but the "
                            f"challenge module {challenge_module} does not declare "
                            "it -- the comparator compares the two side by side, so "
                            "this config can never pass"
                        ),
                    }
                )

        # The leaderboard's `#print axioms` list and the config's pinned list
        # should describe the same set of certified declarations.
        solution_path = module_to_path(solution_module) if solution_module else ""
        full_solution = os.path.join(root, solution_path) if solution_path else ""
        if full_solution and os.path.isfile(full_solution):
            with open(full_solution, encoding="utf-8") as handle:
                audited = set(PRINT_AXIOMS_RE.findall(handle.read()))
            for name in sorted(audited - set(pinned)):
                notes.append(
                    {
                        "check": "extra-leaderboard-audit",
                        "where": os.path.relpath(full_solution, root),
                        "detail": (
                            f"`{name}` is audited with `#print axioms` but is not "
                            f"pinned by {rel_config} (informational: a leaderboard "
                            "may audit supporting results too)"
                        ),
                    }
                )
            for name in sorted(set(pinned) - audited):
                if name in expected_missing:
                    notes.append(
                        {
                            "check": "expected-missing-solution",
                            "where": rel_config,
                            "detail": (
                                f"`{name}` is intentionally absent from the leaderboard; "
                                "the signature/comparator gate is expected to stay red"
                            ),
                        }
                    )
                    continue
                findings.append(
                    {
                        "check": "pinned-name-unaudited",
                        "where": os.path.relpath(full_solution, root),
                        "detail": (
                            f"`{name}` is pinned by {rel_config} but the leaderboard "
                            "does not audit it with `#print axioms`, so its axiom "
                            "footprint is never certified"
                        ),
                    }
                )
            for name in sorted(expected_missing & audited):
                findings.append(
                    {
                        "check": "stale-expected-missing-solution",
                        "where": rel_config,
                        "detail": (
                            f"`{name}` is marked expected-missing but is now audited by "
                            "the leaderboard; remove the exception and require it normally"
                        ),
                    }
                )

    # Every `#print axioms` target anywhere under Challenge/ must resolve.
    for path in sorted(glob.glob(os.path.join(root, "Challenge", "**", "*.lean"), recursive=True)):
        with open(path, encoding="utf-8") as handle:
            audited = PRINT_AXIOMS_RE.findall(handle.read())
        rel = os.path.relpath(path, root)
        for name in audited:
            if name not in index:
                findings.append(
                    {
                        "check": "pinned-name-resolves",
                        "where": rel,
                        "detail": (
                            f"`#print axioms {name}` names a declaration that does "
                            "not exist in the tree"
                        ),
                    }
                )

    # The Davis--Kahan source census restates declaration names as data too, and
    # nothing compiles it. Its names silently became unresolvable after the
    # ForMathlib -> TauCeti namespace move: every gate stayed green while all 87
    # named declarations had ceased to exist under those names.
    census_names = 0
    census_rel = os.path.join("dev", "davis-kahan-1970-full-source-census.json")
    census_path = os.path.join(root, census_rel)
    if os.path.isfile(census_path):
        try:
            with open(census_path, encoding="utf-8") as handle:
                census = json.load(handle)
        except (OSError, json.JSONDecodeError) as exc:
            findings.append(
                {
                    "check": "census-readable",
                    "where": census_rel,
                    "detail": f"cannot read census: {exc}",
                }
            )
            census = {"items": []}
        for item in census.get("items", []):
            item_id = item.get("id", "<no id>")
            for name in item.get("lean_declarations", []) or []:
                if not isinstance(name, str):
                    continue
                census_names += 1
                if name not in index:
                    findings.append(
                        {
                            "check": "pinned-name-resolves",
                            "where": f"{census_rel} [{item_id}]",
                            "detail": (
                                f"`{name}` names a declaration that does not exist "
                                "in the tree"
                            ),
                        }
                    )

    if args.json:
        print(json.dumps({"findings": findings, "notes": notes}, indent=2))
    else:
        if notes and args.verbose:
            print("[notes] (informational, do not fail the gate)")
            for note in notes:
                print(f"  {note['where']}: {note['detail']}")
            print()
        if findings:
            by_check: dict[str, list[dict[str, str]]] = defaultdict(list)
            for finding in findings:
                by_check[finding["check"]].append(finding)
            for check in sorted(by_check):
                print(f"[{check}]")
                for finding in by_check[check]:
                    print(f"  {finding['where']}: {finding['detail']}")
                print()
        print(
            f"declaration-name-drift check: "
            f"{'FAIL' if findings else 'OK'} "
            f"({len(configs)} comparator configs, {len(index)} declarations indexed, "
            f"{census_names} census declarations, "
            f"{len(findings)} finding(s), {len(notes)} note(s))"
        )
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
