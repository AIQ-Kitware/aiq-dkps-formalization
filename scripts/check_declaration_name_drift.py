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
   ``Challenge.MathlibPending.RankPsdRealization.Leaderboard`` failing with
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
    audits is compared but not certified.

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

# Lean libraries whose declarations can be pinned. Everything else (vendored
# Spectra, the Mathlib checkout, build artefacts) is out of scope.
SOURCE_ROOTS = [
    "Acharyya2024",
    "Acharyya2025",
    "Challenge",
    "DavisKahan",
    "DkpsQuench2026",
    "ForMathlib",
    "ForTauCeti",
    "Helm2025",
]

# `theorem foo`, `lemma foo`, `def foo`, `abbrev foo`, `instance foo`, ... The
# leading modifiers are optional and may appear in any order in practice, so
# they are matched as a set rather than a fixed sequence.
_MODIFIERS = r"(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
_KEYWORDS = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|alias)"
DECL_RE = re.compile(
    rf"^{_MODIFIERS}{_KEYWORDS}\s+(?P<name>_root_\.[A-Za-z_0-9'ₐ-ₜ₀-₉«»\.Ͱ-Ͽ℀-⅏←-⇿∀-⋿]+|[A-Za-z_«][A-Za-z_0-9'«»\.Ͱ-Ͽ₀-ₜ℀-⅏←-⇿∀-⋿]*)",
    re.MULTILINE,
)
# NOTE: horizontal whitespace only. `\s` matches newlines, so `\s*$` under
# `re.MULTILINE` happily spans a blank line and swallows the next line -- with
# `\s`, the two lines `end` / `section` parse as a single `end section`, which
# silently unbalances the namespace stack for the whole file.
NAMESPACE_RE = re.compile(r"^namespace[ \t]+(\S+)[ \t]*$", re.MULTILINE)
# `section`, `section Foo`, `noncomputable section`, `@[expose] public section`.
# A bare `end` closes whichever of these or `namespace` is innermost, so both
# have to be tracked on one stack -- treating `end` as always closing a
# namespace silently corrupts every name in a file that opens a section.
SECTION_RE = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)?(?:public[ \t]+|private[ \t]+|noncomputable[ \t]+)*section(?:[ \t]+(\S+))?[ \t]*$",
    re.MULTILINE,
)
END_RE = re.compile(r"^end(?:[ \t]+(\S+))?[ \t]*$", re.MULTILINE)
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


def declarations_in(path: str) -> set[str]:
    """Fully-qualified declaration names declared in one Lean file.

    The namespace stack is tracked through ``namespace``/``end``. A bare ``end``
    closes the innermost open namespace; ``end Foo.Bar`` closes that many
    components. ``_root_.`` prefixes escape the stack.
    """
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
    except (OSError, UnicodeDecodeError):
        return set()

    names: set[str] = set()
    # Entries are ("ns", ["Foo", "Bar"]) or ("sec", name-or-None). A bare `end`
    # pops the innermost entry of either kind.
    stack: list[tuple[str, object]] = []

    def prefix() -> str:
        parts: list[str] = []
        for kind, value in stack:
            if kind == "ns":
                parts.extend(value)  # type: ignore[arg-type]
        return ".".join(parts)

    events = []
    for match in NAMESPACE_RE.finditer(text):
        events.append((match.start(), "ns", match.group(1)))
    for match in SECTION_RE.finditer(text):
        events.append((match.start(), "sec", match.group(1)))
    for match in END_RE.finditer(text):
        events.append((match.start(), "end", match.group(1)))
    for match in DECL_RE.finditer(text):
        events.append((match.start(), "decl", match.group("name")))
    events.sort(key=lambda item: item[0])

    for _, kind, value in events:
        if kind == "ns":
            stack.append(("ns", value.split(".")))
        elif kind == "sec":
            stack.append(("sec", value))
        elif kind == "end":
            if value is None:
                if stack:
                    stack.pop()
            else:
                # `end Foo.Bar` closes the matching opener; pop until we have
                # popped an entry whose name matches, so an intervening
                # anonymous section does not shift the stack.
                target = value.split(".")
                while stack:
                    entry_kind, entry_value = stack.pop()
                    if entry_kind == "ns" and entry_value == target:
                        break
                    if entry_kind == "sec" and entry_value == value:
                        break
        else:
            if value.startswith("_root_."):
                names.add(value[len("_root_.") :])
            else:
                current = prefix()
                names.add(current + "." + value if current else value)
    return names


def collect_declarations(root: str) -> dict[str, list[str]]:
    """Map fully-qualified declaration name -> files declaring it."""
    index: dict[str, list[str]] = defaultdict(list)
    for source_root in SOURCE_ROOTS:
        base = os.path.join(root, source_root)
        if not os.path.isdir(base):
            continue
        for dirpath, _dirnames, filenames in os.walk(base):
            for filename in filenames:
                if not filename.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, filename)
                rel = os.path.relpath(path, root)
                for name in declarations_in(path):
                    index[name].append(rel)
    # Top-level aggregate modules such as `ForMathlib.lean` sit beside the roots.
    for filename in glob.glob(os.path.join(root, "*.lean")):
        rel = os.path.relpath(filename, root)
        for name in declarations_in(filename):
            index[name].append(rel)
    return index


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
    index = collect_declarations(root)

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
        challenge_module = config.get("challenge_module", "")
        solution_module = config.get("solution_module", "")

        challenge_path = module_to_path(challenge_module) if challenge_module else ""
        challenge_decls = (
            declarations_in(os.path.join(root, challenge_path))
            if challenge_path and os.path.isfile(os.path.join(root, challenge_path))
            else set()
        )

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
                            f"`{name}` exists (in {', '.join(index[name])}) but the "
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
