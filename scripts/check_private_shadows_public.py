#!/usr/bin/env python3
"""Refuse a `private` declaration whose name already exists publicly in its own imports.

A module that restates something it already imports is duplication, which the
`reuse` rubric treats as a block.  The interesting case is that it does not look
like duplication from inside the file: the copy is `private`, so nothing outside
can see the clash, and the compiler is perfectly happy.

**This gate exists because that pattern cost 317 lines.**
`DavisKahan/OperatorIdeal/ApproximationNumbers/Real/Threshold.lean` carried a
`private` copy of thirty transport lemmas that were, declaration for
declaration, the public API of a module it imported.  Deleting the copy exposed
the reason it was written: the public lemmas bound both spaces in one universe,
the consumer needed two, so the imported lemmas silently failed to apply and
restating them locally was the cheapest way forward.

That is the general shape and the reason to check the *name* rather than the
cause.  A lemma that does not apply -- wrong universe, wrong instance, wrong
variable order -- never says so.  It just fails to unify, and a local copy is
always the shortest path.  The copy is the visible symptom, and it is visible
without a compiler:

    python3 scripts/check_private_shadows_public.py           # report
    python3 scripts/check_private_shadows_public.py --check   # exit 1 above baseline

## Not every hit is a defect

A thin wrapper that restates an imported theorem in a different *presentation*
and then delegates to it in one line is reuse, not duplication -- both hits on
the first run were exactly that.  Such a wrapper is legitimate and belongs in
the baseline; what does not is a `private` declaration with a real proof body
that repeats one already available.

The baseline is therefore a list of accepted pairs rather than a count, so that
adding an accepted wrapper is a deliberate edit naming the wrapper, and a new
copy of an existing proof is a failure even if an old wrapper is retired the
same day.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

#: Libraries to scan.  `vendor/` is excluded: it is not ours to restructure.
LIBS = ["ForTauCeti", "DavisKahan", "Challenge"]

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable |protected |private |scoped )*"
    r"(?:theorem|lemma|def|abbrev|instance) ([A-Za-z_][\w']*)",
    re.M,
)
PRIVATE_RE = re.compile(
    r"^private (?:noncomputable )?(?:theorem|lemma|def|abbrev) ([A-Za-z_][\w']*)",
    re.M,
)
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)\s*$", re.M)

#: Accepted `(module, private name)` pairs: presentation wrappers that delegate.
#:
#: The single entry restates `TauCeti.re_inner_reducedExtension_self` for
#: `E →L[𝕜] E` with `Reduces`, and its proof is a `rw` followed by `exact` on the
#: imported theorem.  It is the reason this gate reports pairs and not a count.
#:
#: `SinTheta/OperatorNorm.lean` carries the same kind of wrapper and is
#: deliberately **not** here: it is named `re_inner_reducedExtension_self'`, so it
#: does not shadow anything and this gate never sees it.  A prime is enough to
#: make the pattern invisible, which is worth knowing before trusting a clean run
#: -- the check finds *reused names*, and a copy under a fresh name is a job for
#: `scripts/audit_scan.py --dup`.
BASELINE: set[tuple[str, str]] = {
    (
        "ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/SinTheta.lean",
        "re_inner_reducedExtension_self",
    ),
}


def lean_files() -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for lib in LIBS:
        root = ROOT / lib
        if root.is_dir():
            out.extend(sorted(root.rglob("*.lean")))
    return out


def module_name(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def scan(files: list[pathlib.Path]) -> list[tuple[str, list[str]]]:
    """Return `(module path, shadowed names)` for every module with a hit."""
    public: dict[str, set[str]] = {}
    private: dict[pathlib.Path, set[str]] = {}
    imports: dict[str, set[str]] = {}
    for path in files:
        text = path.read_text(encoding="utf-8")
        priv = set(PRIVATE_RE.findall(text))
        mod = module_name(path)
        public[mod] = set(DECL_RE.findall(text)) - priv
        imports[mod] = set(IMPORT_RE.findall(text))
        if priv:
            private[path] = priv

    def closure(mod: str) -> set[str]:
        seen: set[str] = set()
        stack = list(imports.get(mod, ()))
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            stack.extend(imports.get(m, ()))
        return seen

    findings: list[tuple[str, list[str]]] = []
    for path, priv in private.items():
        available: set[str] = set()
        for m in closure(module_name(path)):
            available |= public.get(m, set())
        shadowed = sorted(priv & available)
        if shadowed:
            findings.append((str(path.relative_to(ROOT)), shadowed))
    findings.sort()
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 above the baseline")
    args = parser.parse_args()

    findings = scan(lean_files())
    pairs = {(mod, name) for mod, names in findings for name in names}
    new = sorted(pairs - BASELINE)
    stale = sorted(BASELINE - pairs)

    for mod, names in findings:
        for name in names:
            mark = "  " if (mod, name) in BASELINE else "->"
            print(f"{mark} {mod}: private `{name}` is already public in its imports")
    for mod, name in stale:
        print(f"?? baseline entry no longer present: {mod}: `{name}`")

    if new:
        print(
            f"\nprivate-shadows-public check: {len(new)} finding(s) above the baseline.\n"
            "  A `private` declaration repeating one its own module already imports is\n"
            "  duplication.  If the copy exists because the imported lemma does not\n"
            "  apply, fix the lemma -- a universe, an instance or a variable order --\n"
            "  rather than restating it.  If it is a presentation wrapper that\n"
            "  delegates in one line, add it to BASELINE with the reason."
        )
        return 1 if args.check else 0
    if stale:
        print(
            f"\nprivate-shadows-public check: {len(stale)} stale baseline entry(ies).\n"
            "  Remove them: a baseline naming a declaration that no longer exists\n"
            "  silently accepts the next declaration to take that name."
        )
        return 1 if args.check else 0
    print(
        f"private-shadows-public check: OK "
        f"({len(pairs)} accepted wrapper(s), 0 above the baseline)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
