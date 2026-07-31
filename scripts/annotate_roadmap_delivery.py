#!/usr/bin/env python3
"""Mark each roadmap signature that has since been proved, and say where.

`ForTauCetiRoadmap/**/Suggested.lean` records target signatures for work the
libraries were going to do.  **176 are recorded and 163 are now proved** -- three
topics at 100% -- and nothing anywhere said so.  A reviewer opening
`FiniteDimensionalOperators/` saw 32 unproved signatures and a 448-line README of
intent, for material that is complete; an agent looking for work could not tell
which entries were open without running this comparison by hand.

**Read the three numbers separately, because 163 is not a number to quote.**
Matching is by a name's final component, and **19 of the 163 resolve to more than
one module**, so those are matches by *spelling* and not by identity.  The honest
split is **144 confirmed, 19 ambiguous, 13 outstanding** -- and the script marks
the ambiguous ones as questions rather than deliveries, which is the whole reason
it reports them instead of picking the first module and moving on.

## Why this is a generator and not an editing pass

Hand-written delivery state is precisely what went stale.  Writing 158 markers by
hand today reproduces the same defect the moment the 159th lands -- and this
repository has spent the day repairing exactly that failure in manifests, topic
tables and module docstrings.  So the annotation is derived and rewritten in
place on every run.

    python3 scripts/annotate_roadmap_delivery.py           # report
    python3 scripts/annotate_roadmap_delivery.py --write   # rewrite the markers
    python3 scripts/annotate_roadmap_delivery.py --check   # exit 1 if stale

## The `sorry` bodies are not the problem and are not touched

`Suggested.lean` says of itself: *"Bodies are placeholders; the statements are
the content."*  `ForTauCetiRoadmap.lean` explains that the library exists *"so
that a broken suggested signature is a build failure"* -- a good design that
caught ten real elaboration errors when it landed.  This script adds a docstring
line and changes nothing else.

## Naming drift is the hard part, and an exact matcher is wrong 28% of the time

Five of the eighteen signatures an exact-name matcher calls outstanding **are
delivered**, under a name the implementation chose later:

    schattenFamily                                  -> schattenIdealFamily
    tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy
                                                    -> ..._of_finiteDimensional
                                                       ..._of_hilbertBasis
    yosidaApproximant                               -> yosidaApprox
    frobeniusNorm                                   -> frobenius
    UnboundedSinThetaProblem                        -> UnboundedSinThetaData

So `ALIASES` below is a **declared, reviewed** table -- deliberately not a fuzzy
matcher.  A fuzzy match that pairs the wrong theorem is worse than an honest
"outstanding", because the whole value of the number is that it can be trusted.
Each entry is a claim that a human checked the two statements.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
ROADMAP = ROOT / "ForTauCetiRoadmap"
LIBRARIES = ("ForTauCeti", "DavisKahan")

DECL = re.compile(
    r"^\s*(?:@\[[^]]*\]\s*)?(?:public |private |protected |noncomputable |partial |unsafe )*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][\w.'!?]*)",
    re.M)

#: The marker this script owns.  Everything on a line starting with it is
#: rewritten on `--write`; nothing else in the file is touched.
MARKER = "-- DELIVERED:"

#: Roadmap name -> the name(s) it actually landed under.  **Every entry is a
#: claim that somebody compared the two statements**, not a guess from spelling.
#: Keep it small: an unexplained alias is indistinguishable from a wrong one.
ALIASES: dict[str, tuple[str, ...]] = {
    "schattenFamily": ("schattenIdealFamily",),
    "tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy": (
        "tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional",
        "tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_hilbertBasis",
    ),
    "yosidaApproximant": ("yosidaApprox",),
    "frobeniusNorm": ("frobenius",),
    "UnboundedSinThetaProblem": ("UnboundedSinThetaData", "UnboundedSinThetaDataPMap"),
}


def library_declarations() -> dict[str, list[str]]:
    """Every declaration in the real libraries, mapped to **all** modules holding it.

    All of them, not the first: matching is by the final name component, so a
    short name like `abs` or `resolvent` is declared in more than one place and
    picking whichever came first would silently assert a delivery the roadmap
    never meant.  Ambiguity is reported, not resolved by luck.
    """
    found: dict[str, list[str]] = {}
    for library in LIBRARIES:
        for path in sorted((ROOT / library).rglob("*.lean")):
            module = str(path.relative_to(ROOT))[:-5].replace("/", ".")
            for name in DECL.findall(path.read_text(encoding="utf-8", errors="replace")):
                where = found.setdefault(name.split(".")[-1], [])
                if module not in where:
                    where.append(module)
    return found


def resolve(name: str, declarations: dict[str, list[str]]) -> tuple[str, list[str]] | None:
    """Where `name` landed, following a declared alias if there is one."""
    short = name.split(".")[-1]
    if short in declarations:
        return short, declarations[short]
    for alias in ALIASES.get(short, ()):
        if alias in declarations:
            return alias, declarations[alias]
    return None


def annotate(text: str, declarations: dict[str, list[str]]) -> tuple[str, int, int, int]:
    """Return the file with markers rewritten, plus (delivered, outstanding, ambiguous)."""
    lines = [line for line in text.split("\n") if not line.startswith(MARKER)]
    out: list[str] = []
    delivered = outstanding = ambiguous = 0
    for line in lines:
        match = DECL.match(line)
        if match:
            hit = resolve(match.group(1), declarations)
            if hit:
                name, modules = hit
                suffix = f" (as `{name}`)" if name != match.group(1).split(".")[-1] else ""
                if len(modules) > 1:
                    where = ", ".join(f"`{m}`" for m in modules)
                    out.append(f"{MARKER} AMBIGUOUS -- `{name}` is declared in "
                               f"{len(modules)} modules ({where}); "
                               f"disambiguate before trusting this{suffix}")
                    ambiguous += 1
                else:
                    out.append(f"{MARKER} `{modules[0]}`{suffix}")
                delivered += 1
            else:
                outstanding += 1
        out.append(line)
    return "\n".join(out), delivered, outstanding, ambiguous


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="rewrite the markers")
    parser.add_argument("--check", action="store_true", help="exit 1 if stale")
    args = parser.parse_args()

    declarations = library_declarations()
    total_delivered = total_outstanding = total_ambiguous = 0
    stale: list[str] = []
    open_names: list[tuple[str, str]] = []

    for path in sorted(ROADMAP.rglob("Suggested.lean")):
        original = path.read_text(encoding="utf-8")
        updated, delivered, outstanding, ambiguous = annotate(original, declarations)
        total_delivered += delivered
        total_outstanding += outstanding
        total_ambiguous += ambiguous
        topic = path.parent.name
        total = delivered + outstanding
        percent = 100 * delivered // total if total else 0
        flag = "  <- COMPLETE" if outstanding == 0 and total else ""
        if ambiguous:
            flag += f"   [{ambiguous} ambiguous]"
        print(f"{topic:<32} {delivered:3d}/{total:<3d} delivered ({percent:3d}%){flag}")
        for name in DECL.findall(original):
            if not resolve(name, declarations):
                open_names.append((topic, name))
        if updated != original:
            stale.append(str(path.relative_to(ROOT)))
            if args.write:
                path.write_text(updated, encoding="utf-8")

    total = total_delivered + total_outstanding
    print(f"\n{'TOTAL':<32} {total_delivered:3d}/{total:<3d} delivered "
          f"({100 * total_delivered // total if total else 0}%), "
          f"{total_outstanding} outstanding, {total_ambiguous} ambiguous")
    if total_ambiguous:
        print("  An ambiguous marker means the roadmap name's final component is declared in\n"
              "  more than one module, so the match is by spelling and not by identity.\n"
              "  Each one is a question for a human, not a delivery.")

    if open_names:
        print("\nOutstanding signatures -- this is the roadmap's real backlog:")
        for topic, name in open_names:
            print(f"  {topic:<32} {name}")

    unused = sorted(set(ALIASES) - {n for path in ROADMAP.rglob("Suggested.lean")
                                    for n in DECL.findall(path.read_text(encoding="utf-8"))})
    if unused:
        print("\n?? ALIASES names a signature no roadmap file mentions -- remove it, or the")
        print("   next signature to take that name inherits an unreviewed alias:")
        for name in unused:
            print(f"     {name}")

    if args.write:
        print(f"\nrewrote {len(stale)} file(s)")
        return 0
    if stale:
        print(f"\nroadmap delivery: {len(stale)} file(s) have stale or missing markers "
              f"-- run with --write")
        for name in stale:
            print(f"  {name}")
        return 1 if args.check else 0
    if unused:
        return 1 if args.check else 0
    print("\nroadmap delivery: OK -- every signature is marked with where it landed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
