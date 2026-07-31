#!/usr/bin/env python3
"""Report, per roadmap topic, which suggested signatures are proved in the library.

`ForTauCetiRoadmap/**/Suggested.lean` records target signatures whose bodies are
deliberately `sorry` -- `ForTauCetiRoadmap.lean` exists so that a broken suggested
signature is a build failure, and that guard has caught real elaboration errors.
The bodies are therefore NOT the finding and this script never looks at them.  What
it answers is the other question: *which of those target signatures already have a
declaration of that name in the libraries*, so that whoever plans work can see where
the staged tree stands.

**This is an internal diagnostic and its output does not belong in a roadmap.**  A
name match is evidence about spelling, not about mathematics: it does not check that
the two statements agree, and roughly one match in eight resolves to more than one
module.  Roadmap prose states what the mathematics should be; it is reviewed by
reading it, not by running this.

**Why this is a script and not a `grep`.**  The first hand-rolled check of
`MajorizationAndAngles` reported **17 of 26 signatures missing**, including
`cosThetaMap`, `kyFanSum`, `cosPrincipalAngles`, `prefixSum` and `sinThetaSq` --
every one of which is present in the tree.  A per-name pattern cannot survive the
variation in real Lean declaration syntax:

* `_root_.` prefixes (`_root_.LinearMap.IsPositive.sqrt` -- this one produced a
  false negative in a *second*, independent check);
* attribute lines, `@[simp] theorem foo ...` inline or on the preceding line;
* modifiers (`noncomputable`, `protected`, `scoped`, `private`);
* namespace qualification, so the roadmap's short name is a suffix of the real one;
* signatures that wrap, putting the name far from the keyword.

So: index every declaration in the libraries **once**, key it on both the
fully-qualified and the base name, and set-compare.  Do not grep per name.

Exit status is always 0: an unmatched signature is ordinary outstanding work, not a
defect.

Usage:
    python3 scripts/check_roadmap_delivered.py               # per-roadmap summary
    python3 scripts/check_roadmap_delivered.py --topic OperatorIdeals
    python3 scripts/check_roadmap_delivered.py --missing     # list what is outstanding
    python3 scripts/check_roadmap_delivered.py --map         # per-signature destinations
    python3 scripts/check_roadmap_delivered.py --json
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
ROADMAP = REPO / "ForTauCetiRoadmap"
LIBS = ("ForTauCeti", "DavisKahan")

# A declaration head.  Deliberately permissive about everything that precedes the
# name, because each of these prefixes has produced a false negative in practice.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |noncomputable |partial |scoped |unsafe )*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|opaque)\s+"
    r"(?:_root_\.)?([A-Za-z_][A-Za-z0-9_'.’]*)",
    re.M,
)

def strip_block_comments(text: str) -> str:
    """Blank out `/- ... -/` regions so prose cannot look like a declaration.

    Wrapped docstring prose that happens to begin a line with `theorem` or `def`
    is the classic way these scans overcount; the roadmap files are prose-heavy,
    so this matters more here than usual.
    """
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif text.startswith("-/", i):
            depth = max(0, depth - 1)
            i += 2
        else:
            out.append(" " if depth else text[i])
            i += 1
    return "".join(out)


def declaration_index() -> dict[str, set[str]]:
    """Every declaration name in the libraries -> the files declaring it.

    Keyed on both the fully-qualified name and its final component, since a
    roadmap file names the theorem without the namespace it eventually lands in.
    """
    index: dict[str, set[str]] = {}
    for lib in LIBS:
        root = REPO / lib
        if not root.exists():
            continue
        for path in root.rglob("*.lean"):
            rel = path.relative_to(REPO).as_posix()
            body = strip_block_comments(path.read_text(errors="replace"))
            for m in DECL.finditer(body):
                full = m.group(1)
                for key in (full, full.split(".")[-1]):
                    index.setdefault(key, set()).add(rel)
    return index


def resolve(hits: set[str]) -> tuple[str, list[str]]:
    """Pick the module a roadmap signature most likely refers to, and report rivals.

    A base name can be declared in several modules, and picking the first
    alphabetically is silently wrong often enough to matter: an early version of
    this script attributed the roadmap's `spectralSubspace` to
    `DavisKahan/Experimental/.../SinTheta/General.lean` -- a `sorry`ed escape --
    rather than to `ForTauCeti/.../Spectral/Subspace.lean`, and `abs` to a
    `DavisKahan/Sources/**` instance file rather than to `Polar/Decomposition`.
    Five of 32 attributions in one published banner were wrong that way.

    The roadmap describes what should land in `ForTauCeti`, so prefer it, then
    prefer the shallowest path (a canonical home sits above a bridge or a
    compatibility shim).  Ambiguity is always REPORTED rather than hidden --
    a confident wrong answer is worse here than a flagged uncertain one.
    """
    ranked = sorted(
        hits,
        key=lambda p: (0 if p.startswith("ForTauCeti/") else 1, p.count("/"), p),
    )
    return ranked[0], ranked[1:]


def topic_signatures(topic_dir: pathlib.Path) -> list[str]:
    suggested = topic_dir / "Suggested.lean"
    if not suggested.exists():
        return []
    body = strip_block_comments(suggested.read_text(errors="replace"))
    seen, out = set(), []
    for m in DECL.finditer(body):
        name = m.group(1)
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def analyse() -> list[dict]:
    index = declaration_index()
    results = []
    for topic_dir in sorted(p.parent for p in ROADMAP.rglob("Suggested.lean")):
        names = topic_signatures(topic_dir)
        if not names:
            continue
        found, missing, ambiguous = {}, [], {}
        for n in names:
            hits = index.get(n) or index.get(n.split(".")[-1])
            if not hits:
                missing.append(n)
                continue
            choice, others = resolve(hits)
            found[n] = choice
            if others:
                ambiguous[n] = sorted(hits)
        results.append({
            "topic": topic_dir.name,
            "total": len(names),
            "delivered": len(found),
            "missing": missing,
            "map": found,
            "ambiguous": ambiguous,
        })
    return results


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--topic", help="restrict to one topic directory name")
    ap.add_argument("--missing", action="store_true", help="list undelivered signatures")
    ap.add_argument("--map", action="store_true", help="list where each signature landed")
    ap.add_argument("--ambiguous", action="store_true",
                    help="list signatures whose name is declared in more than one module")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    results = analyse()
    if args.topic:
        results = [r for r in results if r["topic"] == args.topic]
        if not results:
            print(f"no such topic: {args.topic}")
            return 1

    if args.json:
        print(json.dumps(results, indent=2, sort_keys=True))
        return 0

    for r in results:
        pct = 100.0 * r["delivered"] / r["total"]
        print(f"  {r['topic']:<34} {r['delivered']:>3}/{r['total']:<3} ({pct:5.1f}%)")
        if args.missing and r["missing"]:
            for n in r["missing"]:
                print(f"           outstanding: {n}")
        if args.map:
            for n, loc in sorted(r["map"].items()):
                mark = "  [AMBIGUOUS]" if n in r["ambiguous"] else ""
                print(f"           {n} -> {loc}{mark}")
        if args.ambiguous and r["ambiguous"]:
            for n, hits in sorted(r["ambiguous"].items()):
                print(f"           ambiguous: {n}")
                for h in hits:
                    print(f"               {h}")

    total = sum(r["total"] for r in results)
    done = sum(r["delivered"] for r in results)
    print(f"\nname matches: {done}/{total} suggested signatures have a declaration of "
          f"that name ({100.0 * done / total:.1f}%)" if total else "no signatures found")
    print("A name match is not a proof that the statements agree; this is a planning "
          "aid, not a validation.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
