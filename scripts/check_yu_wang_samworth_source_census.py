#!/usr/bin/env python3
"""Validate the Yu--Wang--Samworth full-paper source census.

The census answers one question the repository could not otherwise answer:
**of everything Yu, Wang & Samworth actually prove, what do we have, and what do
we not?**  Coverage claims made from the Lean side alone are structurally biased
-- they enumerate what was written, not what the paper contains -- so the
manifest is keyed by *source* item and every item exists whether or not anything
formalizes it.

Two independent axes, following the Davis--Kahan 1970 census:

``status``
    The mathematical judgement against the printed source.  A human annotation.

``verification``
    What the Lean build certifies.  Checkable, and checked here.  ``--probe``
    resolves every declaration against the real build, so *resolved* means
    *reachable from a target that is actually built*, not *a string that appears
    somewhere in the tree*.

Schema, vocabularies, declaration references, the embedded `semantic_review`
contract, rendering, and the probe itself are generic and live in
`aiq_lean_tools`.  What remains here is Yu--Wang--Samworth policy: the exact set
of printed source anchors the census must cover, the sections they may live in,
the gap taxonomy, and a summary that leads with what the build guarantees.

Anchors use the PUBLISHED Biometrika numbering (checked against the article on
2026-08-13): Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1.

Before 2026-08-02 the paper package was not a default target, so its theorems
were proved but unguarded: a refactor could break them and CI would stay green.
It joined `defaultTargets` on 2026-08-02 and was renamed `YuWangSamworth2015` on
2026-08-17, so "the paper package represents every numbered result" and "CI
protects every numbered result" are now the same claim.

    python3 scripts/check_yu_wang_samworth_source_census.py           # fast gate
    python3 scripts/check_yu_wang_samworth_source_census.py --probe   # + build resolution
    python3 scripts/check_yu_wang_samworth_source_census.py --probe --sync
    python3 scripts/check_yu_wang_samworth_source_census.py --render  # rewrite the .md
"""
from __future__ import annotations

import argparse
from pathlib import Path

try:
    from aiq_lean_tools.census import load_census
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "dev/yu-wang-samworth-2015-full-source-census.json"
MD_PATH = ROOT / "dev/yu-wang-samworth-2015-full-source-census.md"

#: Every numbered result and every unnumbered mathematical assertion in the paper
#: must have a row.  Losing one is how a census silently becomes a list of what
#: someone happened to formalize.
REQUIRED_ANCHORS = {
    "Section 1, principal angles and sin-Theta",
    "Section 1, equation (1)",
    "Section 1, numerical illustration that delta can vanish",
    "Theorem 1",
    "Theorem 2",
    "Theorem 2, residual form",
    "Section 2, sharpness example with orthogonal target subspaces",
    "Section 2, sharpness scale for nearby one-dimensional eigenspaces",
    "Equation (4)",
    "Corollary 1",
    "Section 3, audit of statistical applications",
    "Theorem 3",
    "Theorem 3, rank-boundary convention",
    "Appendix, equations (A7)-(A8)",
    "Lemma A1",
}

ALLOWED_SECTIONS = {"1", "2", "3", "4", "appendix"}
REQUIRED_TEXT_FIELDS = ("source_kind", "source_anchor", "title", "summary", "notes", "next_action")
GAP_KINDS = {"hard_math", "mechanical", "source_audit", "not_proof_debt"}

#: Both are default targets, so a declaration reachable from either is guarded by
#: `lake build`.  They are listed separately because the census records results
#: carried by the shared Davis--Kahan library as well as by the paper package.
PROBE_IMPORTS = ["DavisKahan.All", "YuWangSamworth2015"]


def fail(message: str) -> None:
    print(f"ERROR: {message}")
    raise SystemExit(1)


def check_yws_policy(data: dict) -> list[dict]:
    items = data["items"]

    # An empty gaps table would mean the census has stopped recording what is
    # missing, which is indistinguishable from having nothing missing.
    gaps = data.get("gaps")
    if not isinstance(gaps, dict) or not gaps:
        fail("a nonempty gaps table is required -- an empty one means the census "
             "has stopped recording what is missing")
    for key, gap in gaps.items():
        if gap.get("kind") not in GAP_KINDS:
            fail(f"gap {key} has invalid kind: {gap.get('kind')!r}")
        for field in ("title", "detail"):
            if not isinstance(gap.get(field), str) or not gap[field].strip():
                fail(f"gap {key} has empty {field}")

    anchors: set[str] = set()
    referenced: set[str] = set()
    for item in items:
        item_id = item["id"]
        if item.get("section") not in ALLOWED_SECTIONS:
            fail(f"invalid section for {item_id}: {item.get('section')!r}")
        for key in REQUIRED_TEXT_FIELDS:
            if not isinstance(item.get(key), str) or not item[key].strip():
                fail(f"{item_id} has empty {key}")
        if not isinstance(item.get("gap_refs"), list):
            fail(f"{item_id} must carry a gap_refs list")
        referenced.update(item["gap_refs"])
        anchors.add(item["source_anchor"])

    missing_anchors = sorted(REQUIRED_ANCHORS - anchors)
    if missing_anchors:
        fail("missing numbered source anchors: " + ", ".join(missing_anchors))
    orphan = sorted(set(gaps) - referenced)
    if orphan:
        fail("gaps referenced by no item: " + ", ".join(orphan))
    return items


def report(items: list[dict]) -> None:
    """Lead with what the default build guarantees.

    The old summary opened with "CLEAN" and reported 19 "formalized", folding
    `proved_outside_build` and `partially_in_build` in with the 10 results the
    build actually guards -- so a number that read as progress counted nine
    results the build could not see, which is exactly how a target outside
    `defaultTargets` rots unnoticed.
    """
    total = len(items)
    guarded = sum(1 for i in items if i["verification"] == "proved_in_build")
    outside = sum(1 for i in items if i["verification"] == "proved_outside_build")
    partial = sum(1 for i in items if i["verification"] == "partially_in_build")
    debt = sum(1 for i in items if i["verification"] == "absent" and i["status"] != "not_proof_debt")
    print(f"Yu--Wang--Samworth full source census: {guarded}/{total} proved in the default "
          f"build ({outside} proved outside it, {partial} partial, {debt} unformalized and "
          "still proof debt)")
    at_risk = sorted(i["id"] for i in items
                     if i["verification"] in {"proved_outside_build", "partially_in_build"})
    if at_risk:
        print("  proved but unguarded by `lake build`: " + ", ".join(at_risk))
    missing = sorted(i["id"] for i in items if i["verification"] == "absent")
    if missing:
        print("  not proved: " + ", ".join(missing))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--probe", action="store_true",
                        help="resolve every declaration against the real build")
    parser.add_argument("--sync", action="store_true",
                        help="with --probe, rewrite verification fields the build disagrees with")
    parser.add_argument("--render", action="store_true", help="rewrite the Markdown view")
    args = parser.parse_args(argv)

    document = load_census(JSON_PATH, root=ROOT)
    findings = document.validate()
    for finding in findings:
        print(f"{finding.level.upper():8s}{finding.location}: [{finding.code}] {finding.message}")
    if any(f.level == "error" for f in findings):
        return 1

    items = check_yws_policy(document.data)

    if args.probe:
        probe = document.probe(imports=PROBE_IMPORTS)
        if probe.unresolved:
            print("unresolved against every probe target:")
            for name in probe.unresolved:
                module = probe.private_declarations.get(name)
                if module:
                    print(f"  {name}  [declared PRIVATE in {module} -- proved but not citable; "
                          "do not list it as the evidence for a source item]")
                else:
                    print(f"  {name}  [no declaration of this name exists]")
        changed = document.apply_probe(probe)
        if changed and not args.sync:
            fail(f"{changed} item(s) record a verification the build does not support; "
                 "re-run with --probe --sync to correct")
        if args.sync:
            document.write()
            print(f"census sync: {changed} row(s) updated from the build")
        items = document.data["items"]

    rendered = document.render_markdown()
    if args.render or args.sync:
        MD_PATH.write_text(rendered, encoding="utf-8")
    elif not MD_PATH.exists() or MD_PATH.read_text(encoding="utf-8") != rendered:
        fail(f"{MD_PATH.relative_to(ROOT)} is stale; re-run with --render")

    report(items)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
