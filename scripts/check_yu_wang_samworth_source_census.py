#!/usr/bin/env python3
"""Validate the Yu--Wang--Samworth full-paper source census.

The census answers one question the repository could not otherwise answer:
**of everything Yu, Wang & Samworth actually prove, what do we have, and what
do we not?**  Coverage claims made from the Lean side alone are structurally
biased -- they enumerate what was written, not what the paper contains -- so
the manifest is keyed by *source* item and every item exists whether or not
anything formalizes it.

Two independent axes, following the Davis--Kahan 1970 census:

``status``
    The mathematical judgement against the printed source.  A human annotation.

``verification``
    What the Lean build certifies.  Checkable, and checked here.  ``--probe``
    resolves every declaration against the real build by emitting a Lean file
    that imports the build targets and ``#check``s each fully qualified name,
    so *resolved* means *reachable from a target that is actually built*, not
    *a string that appears somewhere in the tree*.

``FinishYuWangSamworth`` used not to be a default target, so its theorems were
proved but unguarded: a refactor could break them and CI would stay green.  Nine
rows sat in ``proved_outside_build``, including Theorem 1, both halves of
Theorem 4, Lemma 5 and the appendix Gram identities -- the paper's headline
results, none of them protected.  It joined ``defaultTargets`` on 2026-08-02
(sorry-free across all 12 files), so "the lane represents every numbered result"
and "CI protects every numbered result" are now the same claim.

Usage:
    python3 scripts/check_yu_wang_samworth_source_census.py           # fast gate
    python3 scripts/check_yu_wang_samworth_source_census.py --probe   # + build resolution
    python3 scripts/check_yu_wang_samworth_source_census.py --probe --sync
    python3 scripts/check_yu_wang_samworth_source_census.py --render  # rewrite the .md
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "dev/yu-wang-samworth-2015-full-source-census.json"
MD_PATH = ROOT / "dev/yu-wang-samworth-2015-full-source-census.md"
PROBE_PATH = ROOT / "dev/.yws-census-probe.lean"

# Every numbered result and every unnumbered mathematical assertion in the
# paper must have a row.  Losing one is how a census silently becomes a list of
# what someone happened to formalize.
# Anchors use the PUBLISHED Biometrika numbering (checked against the article on
# 2026-08-13): Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1.  The 2014
# preprint shares one counter and numbers the last three Corollary 3, Theorem 4
# and Lemma 5; many Lean names still spell that, which the census records as gap
# `preprint-numbering-aliases` rather than by renaming pinned declarations.
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

# Targets the probe imports.  Order matters only for the report: a declaration
# is attributed to the first target that resolves it, so a name reachable from
# the default build is never mis-reported as completion-lane-only.
PROBE_TARGETS = [
    ("in_build", "DavisKahan.All"),
    ("completion_lane", "FinishYuWangSamworth"),
]

# A name that must never resolve.  If Lean's diagnostics change shape the
# parser would otherwise report universal success; the run refuses to report
# unless this still fails.
CANARY = "TauCeti.DavisKahanTheory.YwsCensusProbeCanaryMustNotResolve"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |scoped )*"
    r"(?:alias|theorem|lemma|def|abbrev|structure|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
    re.M,
)


def fail(message: str) -> None:
    print(f"ERROR: {message}")
    raise SystemExit(1)


# ---------------------------------------------------------------- schema ----

def check_schema(data: dict) -> list[dict]:
    items = data.get("items")
    if not isinstance(items, list) or not items:
        fail("items must be a nonempty list")
    statuses = set(data.get("status_definitions", {}))
    verifications = set(data.get("verification_definitions", {}))
    if not statuses:
        fail("status_definitions is required")
    if not verifications:
        fail("verification_definitions is required")
    gaps = data.get("gaps")
    if not isinstance(gaps, dict) or not gaps:
        fail("a nonempty gaps table is required -- an empty one means the "
             "census has stopped recording what is missing")
    for key, gap in gaps.items():
        if gap.get("kind") not in {"hard_math", "mechanical", "source_audit",
                                   "not_proof_debt"}:
            fail(f"gap {key} has invalid kind: {gap.get('kind')!r}")
        for field in ("title", "detail"):
            if not isinstance(gap.get(field), str) or not gap[field].strip():
                fail(f"gap {key} has empty {field}")

    ids: set[str] = set()
    anchors: set[str] = set()
    referenced: set[str] = set()
    for item in items:
        item_id = item.get("id")
        if not item_id or item_id in ids:
            fail(f"missing or duplicate item id: {item_id!r}")
        ids.add(item_id)
        if item.get("section") not in ALLOWED_SECTIONS:
            fail(f"invalid section for {item_id}: {item.get('section')!r}")
        if item.get("status") not in statuses:
            fail(f"invalid status for {item_id}: {item.get('status')!r}")
        if item.get("verification") not in verifications:
            fail(f"invalid verification for {item_id}: "
                 f"{item.get('verification')!r}")
        for key in ("source_kind", "source_anchor", "title", "summary",
                    "notes", "next_action"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                fail(f"{item_id} has empty {key}")
        missing = item.get("gap_refs")
        if not isinstance(missing, list):
            fail(f"{item_id} must carry a gap_refs list")
        for key in missing:
            if key not in gaps:
                fail(f"{item_id} references gap {key!r}, absent from gaps")
            referenced.add(key)
        anchors.add(item["source_anchor"])

    missing_anchors = sorted(REQUIRED_ANCHORS - anchors)
    if missing_anchors:
        fail("missing numbered source anchors: " + ", ".join(missing_anchors))
    orphan = sorted(set(gaps) - referenced)
    if orphan:
        fail("gaps referenced by no item: " + ", ".join(orphan))
    return items


def check_names(items: list[dict]) -> None:
    """Cheap existence check by short name.

    Deliberately weak -- it matches only the segment after the last dot, so a
    reference in the wrong namespace passes.  It is here to catch deletions and
    renames without a Lean build; ``--probe`` is the authoritative check.
    """
    # Dot-directories are skipped by rule rather than by name.  Like the
    # DavisKahan1970 census this only *adds* to `declared`, so an extra checkout
    # in range cannot fail the gate -- it can only satisfy a pin the real tree
    # has stopped satisfying.  `.claude/worktrees/` is a full second copy of
    # this repo and would do precisely that.
    text = "\n".join(
        path.read_text(errors="ignore")
        for path in ROOT.rglob("*.lean")
        if "external" not in path.parts
        and not any(part.startswith(".") for part in path.relative_to(ROOT).parts)
    )
    declared = set(DECL_RE.findall(text))
    for item in items:
        for ref in item.get("lean_declarations") or []:
            if ref.rsplit(".", 1)[-1] not in declared:
                fail(f"unresolved Lean declaration for {item['id']}: {ref}")
        for ref in item.get("planned_declarations") or []:
            if ref.rsplit(".", 1)[-1] in declared:
                fail(f"{item['id']} lists {ref} as planned, but it now exists; "
                     f"move it into lean_declarations")


# ----------------------------------------------------------------- probe ----

PRIVATE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*private\s+(?:noncomputable\s+)?"
    r"(?:alias|theorem|lemma|def|abbrev|structure|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
    re.M,
)


def private_declarations() -> dict[str, str]:
    """Short name -> file, for every `private` declaration in the tree."""
    out: dict[str, str] = {}
    for path in ROOT.rglob("*.lean"):
        if "external" in path.parts or any(
            part.startswith(".") for part in path.relative_to(ROOT).parts
        ):
            continue
        for name in PRIVATE_RE.findall(path.read_text(errors="ignore")):
            out.setdefault(name, str(path.relative_to(ROOT)))
    return out


def probe(items: list[dict]) -> dict[str, str]:
    """Resolve every declaration against the real build.

    Returns {declaration: target key or 'unresolved'}.  One Lean file and one
    ``lake`` invocation per target covers the whole census.
    """
    decls: list[str] = []
    for item in items:
        for ref in item.get("lean_declarations") or []:
            if ref not in decls:
                decls.append(ref)

    resolved: dict[str, str] = {d: "unresolved" for d in decls}
    for key, target in PROBE_TARGETS:
        pending = [d for d in decls if resolved[d] == "unresolved"]
        if not pending:
            break
        lines = [f"import {target}\n"]
        for index, decl in enumerate(pending):
            lines.append(f"-- probe {index}\n#check @{decl}\n")
        lines.append(f"-- probe {len(pending)}\n#check @{CANARY}\n")
        PROBE_PATH.write_text("".join(lines), encoding="utf8")
        result = subprocess.run(
            ["lake", "env", "lean", str(PROBE_PATH)],
            cwd=ROOT, capture_output=True, text=True,
        )
        output = result.stdout + result.stderr
        # Lean prefixes diagnostics with the path it was handed, which is
        # absolute here; anchoring on the file name rather than on a relative
        # path is what keeps this from silently matching nothing.
        bad = set()
        for match in re.finditer(
                re.escape(PROBE_PATH.name) + r":(\d+):\d+: error", output):
            bad.add(int(match.group(1)))
        # Map error lines back to declarations: each probe occupies two lines
        # after the single import line.
        for index, decl in enumerate(pending):
            if (3 + 2 * index) not in bad:
                resolved[decl] = key
        canary_line = 3 + 2 * len(pending)
        if canary_line not in bad:
            fail("the probe canary resolved -- the diagnostic parser is broken "
                 "and every result in this run is meaningless")
    PROBE_PATH.unlink(missing_ok=True)
    return resolved


def derive_verification(item: dict, resolved: dict[str, str]) -> str:
    decls = item.get("lean_declarations") or []
    if not decls:
        return "not_applicable" if item["status"] == "not_proof_debt" else "absent"
    where = {resolved.get(d, "unresolved") for d in decls}
    if "unresolved" in where:
        return "partially_in_build" if where - {"unresolved"} else "absent"
    # `FinishYuWangSamworth` joined `defaultTargets` on 2026-08-02, so a
    # declaration reachable from it is guarded by `lake build` exactly as one in
    # `DavisKahan.All` is.  The two keys are still probed separately because
    # knowing *which* library carries a result is useful, but neither is
    # "outside the build" any more, and `proved_outside_build` is now
    # unreachable from this function rather than merely unused.
    if where <= {"in_build", "completion_lane"}:
        return "proved_in_build"
    return "partially_in_build"


# ---------------------------------------------------------------- render ----

def render(data: dict) -> str:
    items = data["items"]
    counts: dict[str, int] = {}
    for item in items:
        counts[item["verification"]] = counts.get(item["verification"], 0) + 1
    out = [
        "<!-- generated by scripts/check_yu_wang_samworth_source_census.py "
        "--render; edit the JSON, not this file -->",
        "",
        "# Yu--Wang--Samworth full-paper source census",
        "",
        data["primary_source"]["citation"],
        "",
        data["how_to_use"],
        "",
        "## Headline",
        "",
        f"**{len(items)} source items.**",
        "",
        "| verification | items |",
        "| --- | --- |",
    ]
    for key in sorted(counts):
        out.append(f"| `{key}` | {counts[key]} |")
    out += ["", "## Items", "",
            "| id | section | source anchor | title | status | verification |",
            "| --- | --- | --- | --- | --- | --- |"]
    for item in items:
        out.append(
            f"| `{item['id']}` | {item['section']} | {item['source_anchor']} | "
            f"{item['title']} | `{item['status']}` | `{item['verification']}` |"
        )
    out += ["", "## Gaps", ""]
    for key, gap in data["gaps"].items():
        out += [f"### `{key}` ({gap['kind']}) — {gap['title']}", "",
                gap["detail"], ""]
    out += ["## Detail", ""]
    for item in items:
        out += [f"### `{item['id']}` — {item['title']}", "",
                f"* **source anchor**: {item['source_anchor']} "
                f"({item['source_kind']}, section {item['section']})",
                f"* **summary**: {item['summary']}",
                f"* **status**: `{item['status']}` / "
                f"**verification**: `{item['verification']}`"]
        for label, key in (("lean declarations", "lean_declarations"),
                           ("planned declarations", "planned_declarations")):
            names = item.get(key) or []
            if names:
                out.append(f"* **{label}**: " +
                           ", ".join(f"`{n}`" for n in names))
        if item["gap_refs"]:
            out.append("* **gaps**: " +
                       ", ".join(f"`{g}`" for g in item["gap_refs"]))
        out += [f"* **notes**: {item['notes']}",
                f"* **next action**: {item['next_action']}", ""]
    return "\n".join(out) + "\n"


# ------------------------------------------------------------------ main ----

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe", action="store_true",
                        help="resolve every declaration against the real build")
    parser.add_argument("--sync", action="store_true",
                        help="with --probe, rewrite verification fields")
    parser.add_argument("--render", action="store_true",
                        help="rewrite the markdown view")
    args = parser.parse_args()

    data = json.loads(JSON_PATH.read_text(encoding="utf8"))
    items = check_schema(data)
    check_names(items)

    if args.probe:
        resolved = probe(items)
        drift = []
        for item in items:
            derived = derive_verification(item, resolved)
            if derived != item["verification"]:
                drift.append((item["id"], item["verification"], derived))
                if args.sync:
                    item["verification"] = derived
        unresolved = sorted(d for d, w in resolved.items() if w == "unresolved")
        if unresolved:
            # Distinguish "gone" from "present but private".  They look
            # identical to a `#check` and mean opposite things: a missing name
            # is lost mathematics, a private name is mathematics that exists
            # and cannot be cited.  A census that conflates them will report a
            # proved result as absent, or an absent one as proved.
            private = private_declarations()
            print("unresolved against every probe target:")
            for name in unresolved:
                short = name.rsplit(".", 1)[-1]
                if short in private:
                    print(f"  {name}  [declared PRIVATE in {private[short]} -- "
                          f"proved but not citable; do not list it as the "
                          f"evidence for a source item]")
                else:
                    print(f"  {name}  [no declaration of this name exists]")
        if drift:
            print("verification drift (recorded -> measured):")
            for item_id, was, now in drift:
                print(f"  {item_id}: {was} -> {now}")
            if not args.sync:
                fail(f"{len(drift)} item(s) record a verification the build "
                     f"does not support; re-run with --sync to correct")
        if args.sync:
            JSON_PATH.write_text(
                json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                encoding="utf8")

    rendered = render(data)
    if args.render or args.sync:
        MD_PATH.write_text(rendered, encoding="utf8")
    elif not MD_PATH.exists() or MD_PATH.read_text(encoding="utf8") != rendered:
        fail(f"{MD_PATH.relative_to(ROOT)} is stale; re-run with --render")

    # Lead with what the default build guarantees.  The old summary opened with
    # "CLEAN" and reported 19 "formalized", folding `proved_outside_build` and
    # `partially_in_build` in with the 10 results the build actually guards --
    # so a number that reads as progress counted nine results the build cannot
    # see, which is exactly how a target outside `defaultTargets` rots unnoticed.
    total = len(items)
    guarded = sum(1 for i in items if i["verification"] == "proved_in_build")
    outside = sum(1 for i in items if i["verification"] == "proved_outside_build")
    partial = sum(1 for i in items if i["verification"] == "partially_in_build")
    debt = sum(1 for i in items if i["verification"] == "absent"
               and i["status"] != "not_proof_debt")
    print(f"Yu--Wang--Samworth full source census: {guarded}/{total} proved in "
          f"the default build ({outside} proved outside it, {partial} partial, "
          f"{debt} unformalized and still proof debt)")

    at_risk = sorted(i["id"] for i in items
                     if i["verification"] in {"proved_outside_build",
                                              "partially_in_build"})
    if at_risk:
        print("  proved but unguarded by `lake build`: " + ", ".join(at_risk))
    missing = sorted(i["id"] for i in items if i["verification"] == "absent")
    if missing:
        print("  not proved: " + ", ".join(missing))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
