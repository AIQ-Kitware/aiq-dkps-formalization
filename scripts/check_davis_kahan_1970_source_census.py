#!/usr/bin/env python3
"""Validate the Davis--Kahan 1970 full-paper source census.

Schema, id/status/verification vocabularies, declaration references, the embedded
curated `semantic_review` contract, Markdown rendering, and the compiler probe are
all generic census machinery and live in `aiq_lean_tools`.  What stays here is
Davis--Kahan policy that no other paper shares:

* the exact set of source-claim ids the census must cover, and the sections they
  may live in;
* the `completion_holes` contract and its interaction with hostile certification;
* the blocker taxonomy;
* the refusal to track private source material;
* the reported summary, which must say what is *proved* rather than that the file
  agrees with itself.

Install the tooling once with

    python3 -m pip install -e submodules/aiq-lean-formalization-tools

    python3 scripts/check_davis_kahan_1970_source_census.py
    python3 scripts/check_davis_kahan_1970_source_census.py --no-probe
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

try:
    from aiq_lean_tools.census import load_census
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
MD_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.md"
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"

#: The census must cover exactly these source claims. A count would let one claim
#: leave as another arrives; the explicit set makes either a deliberate edit.
REQUIRED_IDS = {
    "S1-block-residual", "S1-ui-norms",
    "S2-sin-theta", "S2-tan-theta", "S2-sin-two-theta", "S2-tan-two-theta",
    "S2-sharpness", "S2-unbounded-scope",
    "DK-3.1-def", "DK-3.2-def", "DK-3.1-prop", "DK-3.2-prop", "DK-3.3-prop",
    "S3-standing-scope",
    "DK-3.4-prop", "DK-3.1-thm", "DK-3.1-cor", "DK-3.5-prop", "DK-3.2-cor",
    "DK-4.1-prop", "DK-4.1-cor", "DK-4.2-prop", "DK-4.3-prop", "DK-4.4-prop",
    "DK-5.1-thm", "DK-5-hermitian-inequalities", "DK-5.2-thm", "DK-5.1-lem",
    "DK-6.1-lem", "DK-6.2-lem", "DK-6.1-prop", "DK-6.1-thm", "DK-6.2-thm",
    "DK-6.3-thm", "DK-6-appendix", "DK-6.3-lem",
    "DK-7-sin2-proof", "DK-7-tan2-proof",
    "DK-8.1-thm", "DK-8.2-thm",
    "DK-9-model", "DK-9.1-9.4", "DK-9.5-9.7", "DK-9.8",
    "DK-9-infinite-residual-counterexample", "DK-9.9-9.11",
    "DK-10.1", "DK-10.2", "DK-10.3", "DK-10.4",
}
ALLOWED_SECTIONS = {"1", "2", "3", "4", "5", "6", "6 appendix", "7", "8", "9", "10"}
REQUIRED_TEXT_FIELDS = ("source_kind", "source_anchor", "title", "summary", "notes", "next_action")
BLOCKER_KINDS = {"hard_math", "mechanical", "mixed"}

#: The build target the census claims its declarations are reachable from.
#: "Resolved" must mean "reachable from the build", not "exists somewhere on disk".
PROBE_IMPORT = "DavisKahan.All"

#: Private source material must never become tracked. The paper itself is not
#: ours to distribute; the checked-in `DavisKahan1970_part_III.tex` reconstruction
#: is.
PRIVATE_SOURCE_NAMES = ("modernized-transcription", "DavisKahan1970.pdf", "davis-kahan-1970-modernized")


def fail(message: str) -> None:
    print(f"ERROR: {message}")
    raise SystemExit(1)


def check_davis_kahan_policy(data: dict) -> None:
    items = data["items"]
    certifications = set(data.get("completion_certification_definitions", {}))
    if not certifications:
        fail("completion_certification_definitions must be nonempty")
    if not data.get("verification_definitions"):
        fail("schema 4 requires verification_definitions")

    ids = {item["id"] for item in items}
    missing = sorted(REQUIRED_IDS - ids)
    extra = sorted(ids - REQUIRED_IDS)
    if missing:
        fail("missing required source claim ids: " + ", ".join(missing))
    if extra:
        fail("unregistered source claim ids in census: " + ", ".join(extra))

    for item in items:
        item_id = item["id"]
        if item.get("section") not in ALLOWED_SECTIONS:
            fail(f"invalid section for {item_id}: {item.get('section')!r}")
        holes = item.get("completion_holes")
        if not isinstance(holes, list):
            fail(f"{item_id} must carry a completion_holes list")
        for hole in holes:
            if not isinstance(hole, dict) or not isinstance(hole.get("kind"), str) or not hole["kind"]:
                fail(f"{item_id} has malformed completion_hole kind")
            if not isinstance(hole.get("detail"), str) or not hole["detail"].strip():
                fail(f"{item_id} has malformed completion_hole detail")
        if item.get("completion_certification") == "accepted" and holes:
            fail(f"{item_id} is hostile-certified accepted but still records completion_holes")
        for key in REQUIRED_TEXT_FIELDS:
            if not isinstance(item.get(key), str) or not item[key].strip():
                fail(f"{item_id} has empty {key}")
        if not isinstance(item.get("blocked_by"), list):
            fail(f"{item_id} must carry a blocked_by list")

    # An EMPTY blockers table is legal and is the goal state of the campaign.
    # Requiring a nonempty one, combined with the orphan check below, once made
    # "no blockers remain" unrepresentable: retiring the last blocker forced a
    # choice between an orphan failure and keeping a fictional entry.
    blockers = data.get("blockers", {})
    if not isinstance(blockers, dict):
        fail("schema 4 requires a blockers table")
    for key, blocker in blockers.items():
        if blocker.get("kind") not in BLOCKER_KINDS:
            fail(f"blocker {key} has invalid kind: {blocker.get('kind')!r}")
        for field in ("title", "detail"):
            if not isinstance(blocker.get(field), str) or not blocker[field].strip():
                fail(f"blocker {key} has empty {field}")
    referenced = {key for item in items for key in item.get("blocked_by", [])}
    orphan = sorted(set(blockers) - referenced)
    if orphan:
        fail("blockers referenced by no item: " + ", ".join(orphan))


def check_private_source_not_tracked() -> None:
    tracked: list[str] = []
    if (ROOT / ".git").exists():
        result = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True)
        if result.returncode == 0:
            tracked = result.stdout.splitlines()
    if not tracked:
        tracked = [str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file()]
    for path in tracked:
        lower = path.lower()
        if any(name.lower() in lower for name in PRIVATE_SOURCE_NAMES):
            fail(f"private source appears tracked: {path}")


def report(items: list[dict]) -> None:
    """Report the mathematics, not the file's agreement with itself.

    This summary once read "CLEAN (48 items)", which is true of a self-consistent
    census in which nothing is proved: it counts rows, and every row is a row
    whether its theorem compiles or does not exist. Theorems 8.1 and 8.2 -- the
    paper's headline sin-Theta results -- were `not_compiling` under that line.
    """
    counts: dict[str, int] = {}
    for item in items:
        key = item.get("verification", "unknown")
        counts[key] = counts.get(key, 0) + 1
    order = ("proved_in_build", "proved_conditional", "partially_in_build",
             "proved_outside_build", "not_compiling", "absent", "not_applicable")
    detail = ", ".join(f"{counts[k]} {k}" for k in order if counts.get(k))
    for k in sorted(counts):
        if k not in order:
            detail += f", {counts[k]} {k}"
    print(f"Davis--Kahan full source census: {counts.get('proved_in_build', 0)}/{len(items)} "
          f"proved in the default build ({detail})")

    # Name the source results that are not proved, and separately those that are
    # proved but unguarded: one needs mathematics, the other needs a module moved
    # into a default target.
    at_risk = sorted(i["id"] for i in items
                     if i.get("verification") in {"proved_outside_build", "partially_in_build"})
    if at_risk:
        print("  proved but unguarded by `lake build`: " + ", ".join(at_risk))
    unproved = sorted(i["id"] for i in items
                      if i.get("verification") in {"not_compiling", "absent"})
    if unproved:
        print("  not proved: " + ", ".join(unproved))


def report_row_triage(items: list[dict]) -> None:
    """Row-level hostile certification is triage, not the 100% denominator.

    The denominator is the compact stated-result inventory; source-fidelity atoms
    are not proof obligations either.
    """
    statement_map = json.loads(MAP_PATH.read_text(encoding="utf-8"))
    obligations = {item["id"] for item in statement_map.get("items", [])
                   if item.get("completion_obligation") is True}
    by_id = {item["id"]: item for item in items}
    accepted = [
        i for i in (by_id[k] for k in obligations)
        if i.get("completion_certification") == "accepted"
        and i.get("status") in {"compiled_exact", "refuted_as_transcribed"}
        and i.get("verification") == "proved_in_build"
    ]
    print(f"  organizational-row semantic triage: {len(accepted)}/{len(obligations)} legacy row "
          "flags accepted (diagnostic only; not the formalization denominator)")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--no-probe", action="store_true",
                        help="skip the compiler probe (declaration resolution is then NOT verified)")
    args = parser.parse_args(argv)

    document = load_census(JSON_PATH, root=ROOT)
    findings = document.validate()
    errors = [f for f in findings if f.level == "error"]
    for finding in findings:
        print(f"{finding.level.upper():8s}{finding.location}: [{finding.code}] {finding.message}")
    if errors:
        return 1

    data = document.data
    check_davis_kahan_policy(data)

    # The static reference check the package performs matches short names, so a
    # reference in the wrong namespace passes it. The probe resolves every name
    # against the real build and is the authoritative check; run it here rather
    # than pointing at it, because for months nothing ran the separate script.
    if args.no_probe:
        print("NOTE: --no-probe given; declaration resolution was NOT verified")
    elif shutil.which("lake") is None:
        print("NOTE: lake unavailable; declaration resolution was NOT verified")
    else:
        probe = document.probe(imports=[PROBE_IMPORT])
        if probe.unresolved:
            print(f"Census declaration probe: {len(probe.unresolved)} unresolved reference(s) "
                  f"against {PROBE_IMPORT}")
            for name in probe.unresolved:
                print(f"  {name}")
            return 1
        changed = document.apply_probe(probe)
        if changed:
            print(f"Census declaration probe: {changed} row(s) record a `verification` the "
                  f"build disagrees with; run `aiq-lean census probe {JSON_PATH.relative_to(ROOT)} "
                  f"--import {PROBE_IMPORT} --write`")
            return 1
        print(f"Census declaration probe: {len(probe.resolved)}/{len(probe.results)} resolve "
              f"against {PROBE_IMPORT}, and every row's `verification` matches the build's view "
              "of the declarations it names")
        print("  NOT checked here: whether those statements match the paper's scope, whether "
              "`status` is accurate, or whether any row omits a declaration for a conclusion "
              "the paper asserts")

    check_private_source_not_tracked()

    if MD_PATH.read_text(encoding="utf-8") != document.render_markdown():
        print(f"ERROR: {MD_PATH.relative_to(ROOT)} is stale; regenerate it with "
              f"`aiq-lean census render {JSON_PATH.relative_to(ROOT)} -o {MD_PATH.relative_to(ROOT)}`")
        return 1

    result_checker = subprocess.run(
        [sys.executable, str(ROOT / "scripts/check_davis_kahan_1970_result_inventory.py")],
        cwd=ROOT,
    )
    if result_checker.returncode:
        return result_checker.returncode

    report(data["items"])
    report_row_triage(data["items"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
