#!/usr/bin/env python3
"""Validate the Davis--Kahan 1970 full-paper source census."""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"

REQUIRED_ANCHORS = {
    "Definition 3.1", "Definition 3.2",
    "Proposition 3.1", "Proposition 3.2", "Proposition 3.3", "Proposition 3.4",
    "Theorem 3.1", "Corollary 3.1", "Proposition 3.5", "Corollary 3.2",
    "Proposition 4.1", "Corollary 4.1", "Proposition 4.2", "Proposition 4.3", "Proposition 4.4",
    "Theorem 5.1", "Theorem 5.2", "Lemma 5.1",
    "Lemma 6.1", "Lemma 6.2", "Proposition 6.1", "Theorem 6.1", "Theorem 6.2", "Theorem 6.3", "Lemma 6.3",
    "Theorem 8.1", "Theorem 8.2",
    "Question 10.1", "Question 10.2", "Question 10.3", "Question 10.4",
}
ALLOWED_SECTIONS = {"1", "2", "3", "4", "5", "6", "6 appendix", "7", "8", "9", "10"}
DECL_RE = re.compile(r"\b(?:alias|theorem|lemma|def|structure|abbrev|noncomputable def)\s+([A-Za-z0-9_']+)")


def fail(message: str) -> None:
    print(f"ERROR: {message}")
    raise SystemExit(1)


def main() -> int:
    data = json.loads(JSON_PATH.read_text())
    items = data.get("items")
    if not isinstance(items, list) or not items:
        fail("items must be a nonempty list")
    statuses = set(data.get("status_definitions", {}))
    ids: set[str] = set()
    anchors: set[str] = set()
    for item in items:
        item_id = item.get("id")
        if not item_id or item_id in ids:
            fail(f"missing or duplicate item id: {item_id!r}")
        ids.add(item_id)
        if item.get("section") not in ALLOWED_SECTIONS:
            fail(f"invalid section for {item_id}: {item.get('section')!r}")
        if item.get("status") not in statuses:
            fail(f"invalid status for {item_id}: {item.get('status')!r}")
        for key in ("source_kind", "source_anchor", "title", "summary", "notes", "next_action"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                fail(f"{item_id} has empty {key}")
        anchors.add(item["source_anchor"])

    missing_anchors = sorted(REQUIRED_ANCHORS - anchors)
    if missing_anchors:
        fail("missing numbered source anchors: " + ", ".join(missing_anchors))

    # Skip every dot-directory, not just `.lake`.  This census only *adds* to
    # `declared`, so a stray checkout inside the repo cannot make it fail -- it
    # can only satisfy a pin that the real tree no longer satisfies, turning a
    # missing declaration into a silent pass.  A subagent worktree at
    # `.claude/worktrees/` put ~1259 extra `.lean` files in range, which is
    # exactly enough to hide a rename from this check.
    lean_text = "\n".join(
        path.read_text(errors="ignore")
        for path in ROOT.rglob("*.lean")
        if not any(part.startswith(".") for part in path.relative_to(ROOT).parts)
    )
    declared = set(DECL_RE.findall(lean_text))
    for item in items:
        for ref in item.get("lean_declarations", []):
            short = ref.rsplit(".", 1)[-1]
            if short not in declared:
                fail(f"unresolved Lean declaration reference for {item['id']}: {ref}")
        # `planned_declarations` records names the census wants but nobody has
        # written.  If one starts existing it must be promoted, or the census
        # keeps under-reporting progress.
        for ref in item.get("planned_declarations", []):
            short = ref.rsplit(".", 1)[-1]
            if short in declared:
                fail(f"{item['id']} lists {ref} as planned, but it now exists; "
                     f"move it into lean_declarations")

    # --- schema 4: the compile-backed verification axis --------------------
    # The textual check above is deliberately weak: it matches only the short
    # name after the last dot, so a reference in the wrong namespace passes.
    # `probe_census_declarations.py --verify` is the authoritative check -- it
    # resolves every name against the real build -- and for months nothing ran
    # it, because `run_gates.py` discovers `scripts/check_*.py` and the probe is
    # not named that.  So the weak check was the only one anyone saw, and it
    # reported CLEAN.  Run the real one here rather than pointing at it.
    if shutil.which("lake") is not None:
        probe = subprocess.run(
            [sys.executable, str(ROOT / "scripts/probe_census_declarations.py"), "--verify"],
            cwd=ROOT,
        )
        if probe.returncode:
            return probe.returncode
    else:
        print("NOTE: lake unavailable; declaration resolution was NOT verified")

    verifications = set(data.get("verification_definitions", {}))
    if not verifications:
        fail("schema 4 requires verification_definitions")
    blockers = data.get("blockers", {})
    # An EMPTY blockers table is legal, and is the goal state of the campaign.
    # This check used to require a nonempty table, which combined with the
    # orphan check below made "no blockers remain" unrepresentable: retiring the
    # last blocker forced a choice between an orphan failure and keeping a
    # fictional entry.  Retired blockers keep their accumulated route notes under
    # the separate `retired_blockers` key, which nothing is required to reference.
    if not isinstance(blockers, dict):
        fail("schema 4 requires a blockers table")
    for key, blocker in blockers.items():
        if blocker.get("kind") not in {"hard_math", "mechanical", "mixed"}:
            fail(f"blocker {key} has invalid kind: {blocker.get('kind')!r}")
        for field in ("title", "detail"):
            if not isinstance(blocker.get(field), str) or not blocker[field].strip():
                fail(f"blocker {key} has empty {field}")
    referenced: set[str] = set()
    for item in items:
        if item.get("verification") not in verifications:
            fail(f"invalid verification for {item['id']}: "
                 f"{item.get('verification')!r}")
        blocked = item.get("blocked_by")
        if not isinstance(blocked, list):
            fail(f"{item['id']} must carry a blocked_by list")
        for key in blocked:
            if key not in blockers:
                fail(f"{item['id']} is blocked_by {key!r}, absent from blockers")
            referenced.add(key)
    orphan = sorted(set(blockers) - referenced)
    if orphan:
        fail("blockers referenced by no item: " + ", ".join(orphan))

    private_names = ("modernized-transcription", "DavisKahan1970.pdf", "davis-kahan-1970-modernized")
    git_dir = ROOT / ".git"
    tracked = []
    if git_dir.exists():
        result = subprocess.run(
            ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True
        )
        if result.returncode == 0:
            tracked = result.stdout.splitlines()
    if not tracked:
        tracked = [str(path.relative_to(ROOT)) for path in ROOT.rglob("*") if path.is_file()]
    for path in tracked:
        lower = path.lower()
        if any(name.lower() in lower for name in private_names):
            fail(f"private source appears tracked: {path}")

    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts/render_davis_kahan_1970_source_census.py"), "--check"],
        cwd=ROOT,
    )
    if result.returncode:
        return result.returncode

    # Report the mathematics, not the file's agreement with itself.  This line
    # used to read "CLEAN (48 items)", which is true of a self-consistent census
    # in which nothing is proved: it counts rows, and every row is a row whether
    # its theorem compiles or does not exist.  Theorems 8.1 and 8.2 -- the paper's
    # headline sin-Theta results -- are `not_compiling`, and the old summary said
    # CLEAN above them.
    counts: dict[str, int] = {}
    for item in items:
        counts[item.get("verification", "unknown")] = (
            counts.get(item.get("verification", "unknown"), 0) + 1
        )
    proved = counts.get("proved_in_build", 0)
    order = ("proved_in_build", "proved_conditional", "partially_in_build",
             "proved_outside_build", "not_compiling", "absent", "not_applicable")
    detail = ", ".join(f"{counts[k]} {k}" for k in order if counts.get(k))
    for k in sorted(counts):
        if k not in order:
            detail += f", {counts[k]} {k}"
    print(f"Davis--Kahan full source census: {proved}/{len(items)} proved in the "
          f"default build ({detail})")

    # Name the source results that are not proved, and separately those that are
    # proved but unguarded.  A reader must not have to cross-reference the JSON,
    # and the two are different obligations: one needs mathematics, the other
    # needs a module moved into a default target.
    at_risk = sorted(
        item["id"] for item in items
        if item.get("verification") in {"proved_outside_build", "partially_in_build"}
    )
    if at_risk:
        print("  proved but unguarded by `lake build`: " + ", ".join(at_risk))
    unproved = sorted(
        item["id"] for item in items
        if item.get("verification") in {"not_compiling", "absent"}
    )
    if unproved:
        print("  not proved: " + ", ".join(unproved))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
