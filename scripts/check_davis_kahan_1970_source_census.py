#!/usr/bin/env python3
"""Validate the Davis--Kahan 1970 full-paper source census."""
from __future__ import annotations

import json
import re
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

    lean_text = "\n".join(
        path.read_text(errors="ignore")
        for path in ROOT.rglob("*.lean")
        if ".lake" not in path.parts
    )
    declared = set(DECL_RE.findall(lean_text))
    for item in items:
        for ref in item.get("lean_declarations", []):
            short = ref.rsplit(".", 1)[-1]
            if short not in declared:
                fail(f"unresolved Lean declaration reference for {item['id']}: {ref}")

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

    print(f"Davis--Kahan full source census: CLEAN ({len(items)} items)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
