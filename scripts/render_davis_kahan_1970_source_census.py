#!/usr/bin/env python3
"""Render the committed Davis--Kahan 1970 source census as Markdown."""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
MD_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.md"


# Ordered so the ledger reads from "done" to "needs work"; a fresh reader
# should be able to find the frontier by scanning downward.
VERIFICATION_ORDER = [
    "proved_in_build", "proved_conditional", "partially_in_build",
    "proved_outside_build", "compiler_pending", "not_compiling", "absent",
    "not_applicable",
]
NEEDS_WORK = ["absent", "not_compiling", "compiler_pending", "proved_conditional",
              "partially_in_build", "proved_outside_build"]
CERTIFICATION_ORDER = [
    "accepted", "reopened_source_spec", "reopened_math", "reopened_mapping",
    "mixed_disposition", "not_applicable",
]



def _render_completion_certification(data: dict, items: list) -> list[str]:
    """The hostile semantic axis: whether a row may count toward 100%."""
    counts = Counter(item.get("completion_certification", "missing") for item in items)
    lines = [
        "",
        "## Hostile completion-certification summary",
        "",
        "A terminal `status` and a green Lean declaration probe are necessary but no longer",
        "sufficient for the 100% claim. `completion_certification` records whether the entire",
        "hashed source passage survived an adversarial source-to-Lean review. Only `accepted`",
        "completion obligations count toward hostile-certified 100% coverage.",
        "",
        "| Completion certification | Count |",
        "| --- | ---: |",
    ]
    for key in CERTIFICATION_ORDER:
        lines.append(f"| `{key}` | {counts.get(key, 0)} |")
    lines += ["", "## Completion-certification meanings", ""]
    for key in CERTIFICATION_ORDER:
        meaning = data.get("completion_certification_definitions", {}).get(key)
        if meaning:
            lines.append(f"- **`{key}`** -- {meaning}")
    return lines

def _render_verification(data: dict, items: list) -> list[str]:
    """The compile-backed axis: what the Lean build actually certifies."""
    counts = Counter(item["verification"] for item in items)
    lines = [
        "",
        "## Verification summary",
        "",
        "`status` above is the mathematical judgement against the printed",
        "source. `verification` below is what the Lean build certifies, and is",
        "checkable: run `python3 scripts/probe_census_declarations.py --verify`",
        "to confirm every row still matches the build. The default build carries",
        "no `sorry` and no `axiom`, so a declaration reachable from",
        "`DavisKahan.All` is genuinely proved.",
        "",
        "| Verification | Count |",
        "| --- | ---: |",
    ]
    for key in VERIFICATION_ORDER:
        if key in data.get("verification_definitions", {}):
            lines.append(f"| `{key}` | {counts.get(key, 0)} |")
    lines += ["", "## Verification meanings", ""]
    for key in VERIFICATION_ORDER:
        meaning = data.get("verification_definitions", {}).get(key)
        if meaning:
            lines.append(f"- **`{key}`** -- {meaning}")
    return lines


def _render_frontier(data: dict, items: list) -> list[str]:
    """Group everything still outstanding under the obstruction that gates it."""
    blockers = data.get("blockers", {})
    lines = [
        "",
        "## Frontier",
        "",
        "Every row that still owes work, grouped by the obstruction standing",
        "in front of it. This includes rows that are already",
        "`proved_in_build`: the mathematics can be proved and CI-guarded while",
        "the source-numbered wrapper is still missing. Obstructions marked",
        "`mechanical` need only wiring or a restatement; `hard_math` needs new",
        "mathematics.",
        "",
    ]
    by_blocker: dict[str, list] = {}
    unblocked: list = []
    for item in items:
        keys = item.get("blocked_by") or []
        # A row can be `proved_in_build` and still owe work -- the mathematics
        # is proved and guarded, but the source-numbered wrapper is missing.
        # Filtering on verification alone would hide exactly those.
        if item["verification"] not in NEEDS_WORK and not keys:
            continue
        if not keys:
            unblocked.append(item)
        for key in keys:
            by_blocker.setdefault(key, []).append(item)

    for key in sorted(by_blocker, key=lambda k: (
            {"hard_math": 0, "mixed": 1, "mechanical": 2}.get(
                blockers.get(k, {}).get("kind"), 3), k)):
        blocker = blockers.get(key, {})
        lines += [
            f"### `{key}` -- {blocker.get('kind', '?')}",
            "",
            f"**{blocker.get('title', key)}**",
            "",
            blocker.get("detail", ""),
            "",
            "Gates: " + ", ".join(
                f"{i['id']} ({i['verification']})" for i in by_blocker[key]),
            "",
        ]
    if unblocked:
        lines += [
            "### Not attributed to a blocker",
            "",
            ", ".join(f"{i['id']} ({i['verification']})" for i in unblocked),
            "",
        ]
    return lines


def render(data: dict) -> str:
    items = data["items"]
    counts = Counter(item["status"] for item in items)
    lines = [
        "# Davis--Kahan 1970 full source census",
        "",
        f"Base commit: `{data['base_commit']}`.",
        "",
        "This is the public, independently worded theorem-by-theorem ledger for the",
        "full paper. The checked-in `DavisKahan1970_part_III.tex` is the distributable",
        "source-order semantic specification used by the static statement audit. Private",
        "source material is optional provenance for re-auditing that reconstruction. The",
        "JSON file is authoritative for census status; this Markdown file is generated",
        "from it.",
        "",
        "## Status summary",
        "",
        "| Status | Count |",
        "| --- | ---: |",
    ]
    for status in data["status_definitions"]:
        lines.append(f"| `{status}` | {counts.get(status, 0)} |")
    lines += ["", "## Status meanings", ""]
    for status, meaning in data["status_definitions"].items():
        lines.append(f"- **`{status}`** -- {meaning}")

    lines += _render_completion_certification(data, items)
    lines += _render_verification(data, items)
    lines += _render_frontier(data, items)
    lines += ["", "## Source ledger", ""]

    current_section = None
    for item in items:
        if item["section"] != current_section:
            current_section = item["section"]
            lines += [f"### Section {current_section}", ""]
        lines += [
            f"#### {item['source_anchor']}: {item['title']}",
            "",
            f"- **Kind:** `{item['source_kind']}`",
            f"- **Status:** `{item['status']}`",
            f"- **Verification:** `{item['verification']}`",
            f"- **Hostile completion certification:** `{item.get('completion_certification', 'missing')}`",
            f"- **Mathematics:** {item['summary']}",
        ]
        blocked = item.get("blocked_by") or []
        if blocked:
            lines.append("- **Blocked by:** " + ", ".join(f"`{x}`" for x in blocked))
        holes = item.get("completion_holes") or []
        if holes:
            lines.append("- **Known hostile-review holes:**")
            for hole in holes:
                lines.append(f"  - `{hole.get('kind', 'unspecified')}`: {hole.get('detail', '')}")
        refs = item.get("lean_declarations", [])
        if refs:
            lines.append("- **Current Lean references:** " + ", ".join(f"`{x}`" for x in refs))
        else:
            lines.append("- **Current Lean references:** none identified")
        outside = item.get("declarations_outside_build") or []
        if outside:
            lines.append(
                "- **Not reachable from `DavisKahan.All`:** "
                + ", ".join(f"`{x}`" for x in outside))
        lines += [
            f"- **Assessment:** {item['notes']}",
            f"- **Next action:** {item['next_action']}",
            "",
        ]

    lines += [
        "## Completion interpretation",
        "",
        "The compiler and declaration census are healthy evidence layers, but they are not a",
        "semantic completeness certificate. The 2026-08-12 hostile review deliberately reopened",
        "rows whose public source specification is incomplete, whose source-facing statement is",
        "missing/narrower than the paper, or whose current `.whole` audit clause cannot demonstrate",
        "that every separable assertion in the hashed passage is covered.",
        "",
        "The hard 100% gate is now: explicit statement-map completion obligation + terminal source",
        "status + `proved_in_build` + `completion_certification = accepted`. Pure source open questions",
        "remain non-obligations. Question 10.4 is intentionally different: its final general-f question",
        "is open, but the same source block contains established functional-calculus/projection identities",
        "and tan(2 Theta) specializations, so that mixed block remains a completion obligation until its",
        "established clauses are atomically certified.",
        "",
        "Do not report 100% from the raw `compiled_exact` count, from a green `lake build`, or from a",
        "recursively grounded legacy frontier graph. Those answer different questions. Repair the known",
        "holes listed above, re-run the hostile audit, and only then promote `completion_certification` to",
        "`accepted`.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.loads(JSON_PATH.read_text())
    text = render(data)
    if args.check:
        if not MD_PATH.exists() or MD_PATH.read_text() != text:
            print(f"stale generated file: {MD_PATH.relative_to(ROOT)}")
            return 1
        return 0
    MD_PATH.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
