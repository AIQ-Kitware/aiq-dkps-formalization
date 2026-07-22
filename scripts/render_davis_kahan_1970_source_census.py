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
    "proved_outside_build", "not_compiling", "absent", "not_applicable",
]
NEEDS_WORK = ["absent", "not_compiling", "proved_conditional",
              "partially_in_build", "proved_outside_build"]


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
        "Every row that is not already `proved_in_build`, grouped by the",
        "obstruction standing in front of it. Work items marked `mechanical`",
        "are already proved and need only wiring; `hard_math` needs new",
        "mathematics.",
        "",
    ]
    by_blocker: dict[str, list] = {}
    unblocked: list = []
    for item in items:
        if item["verification"] not in NEEDS_WORK:
            continue
        keys = item.get("blocked_by") or []
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
        "full paper. The maintained modernized transcription is used only as a local",
        "comparison source and is intentionally not distributed. The JSON file is",
        "authoritative; this Markdown file is generated from it.",
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
            f"- **Mathematics:** {item['summary']}",
        ]
        blocked = item.get("blocked_by") or []
        if blocked:
            lines.append("- **Blocked by:** " + ", ".join(f"`{x}`" for x in blocked))
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
        "The completed Section 6 sine-theta surface is not the same as completion of",
        "the whole paper, but the remaining distance is smaller than a raw count of",
        "outstanding rows suggests, and it is not uniform.",
        "",
        "A zero `sorry` count is not evidence of completion here. Because the tree is",
        "both sorry-free and axiom-free, unfinished work cannot show up as a `sorry`;",
        "it shows up in exactly three places, which the `verification` axis separates:",
        "a package that does not compile (`not_compiling`), a conclusion stated",
        "relative to a hypothesis record nobody constructs (`proved_conditional`), and",
        "a statement nobody wrote (`absent`). Rows marked `proved_outside_build` and",
        "`partially_in_build` are a fourth, much cheaper case: the mathematics is",
        "already proved and merely sits outside the default build target.",
        "",
        "The genuinely hard remainder is Section 8, which is blocked on an",
        "operator-valued contour-integration API that exists nowhere, the Section 9",
        "analytic model, and the Section 3 classification results. The Section 10",
        "questions are part of the source record but are not proof obligations for a",
        "faithful formalization of what the paper proves.",
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
