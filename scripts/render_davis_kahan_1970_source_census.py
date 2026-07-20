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
            f"- **Mathematics:** {item['summary']}",
        ]
        refs = item.get("lean_declarations", [])
        if refs:
            lines.append("- **Current Lean references:** " + ", ".join(f"`{x}`" for x in refs))
        else:
            lines.append("- **Current Lean references:** none identified")
        lines += [
            f"- **Assessment:** {item['notes']}",
            f"- **Next action:** {item['next_action']}",
            "",
        ]

    lines += [
        "## Completion interpretation",
        "",
        "The completed Section 6 sine-theta surface is not the same as completion of",
        "the whole paper. The largest definite source gaps are the Section 3",
        "classification and nonacute direct-rotation results, exact source wrappers",
        "for Sections 4--5 and 7--8, and the complete Section 9 numerical example.",
        "The Section 10 questions are part of the source record but are not proof",
        "obligations for a faithful formalization of what the paper proves.",
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
