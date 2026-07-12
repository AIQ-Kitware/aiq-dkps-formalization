#!/usr/bin/env python3
"""Render the DKPS source-paper inventory as Markdown and standalone LaTeX."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

GROUP_ORDER = [
    "DKPS lineage and target papers",
    "MDS, Euclidean distance geometry, Gram rigidity, and alignment",
    "Spectral perturbation, principal angles, and matrix inequalities",
    "Reference works and modern syntheses",
]

ROLE_LABELS = {
    "direct_target": "direct target",
    "inherited_foundation": "inherited foundation",
    "primary_method_source": "primary method source",
    "primary_theorem_source": "primary theorem source",
    "supporting_source": "supporting source",
    "modern_comparison": "modern comparison",
    "lineage_background": "lineage background",
    "future_extension": "future extension",
    "related_upstream": "related upstream",
    "reference_work": "reference work",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed renderings differ from the manifest",
    )
    return parser.parse_args()


def load_manifest(repo: Path) -> dict:
    path = repo / "prose" / "distilled_literature" / "source_manifest.json"
    return json.loads(path.read_text(encoding="utf8"))


def markdown_escape(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ")


def latex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def works_by_group(manifest: dict) -> dict[str, list[tuple[str, dict]]]:
    grouped = {group: [] for group in GROUP_ORDER}
    for key, work in manifest["works"].items():
        grouped.setdefault(work["group"], []).append((key, work))
    for items in grouped.values():
        items.sort(key=lambda item: (item[1]["year"], item[0]))
    return grouped


def render_markdown(manifest: dict) -> str:
    works = manifest["works"]
    values = list(works.values())
    kinds = Counter(work["kind"] for work in values)
    statuses = Counter(work["distilled_status"] for work in values)
    bib_statuses = Counter(work["bibliographic_status"] for work in values)
    priorities = Counter(work["priority"] for work in values)
    grouped = works_by_group(manifest)

    lines = [
        "# DKPS source-paper index",
        "",
        "Generated from `source_manifest.json`. This is the canonical inventory of works whose definitions, theorem families, or proof architecture are directly formalized, actively scaffolded, or inherited by the DKPS and Perfect Quench development.",
        "",
        "The index deliberately separates a paper's **formalization role** from the state of its local literature asset. A transcription is normally not a proof-level reconstruction; an exact short-paper transcription may be marked sufficient only when a maintained discrepancy ledger performs the modernization and theorem mapping. A modern textbook never silently replaces a primary source.",
        "",
        "## Inventory summary",
        "",
        f"- **{len(works)} works**: {kinds['paper']} papers, {kinds['book']} books, and {kinds['monograph']} monograph.",
        f"- **{statuses['complete']}** source-order distilled reconstructions are complete.",
        f"- **{statuses['core_note']}** broad core notes remain to be upgraded.",
        f"- **{statuses['transcription_sufficient']}** exact transcriptions are intentionally sufficient because a maintained discrepancy ledger supplies the theorem-level reconstruction.",
        f"- **{statuses['transcription_only'] + statuses['source_text_only']}** works have transcription or source text but no source-order proof reconstruction.",
        f"- **{statuses['missing']}** works have no local distilled note at all.",
        f"- **{bib_statuses['needs_verification']}** entries remain in the bibliographic verification queue.",
        f"- Priority split: P0={priorities['P0']}, P1={priorities['P1']}, P2={priorities['P2']}, P3={priorities['P3']}.",
        "",
        "## Interpretation",
        "",
        "- **P0**: direct DKPS/Quench theorem papers, inherited DKPS foundations, or the central Davis--Kahan sources.",
        "- **P1**: exact theorem sources needed to audit mathematical infrastructure already formalized or on the active proof path.",
        "- **P2**: supporting, newly discovered primary, or lineage sources that clarify provenance and constants.",
        "- **P3**: reference works and retained future arbitrary-dimensional extensions.",
        "",
    ]

    for group in GROUP_ORDER:
        lines.extend([
            f"## {group}",
            "",
            "| Key | Year | Work | Role | Formalization status | Literature asset | Priority |",
            "|---|---:|---|---|---|---|---|",
        ])
        for key, work in grouped.get(group, []):
            lines.append(
                "| `{}` | {} | {} | {} | {} | `{}` | {} |".format(
                    markdown_escape(key),
                    work["year"],
                    markdown_escape(work["title"]),
                    ROLE_LABELS[work["role"]],
                    markdown_escape(work["formalization_status"]),
                    work["distilled_status"],
                    work["priority"],
                )
            )
        lines.append("")

    direct_missing = [
        (key, work)
        for key, work in works.items()
        if work["priority"] in {"P0", "P1"}
        and work["distilled_status"] not in {"complete", "transcription_sufficient"}
    ]
    lines.extend([
        "## Highest-value missing reconstructions",
        "",
    ])
    for key, work in direct_missing:
        lines.append(
            f"- **`{key}` — {work['title']}**: {work['missing_work']}"
        )
    lines.append("")

    discovered = [
        (key, work)
        for key, work in works.items()
        if work["tier"] in {"discovered_primary", "lineage_background"}
    ]
    lines.extend([
        "## Sources missing from the repository's prior explicit source map",
        "",
        "These works were added by the audit rather than copied from an existing canonical DKPS source inventory:",
        "",
    ])
    for key, work in discovered:
        lines.append(
            f"- **`{key}` — {work['title']}** ({work['year']}): {work['scope']}"
        )
    lines.append("")

    verify = [
        (key, work)
        for key, work in works.items()
        if work["bibliographic_status"] == "needs_verification"
    ]
    lines.extend([
        "## Bibliographic verification queue",
        "",
        "No distilled note should be presented as source-faithful until the exact edition or article record is confirmed.",
        "",
    ])
    for key, work in verify:
        lines.append(f"- `{key}` — {work['title']}")
    lines.extend([
        "",
        "## Maintenance",
        "",
        "```bash",
        "python scripts/check_distilled_literature_index.py",
        "python scripts/render_distilled_literature_index.py",
        "```",
        "",
        "The checker validates schema, enums, repository evidence paths, local asset paths, unique target-note names, and exact agreement between the manifest and both generated indexes.",
        "",
    ])
    return "\n".join(lines)


def render_tex(manifest: dict) -> str:
    works = manifest["works"]
    values = list(works.values())
    kinds = Counter(work["kind"] for work in values)
    statuses = Counter(work["distilled_status"] for work in values)
    grouped = works_by_group(manifest)

    lines = [
        r"\documentclass[10pt]{article}",
        r"\usepackage[margin=0.7in]{geometry}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage{lmodern}",
        r"\usepackage{longtable}",
        r"\usepackage{booktabs}",
        r"\usepackage{array}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{5pt}",
        r"\newcommand{\code}[1]{\texttt{#1}}",
        r"\title{DKPS Source-Paper and Distilled-Literature Index}",
        r"\author{}",
        r"\date{Generated from \code{source\_manifest.json}}",
        r"\begin{document}",
        r"\maketitle",
        r"\section*{Purpose}",
        "This document inventories the works whose definitions, theorem families, or proof architecture are directly formalized, actively scaffolded, or inherited by the DKPS and Perfect Quench development. It is an index, not yet a corpus of completed proof reconstructions.",
        r"\section*{Current state}",
        f"The inventory contains {len(works)} works: {kinds['paper']} papers, {kinds['book']} books, and {kinds['monograph']} monograph. "
        f"There are {statuses['complete']} completed source-order reconstructions, {statuses['transcription_sufficient']} intentionally sufficient exact transcription(s), {statuses['core_note']} broad core notes, {statuses['transcription_only'] + statuses['source_text_only']} transcription/source-text assets awaiting reconstruction, and {statuses['missing']} works with no local distilled note.",
    ]

    for group in GROUP_ORDER:
        lines.extend([
            r"\section*{" + latex_escape(group) + "}",
            r"\begin{longtable}{@{}p{0.17\textwidth}p{0.05\textwidth}p{0.35\textwidth}p{0.16\textwidth}p{0.12\textwidth}p{0.06\textwidth}@{}}",
            r"\toprule",
            r"Key & Year & Work & Role & Asset & Priority \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Key & Year & Work & Role & Asset & Priority \\",
            r"\midrule",
            r"\endhead",
        ])
        for key, work in grouped.get(group, []):
            lines.append(
                r"\code{" + latex_escape(key) + "} & "
                + str(work["year"]) + " & "
                + latex_escape(work["title"]) + " & "
                + latex_escape(ROLE_LABELS[work["role"]]) + " & "
                + latex_escape(work["distilled_status"].replace("_", " ")) + " & "
                + latex_escape(work["priority"]) + r" \\"
            )
        lines.extend([r"\bottomrule", r"\end{longtable}"])

    lines.extend([
        r"\section*{Source-faithful reconstruction standard}",
        "Each future note should state its exact source files and edition, scope, theorem/equation anchors, preserved proof route, supplemental arguments, source issues, and the corresponding Lean declarations. A transcription or a modern substitute proof must not be presented as the paper's own proof.",
        r"\end{document}",
        "",
    ])
    return "\n".join(lines)


def update_or_check(path: Path, content: str, check: bool) -> bool:
    if check:
        return path.is_file() and path.read_text(encoding="utf8") == content
    path.write_text(content, encoding="utf8")
    return True


def main() -> int:
    args = parse_args()
    repo = Path(__file__).resolve().parents[1]
    lit = repo / "prose" / "distilled_literature"
    manifest = load_manifest(repo)
    outputs = {
        lit / "source_index.md": render_markdown(manifest),
        lit / "distilled_papers_index.tex": render_tex(manifest),
    }
    failures = []
    for path, content in outputs.items():
        if not update_or_check(path, content, args.check):
            failures.append(path.relative_to(repo))
    if failures:
        for path in failures:
            print(f"out of date: {path}")
        return 1
    if args.check:
        print(f"Rendered indexes are current ({len(manifest['works'])} works).")
    else:
        for path in outputs:
            print(f"wrote {path.relative_to(repo)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
