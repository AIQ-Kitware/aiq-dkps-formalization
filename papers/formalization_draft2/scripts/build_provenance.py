#!/usr/bin/env python3
"""Build a paper-local proof-provenance audit inventory.

This does not attempt to infer intellectual provenance from code similarity.
It inventories contemporaneous provenance statements already maintained in the
repository and makes gaps visible for a declaration-level citation audit.
"""

from __future__ import annotations

import csv
import pathlib
import re
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
PAPER = HERE.parent
GENERATED = PAPER / "generated"
SNAPSHOTS = PAPER / "snapshots"
ROOT = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=PAPER, text=True).strip())

SCAN_ROOTS = ["ForTauCeti", "DavisKahan", "YuWangSamworth2015", "DkpsQuench2026"]
SOURCE_REGISTRIES = [
    ("spectra_map", "dev/tauceti/spectra-provenance-map.md"),
    ("external_lean", "dev/external-lean-references.md"),
    ("external_literature", "dev/external-literature-references.md"),
    ("prior_paper_inventory", "papers/formalization_draft1/model_provenance.md"),
]


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def provenance_blocks(path: pathlib.Path) -> list[tuple[int, str]]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    out: list[tuple[int, str]] = []
    for i, line in enumerate(lines):
        if "## Provenance" not in line:
            continue
        captured: list[str] = []
        for j in range(i + 1, min(len(lines), i + 80)):
            cur = lines[j]
            if j > i + 1 and (cur.lstrip().startswith("## ") or "-/" in cur):
                before = cur.split("-/", 1)[0]
                if before.strip():
                    captured.append(before)
                break
            captured.append(cur)
        out.append((i + 1, normalize(" ".join(captured))))
    return out


def spectra_class(block: str) -> str:
    low = block.lower()
    if "spectra influence" in low:
        m = re.search(r"spectra influence:\s*(?:\*\*)?([^.;*]+)", block, re.I)
        if m and m.group(1).strip().lower().startswith("none"):
            return "explicit_none"
        return "declared_influence"
    if "spectra" in low:
        return "mentioned_unspecified"
    return "not_mentioned"


def relationship_flags(block: str) -> dict[str, int]:
    low = block.lower()
    return {
        "mentions_spectra": int("spectra" in low),
        "mentions_mathlib": int("mathlib" in low),
        "mentions_external_repo_or_vendor": int(any(x in low for x in ("vendor", "upstream", "external", "github.com"))),
        "mentions_copy_or_adaptation": int(any(x in low for x in ("copied", "adapted", "port", "ported", "extraction class", "donor"))),
        "mentions_ai_authorship": int(any(x in low for x in ("claude", "gpt", "codex", "ai-contribution", "ai contribution"))),
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    for root_name in SCAN_ROOTS:
        base = ROOT / root_name
        if not base.exists():
            continue
        for path in sorted(base.rglob("*.lean")):
            for line_no, block in provenance_blocks(path):
                flags = relationship_flags(block)
                rows.append(
                    {
                        "file": path.relative_to(ROOT).as_posix(),
                        "line": line_no,
                        "spectra_relation": spectra_class(block),
                        **flags,
                        "provenance_text": block,
                    }
                )
    fields = list(rows[0]) if rows else ["file", "line", "provenance_text"]
    with (GENERATED / "proof_provenance_inventory.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    registry_rows = []
    for kind, rel in SOURCE_REGISTRIES:
        p = ROOT / rel
        registry_rows.append(
            {
                "kind": kind,
                "path": rel,
                "exists": int(p.exists()),
                "line_count": len(p.read_text(encoding="utf-8", errors="replace").splitlines()) if p.exists() else 0,
            }
        )
    with (GENERATED / "proof_provenance_sources.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(registry_rows[0]))
        w.writeheader()
        w.writerows(registry_rows)

    spectra_declared = sum(r["spectra_relation"] == "declared_influence" for r in rows)
    spectra_unspecified = sum(r["spectra_relation"] == "mentioned_unspecified" for r in rows)
    adaptation = sum(r["mentions_copy_or_adaptation"] for r in rows)
    ai_authorship = sum(r["mentions_ai_authorship"] for r in rows)
    report = [
        "# Proof-provenance inventory",
        "",
        f"Scanned **{len(rows)}** module-level `## Provenance` blocks under {', '.join('`'+x+'`' for x in SCAN_ROOTS)}.",
        f"- blocks declaring Spectra influence: **{spectra_declared}**",
        f"- blocks mentioning Spectra without the standard influence field: **{spectra_unspecified}**",
        f"- blocks mentioning copying/adaptation/porting/donor/extraction relationships: **{adaptation}**",
        f"- blocks mentioning LLM authorship or AI-contribution policy: **{ai_authorship}**",
        "",
        "This is an inventory of recorded provenance, not a substitute for scholarly citation review. Before submission, every proof or construction discussed in the manuscript should be traced to the relevant mathematical source and any Lean donor separately.",
        "",
        "## Maintained source registries",
        "",
    ]
    for r in registry_rows:
        report.append(f"- `{r['path']}` ({r['kind']}): {'present' if r['exists'] else 'MISSING'}, {r['line_count']} lines")
    report += [
        "",
        "## Required paper-level distinctions",
        "",
        "1. copied or closely adapted code;",
        "2. mathematics ported with substantial API rewriting;",
        "3. a donor proof strategy followed by an independent re-derivation; and",
        "4. an ordinary upstream Mathlib dependency.",
        "",
        "The generated CSV is designed to seed, not replace, a declaration-level citation audit.",
    ]
    (GENERATED / "PROVENANCE_REPORT.md").write_text("\n".join(report) + "\n", encoding="utf-8")

    macros = [
        "% Generated by scripts/build_provenance.py; do not edit by hand.",
        f"\\newcommand{{\\ProvenanceBlockCount}}{{{len(rows)}}}",
        f"\\newcommand{{\\SpectraInfluenceBlockCount}}{{{spectra_declared}}}",
    ]
    (SNAPSHOTS / "provenance_macros.tex").write_text("\n".join(macros) + "\n", encoding="utf-8")
    print(f"provenance: {len(rows)} blocks, {spectra_declared} declaring Spectra influence")


if __name__ == "__main__":
    main()
