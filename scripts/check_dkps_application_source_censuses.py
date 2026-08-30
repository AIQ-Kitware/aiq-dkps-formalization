#!/usr/bin/env python3
"""Validate, probe, and render the Acharyya/Helm/Quench source censuses.

The JSON files are authoritative; the Markdown files are generated views.

Schema, vocabularies, source-locator ranges, declaration references, and the
compiler probe are generic census machinery in `aiq_lean_tools`.  What stays here
is the DKPS application policy: which four censuses exist, the census kind they
must declare, the fields every row must fill in, and the Lean modules a probe has
to import to see all four papers at once.

    python3 scripts/check_dkps_application_source_censuses.py
    python3 scripts/check_dkps_application_source_censuses.py --render
    python3 scripts/check_dkps_application_source_censuses.py --probe
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
SLUGS = ("acharyya-2024", "acharyya-2025", "helm-2025", "quench-2026")
CENSUS_KIND = "dkps_application_source_semantic_alignment"
REQUIRED_TEXT_FIELDS = (
    "importance", "section", "source_anchor", "source_kind", "title",
    "source_claim", "status", "verification", "notes", "next_action",
)

#: The modules a probe must import to see all four application papers.  A census
#: declaration is evidence only if it is reachable from something that is built.
PROBE_IMPORTS = [
    "Acharyya2024",
    "Acharyya2025.Bridge", "Acharyya2025.ConfigPerturbation",
    "Acharyya2025.MathlibBridge", "Acharyya2025.SpectralPipeline",
    "Acharyya2025.AlignedPipeline", "Acharyya2025.GrowingResponse",
    "Acharyya2025.PaperRate", "Acharyya2025.RateChain", "Acharyya2025.Overlap",
    "Acharyya2025.ManifoldCondition", "Acharyya2025.Theorem1Scale",
    "Helm2025", "DkpsQuench2026",
    "ForTauCeti.Probability.AverageError",
    "ForTauCeti.Probability.VStatistic",
    "ForTauCeti.Probability.ProductConvergence",
]


def fail(message: str) -> None:
    raise SystemExit(f"ERROR: {message}")


def check_application_policy(path: Path, data: dict) -> list[dict]:
    if data.get("census_kind") != CENSUS_KIND:
        fail(f"{path}: wrong census_kind")
    if not data.get("semantic_alignment_definitions"):
        fail(f"{path}: missing semantic_alignment_definitions")
    gaps = data.get("gaps", {})
    referenced: set[str] = set()
    for row in data["items"]:
        rid = row["id"]
        for field in REQUIRED_TEXT_FIELDS:
            if not isinstance(row.get(field), str) or not row[field].strip():
                fail(f"{path}: {rid} has empty {field}")
        for field in ("lean_declarations", "planned_declarations", "gap_refs"):
            if not isinstance(row.get(field), list):
                fail(f"{path}: {rid} {field} must be a list")
        if not row.get("source_locator"):
            fail(f"{path}: {rid} missing source_locator")
        referenced.update(row["gap_refs"])
    orphan = sorted(set(gaps) - referenced)
    if orphan:
        fail(f"{path}: orphan gaps: {orphan}")
    return data["items"]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--render", action="store_true", help="rewrite the Markdown views")
    parser.add_argument("--probe", action="store_true",
                        help="resolve every cited declaration against the real build")
    args = parser.parse_args(argv)

    documents = [load_census(ROOT / "dev" / f"{slug}-full-source-census.json", root=ROOT)
                 for slug in SLUGS]
    rows: list[dict] = []
    refs: list[str] = []
    for document in documents:
        findings = document.validate()
        for finding in findings:
            print(f"{finding.level.upper():8s}{document.path.name} {finding.location}: "
                  f"[{finding.code}] {finding.message}")
        if any(f.level == "error" for f in findings):
            return 1
        rows.extend(check_application_policy(document.path, document.data))
        refs.extend(document.declaration_refs)
    refs = list(dict.fromkeys(refs))

    if args.probe:
        unresolved: list[str] = []
        for document in documents:
            probe = document.probe(imports=PROBE_IMPORTS)
            for name in probe.unresolved:
                module = probe.private_declarations.get(name)
                suffix = (f"  [declared PRIVATE in {module}: proved but not citable]"
                          if module else "  [no declaration of this name exists]")
                unresolved.append(f"{document.path.name}: {name}{suffix}")
        if unresolved:
            print("unresolved cited declarations:")
            for line in unresolved:
                print(f"  {line}")
            return 1

    for document in documents:
        target = document.path.with_suffix(".md")
        text = document.render_markdown()
        if args.render:
            target.write_text(text, encoding="utf-8")
        elif not target.exists() or target.read_text(encoding="utf-8") != text:
            fail(f"{target.relative_to(ROOT)} is stale; re-run with --render")

    print(f"OK: {len(documents)} censuses, {len(rows)} source rows, "
          f"{len(refs)} cited Lean declarations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
