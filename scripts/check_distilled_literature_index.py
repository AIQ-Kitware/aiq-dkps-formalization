#!/usr/bin/env python3
"""Validate the DKPS source-paper inventory and generated indexes."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from urllib.parse import urlparse

REQUIRED_TOP_LEVEL = {
    "version",
    "purpose",
    "scope_rule",
    "status_legend",
    "role_legend",
    "bibliographic_status_legend",
    "works",
}
REQUIRED_WORK_FIELDS = {
    "title",
    "authors",
    "year",
    "kind",
    "group",
    "tier",
    "priority",
    "role",
    "formalization_status",
    "distilled_status",
    "bibliographic_status",
    "primary_url",
    "target_note",
    "repo_evidence",
    "existing_assets",
    "scope",
    "missing_work",
}
KINDS = {"paper", "book", "monograph"}
PRIORITIES = {"P0", "P1", "P2", "P3"}
DISTILLED_STATUSES = {"missing", "transcription_only", "transcription_sufficient", "source_text_only", "core_note", "source_faithful_audit_specification", "complete"}
BIBLIOGRAPHIC_STATUSES = {"verified", "needs_verification"}
GROUPS = {
    "DKPS lineage and target papers",
    "MDS, Euclidean distance geometry, Gram rigidity, and alignment",
    "Spectral perturbation, principal angles, and matrix inequalities",
    "Reference works and modern syntheses",
}

COMPLETE_NOTE_REQUIRED_MARKERS = {
    "Davis1963": (
        "Davis 1.1", "Davis 1.2", "Davis 1.3",
        "Davis 2.1", "Davis 2.2", "Davis 2.3",
        "Davis 3.1", "Davis 3.2", "Davis 3.3",
        "Davis 4.1", "Davis 5.1",
        "\\tag{2.1}", "\\tag{2.2}", "\\tag{2.3}",
        "\\tag{2.4}", "\\tag{2.5}", "\\tag{3.1}",
        "\\tag{3.2}", "\\tag{3.3}", "\\tag{4.1}",
        "\\tag{4.2}", "\\tag{5.1}", "\\tag{5.2}",
    ),
    "YuWangSamworth2015": (
        "Statistical Davis--Kahan baseline",
        "Yu--Wang--Samworth population-gap theorem",
        "Rank-one form",
        "Yu--Wang--Samworth singular-subspace theorem",
        "Orthogonal compression",
        "\\tag{YWS-1}", "\\tag{YWS-2}", "\\tag{YWS-3}",
        "\\tag{YWS-4}", "\\tag{YWS-5}", "\\tag{YWS-6}",
        "\\tag{YWS-7}", "\\tag{YWS-8}", "\\tag{YWS-9}",
        "\\tag{YWS-10}", "\\tag{YWS-11}",
    ),
}


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    lit = repo / "prose" / "distilled_literature"
    manifest_path = lit / "source_manifest.json"
    errors: list[str] = []

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf8"))
    except Exception as ex:
        print(f"error: cannot read {manifest_path}: {ex}", file=sys.stderr)
        return 2

    missing_top = REQUIRED_TOP_LEVEL - set(manifest)
    if missing_top:
        errors.append(f"manifest missing top-level fields: {', '.join(sorted(missing_top))}")

    works = manifest.get("works")
    if not isinstance(works, dict) or not works:
        errors.append("manifest 'works' must be a nonempty object")
        works = {}

    role_values = set(manifest.get("role_legend", {}))
    target_notes: dict[str, str] = {}
    for key, work in works.items():
        if not isinstance(key, str) or not key:
            errors.append("work key must be a nonempty string")
            continue
        if not isinstance(work, dict):
            errors.append(f"{key}: work entry is not an object")
            continue
        missing = REQUIRED_WORK_FIELDS - set(work)
        if missing:
            errors.append(f"{key}: missing fields: {', '.join(sorted(missing))}")
            continue

        if not isinstance(work["title"], str) or not work["title"].strip():
            errors.append(f"{key}: title must be nonempty")
        if not isinstance(work["authors"], list) or not work["authors"] or not all(
            isinstance(author, str) and author.strip() for author in work["authors"]
        ):
            errors.append(f"{key}: authors must be a nonempty list of strings")
        if not isinstance(work["year"], int) or not (1800 <= work["year"] <= 2100):
            errors.append(f"{key}: invalid year {work['year']!r}")
        if work["kind"] not in KINDS:
            errors.append(f"{key}: invalid kind {work['kind']!r}")
        if work["group"] not in GROUPS:
            errors.append(f"{key}: invalid group {work['group']!r}")
        if work["priority"] not in PRIORITIES:
            errors.append(f"{key}: invalid priority {work['priority']!r}")
        if work["role"] not in role_values:
            errors.append(f"{key}: unknown role {work['role']!r}")
        if work["distilled_status"] not in DISTILLED_STATUSES:
            errors.append(f"{key}: invalid distilled_status {work['distilled_status']!r}")
        if work["bibliographic_status"] not in BIBLIOGRAPHIC_STATUSES:
            errors.append(f"{key}: invalid bibliographic_status {work['bibliographic_status']!r}")

        url = work["primary_url"]
        if url:
            parsed = urlparse(url)
            if parsed.scheme not in {"http", "https"} or not parsed.netloc:
                errors.append(f"{key}: invalid primary_url {url!r}")

        note = work["target_note"]
        if not isinstance(note, str) or not note.endswith(".tex"):
            errors.append(f"{key}: target_note must be a .tex filename")
        elif "/" in note or "\\" in note:
            errors.append(f"{key}: target_note must be a basename")
        elif note in target_notes:
            errors.append(f"{key}: target_note duplicates {target_notes[note]}: {note}")
        else:
            target_notes[note] = key

        for field in ("repo_evidence", "existing_assets"):
            paths = work[field]
            if not isinstance(paths, list) or not all(isinstance(item, str) for item in paths):
                errors.append(f"{key}: {field} must be a list of paths")
                continue
            for rel in paths:
                path = repo / rel
                if not path.exists():
                    errors.append(f"{key}: {field} path does not exist: {rel}")

        for field in ("formalization_status", "scope", "missing_work"):
            if not isinstance(work[field], str) or not work[field].strip():
                errors.append(f"{key}: {field} must be nonempty")

        if work["distilled_status"] == "complete":
            note_path = lit / work["target_note"]
            if not note_path.is_file():
                errors.append(f"{key}: complete distilled note is missing: {work['target_note']}")
            else:
                note_text = note_path.read_text(encoding="utf8")
                markers = (
                    "Source map and scope",
                    "Formalization map",
                    "Source-faithfulness",
                    "\\end{document}",
                ) + COMPLETE_NOTE_REQUIRED_MARKERS.get(key, ())
                for marker in markers:
                    if marker not in note_text:
                        errors.append(f"{key}: complete note missing marker {marker!r}")

    readme_path = lit / "README.md"
    if not readme_path.is_file():
        errors.append("README.md is missing")
    else:
        readme = readme_path.read_text(encoding="utf8")
        for heading in (
            "## Inclusion rule",
            "## Reconstruction standard",
            "## Citation discipline",
            "## Current starting point",
        ):
            if heading not in readme:
                errors.append(f"README.md missing heading {heading!r}")

    render = repo / "scripts" / "render_distilled_literature_index.py"
    if not render.is_file():
        errors.append("render_distilled_literature_index.py is missing")
    else:
        result = subprocess.run(
            [sys.executable, str(render), "--check"],
            cwd=repo,
            text=True,
            capture_output=True,
        )
        if result.returncode != 0:
            detail = (result.stdout + result.stderr).strip()
            errors.append(f"generated indexes are stale: {detail}")

    if errors:
        print("Distilled-literature index checks failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(f"Distilled-literature index checks passed for {len(works)} works.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
