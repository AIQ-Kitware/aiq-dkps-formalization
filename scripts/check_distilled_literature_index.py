#!/usr/bin/env python3
"""Validate the DKPS source-paper inventory and its generated indexes.

The manifest schema, vocabularies, required fields, URL and note-basename rules,
evidence-path existence, and the `complete`-reconstruction marker contract are
all validated by `aiq-lean literature validate`, driven by the `policy` and
`reconstruction` blocks *inside* `source_manifest.json`.  Moving that policy into
the manifest is the point: the vocabulary and the works it governs are now one
file, and adding a group or a required marker is a data edit.

What stays here is the DKPS-specific composition: the prose README contract, and
the two generated indexes whose presentation is this project's rather than the
tool's.

    python3 scripts/check_distilled_literature_index.py
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

try:
    from aiq_lean_tools.literature import load_literature
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

REPO = Path(__file__).resolve().parents[1]
LITERATURE = REPO / "prose" / "distilled_literature"
MANIFEST = LITERATURE / "source_manifest.json"

#: The README states the rules a reader needs before trusting any entry: what is
#: in scope, what a reconstruction has to be, how to cite, and where to start.
#: A missing heading means one of those rules has quietly gone away.
REQUIRED_README_HEADINGS = (
    "## Inclusion rule",
    "## Reconstruction standard",
    "## Citation discipline",
    "## Current starting point",
)


def main() -> int:
    errors: list[str] = []

    document = load_literature(MANIFEST, root=REPO)
    for finding in document.validate():
        if finding.level == "error":
            errors.append(f"{finding.location}: {finding.message}")
        else:
            print(f"WARNING {finding.location}: {finding.message}", file=sys.stderr)

    readme = LITERATURE / "README.md"
    if not readme.is_file():
        errors.append("README.md is missing")
    else:
        text = readme.read_text(encoding="utf-8")
        for heading in REQUIRED_README_HEADINGS:
            if heading not in text:
                errors.append(f"README.md missing heading {heading!r}")

    renderer = REPO / "scripts" / "render_distilled_literature_index.py"
    if not renderer.is_file():
        errors.append("render_distilled_literature_index.py is missing")
    else:
        result = subprocess.run(
            [sys.executable, str(renderer), "--check"], cwd=REPO, text=True, capture_output=True
        )
        if result.returncode != 0:
            errors.append(f"generated indexes are stale: {(result.stdout + result.stderr).strip()}")

    if errors:
        print("Distilled-literature index checks failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(f"Distilled-literature index checks passed for {len(document.works)} works.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
