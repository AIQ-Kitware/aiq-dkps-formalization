#!/usr/bin/env python3
"""Remove redundant snapshots copied from the project's existing Mathlib dependency.

A previous vendor survey may have copied selected Mathlib declarations under
``vendor/lean/mathlib4``.  Those copies are not third-party vendors: production
code can and should import the pinned Mathlib modules directly.

This cleanup is intentionally narrow and idempotent.  It removes only the known
Mathlib snapshot directory and provenance records whose ``local_path`` points
inside that directory.
"""

from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path

PREFIX = "vendor/lean/mathlib4/"
KNOWN_NAMES = {
    "LinearPMapClosedGraph.excerpt.lean",
    "AntilipschitzClosedRange.excerpt.lean",
    "BanachClosedRangeInverse.excerpt.lean",
    "NearIdentityInverse.excerpt.lean",
}


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / ".git").exists() or (candidate / "lakefile.toml").exists():
            return candidate
    raise SystemExit("could not locate repository root")


def clean_manifest(path: Path) -> bool:
    if not path.exists():
        return False
    text = path.read_text()
    parts = re.split(r"(?=^\[\[source\]\]\s*$)", text, flags=re.MULTILINE)
    kept: list[str] = []
    changed = False
    for part in parts:
        if part.startswith("[[source]]") and re.search(
            rf'^local_path\s*=\s*"{re.escape(PREFIX)}', part, flags=re.MULTILINE
        ):
            changed = True
            continue
        kept.append(part)
    if changed:
        path.write_text("".join(kept).rstrip() + "\n")
    return changed


def clean_line_registry(path: Path) -> bool:
    if not path.exists() or not path.is_file():
        return False
    try:
        text = path.read_text()
    except UnicodeDecodeError:
        return False
    lines = text.splitlines()
    kept = [
        line
        for line in lines
        if PREFIX not in line and not any(name in line for name in KNOWN_NAMES)
    ]
    if kept == lines:
        return False
    path.write_text("\n".join(kept).rstrip() + "\n")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = find_repo_root(args.repo.resolve())

    target = root / "vendor/lean/mathlib4"
    if target.exists():
        shutil.rmtree(target)
        print(f"removed {target.relative_to(root)}")

    changed = clean_manifest(root / "vendor/lean/manifest.toml")
    if changed:
        print("removed Mathlib snapshot records from vendor/lean/manifest.toml")

    candidates = [
        root / "vendor/lean/README.md",
        root / "vendor/lean/SHA256SUMS",
        root / "vendor/lean/NOTICE",
        root / "vendor/lean/NOTICE.md",
        root / "vendor/lean/NOTICES",
        root / "vendor/lean/NOTICES.md",
        root / "dev/graph-subspace-vendor-survey-2026-07-14.md",
    ]
    for path in candidates:
        if clean_line_registry(path):
            print(f"removed redundant Mathlib snapshot references from {path.relative_to(root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
