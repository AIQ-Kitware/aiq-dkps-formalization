#!/usr/bin/env python3
"""Verify that the vendored Spectra snapshot matches its recorded manifest."""
from __future__ import annotations

import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _snapshot_parent(root: "pathlib.Path") -> "pathlib.Path":
    """Directory holding the vendored Spectra snapshot.

    S6 relocates `vendor/Spectra` to `retired/Spectra` so that agents stop
    reusing it.  Resolving the location here instead of hard-coding it makes
    that move a `git mv` and nothing else -- this script keeps working on either
    side of it.  If neither exists we fall back to `vendor`, so the script's own
    "snapshot is missing" diagnostics fire as before rather than being masked by
    a path error.
    """
    for parent in ("vendor", "retired"):
        if (root / parent / "Spectra").is_dir():
            return root / parent
    return root / "vendor"


_PARENT = _snapshot_parent(ROOT)
SNAPSHOT = _PARENT / "Spectra"
MANIFEST = _PARENT / "Spectra.SHA256SUMS"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as file:
        for block in iter(lambda: file.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    expected: dict[str, str] = {}
    for line in MANIFEST.read_text().splitlines():
        checksum, relative = line.split("  ", 1)
        expected[relative.removeprefix("./")] = checksum

    actual_paths = {
        path.relative_to(SNAPSHOT).as_posix()
        for path in SNAPSHOT.rglob("*")
        if path.is_file()
    }
    expected_paths = set(expected)

    ok = True
    for relative in sorted(expected_paths - actual_paths):
        print(f"missing: vendor/Spectra/{relative}", file=sys.stderr)
        ok = False
    for relative in sorted(actual_paths - expected_paths):
        print(f"unexpected: vendor/Spectra/{relative}", file=sys.stderr)
        ok = False
    for relative in sorted(expected_paths & actual_paths):
        observed = sha256(SNAPSHOT / relative)
        if observed != expected[relative]:
            print(f"modified: vendor/Spectra/{relative}", file=sys.stderr)
            ok = False

    if not ok:
        return 1
    print(f"verified {len(expected)} files in vendor/Spectra")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
