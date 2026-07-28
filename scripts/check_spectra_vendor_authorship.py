#!/usr/bin/env python3
"""Ratchet on DKPS mathematics living inside the vendored Spectra snapshot.

`vendor/Spectra.UPSTREAM.md` states the rule plainly: the snapshot "must remain
byte-for-byte equivalent to the tracked files at that upstream commit", and
project-specific changes "must not be edited into `vendor/Spectra/` as an
undocumented fork".  They are, at scale — whole modules authored here, carrying a
`Copyright (c) 2026 Spectra Formalization Project` header, absent from upstream,
and absent from the managed compatibility patch.

Two consequences, both bad, and neither visible without this check:

1. **Attribution inverts.**  A file in `vendor/` reads as the donor's work.  When
   the Spectra dependency is removed these modules would either be credited to
   Spectra or silently dropped from the provenance ledger — the exact failure the
   ledger exists to prevent.
2. **The documented update procedure destroys them.**  Step 3 of
   `Spectra.UPSTREAM.md` is "replace `vendor/Spectra/` with
   `git archive <new-upstream-commit>`".  Following it deletes every line below.

This is a **ratchet**, not a pass/fail gate: the baseline records what already
exists so the situation cannot grow silently, and the campaign in
`dev/tauceti/spectra-removal-plan.md` drives it to zero.  Adding a new file
fails; removing one and refreshing the baseline is the intended direction.

Usage:
  python3 scripts/check_spectra_vendor_authorship.py            # check ratchet
  python3 scripts/check_spectra_vendor_authorship.py --update   # re-record baseline
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

BASELINE_NAME = "spectra-vendor-authorship-baseline.json"


def upstream_paths(repo: Path) -> set[str] | None:
    ref = repo / "external" / "Spectra"
    if not (ref / ".git").exists():
        return None
    out = subprocess.run(["git", "-C", str(ref), "ls-files"],
                         capture_output=True, text=True, check=False).stdout
    return {p for p in out.splitlines() if p.endswith(".lean")}


def scan(repo: Path) -> list[dict]:
    """Vendored .lean files that do not exist at the pinned upstream commit."""
    upstream = upstream_paths(repo)
    if upstream is None:
        raise SystemExit("external/Spectra reference checkout is missing; cannot classify")
    vendor = repo / "vendor" / "Spectra"
    rows = []
    for path in sorted(vendor.rglob("*.lean")):
        rel = path.relative_to(vendor).as_posix()
        if rel in upstream:
            continue
        head = path.read_text(errors="ignore").splitlines()
        authors = next((l[len("Authors:"):].strip() for l in head[:10]
                        if l.startswith("Authors:")), "")
        rows.append({"path": rel, "lines": len(head), "authors": authors})
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--update", action="store_true", help="re-record the baseline")
    args = ap.parse_args()
    repo = args.repo
    baseline_path = repo / "dev" / "tauceti" / BASELINE_NAME

    rows = scan(repo)
    total = sum(r["lines"] for r in rows)
    payload = {
        "note": ("DKPS-authored modules inside vendor/Spectra. Ratchet: this list may only "
                 "shrink. Driven to zero by dev/tauceti/spectra-removal-plan.md."),
        "fileCount": len(rows),
        "lineCount": total,
        "files": rows,
    }

    if args.update:
        baseline_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"recorded {len(rows)} files / {total} lines in {baseline_path}")
        return 0

    if not baseline_path.exists():
        print(f"missing baseline {baseline_path}; run with --update", file=sys.stderr)
        return 1
    baseline = json.loads(baseline_path.read_text())
    known = {r["path"] for r in baseline["files"]}
    current = {r["path"] for r in rows}

    added = sorted(current - known)
    removed = sorted(known - current)

    if added:
        print("New DKPS-authored files added to vendor/Spectra since the baseline:", file=sys.stderr)
        for p in added:
            print(f"  + {p}", file=sys.stderr)
        print("\nvendor/Spectra is a byte-identical upstream snapshot (Spectra.UPSTREAM.md).\n"
              "Put new mathematics in ForTauCeti/ or DavisKahan/, not in the donor tree.",
              file=sys.stderr)
        return 1

    if removed:
        print(f"{len(removed)} file(s) left vendor/Spectra since the baseline — "
              f"good; refresh with --update:")
        for p in removed:
            print(f"  - {p}")
        return 1

    print(f"ratchet holding: {len(rows)} DKPS-authored files / {total} lines still in "
          f"vendor/Spectra (target 0)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
