#!/usr/bin/env python3
"""Validate the Experimental root registry and, by default, the real build target.

The registry is a status annotation, not evidence of compilation.  A normal run
therefore invokes ``lake build DavisKahan.Experimental`` and refuses to print a
clean result unless that command succeeds.  ``--static-only`` is available for
source archives that do not contain a Lean toolchain; its output explicitly
states that compilation was not checked.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "dev/experimental-root-status.json"
ALLOWED = {"active", "parked"}


def validate_registry() -> tuple[list[dict[str, object]], list[str], dict[str, int]]:
    data = json.loads(REGISTRY.read_text(encoding="utf8"))
    records = data.get("roots", [])
    errors: list[str] = []
    seen: set[str] = set()
    counts = {status: 0 for status in ALLOWED}
    if not isinstance(records, list):
        return [], ["roots must be a list"], counts
    for record in records:
        if not isinstance(record, dict):
            errors.append(f"invalid root record: {record!r}")
            continue
        module = record.get("module")
        status = record.get("status")
        reason = record.get("reason", "")
        if not isinstance(module, str) or not module.endswith(".lean"):
            errors.append(f"invalid module entry: {module!r}")
            continue
        if module in seen:
            errors.append(f"duplicate module entry: {module}")
        seen.add(module)
        if status not in ALLOWED:
            errors.append(f"invalid status for {module}: {status!r}")
        else:
            counts[status] += 1
        if not (ROOT / module).is_file():
            errors.append(f"registered module is missing: {module}")
        if not isinstance(reason, str) or not reason.strip():
            errors.append(f"missing reason: {module}")
    return records, errors, counts


def print_records(records: list[dict[str, object]]) -> None:
    for record in records:
        print(f"  {record['status']:6}  {record['module']}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--static-only",
        action="store_true",
        help="validate registry syntax only; do not certify compilation",
    )
    args = parser.parse_args()

    records, errors, counts = validate_registry()
    if errors:
        print("Experimental root registry: FAILED")
        for error in errors:
            print(f"  - {error}")
        return 1

    if args.static_only:
        print(
            "Experimental root registry: STATIC CLEAN -- "
            f"{counts['active']} active, {counts['parked']} parked; "
            "compilation not checked"
        )
        print_records(records)
        return 0

    for record in records:
        if record["status"] != "active":
            continue
        module = str(record["module"])
        result = subprocess.run(
            ["lake", "env", "lean", module],
            cwd=ROOT,
            check=False,
        )
        if result.returncode != 0:
            print(
                "Experimental root registry: FAILED -- "
                f"active root did not compile: {module}"
            )
            print_records(records)
            return result.returncode or 1

    result = subprocess.run(
        ["lake", "build", "DavisKahan.Experimental"],
        cwd=ROOT,
        check=False,
    )
    if result.returncode != 0:
        print(
            "Experimental root registry: FAILED -- "
            "lake build DavisKahan.Experimental did not succeed"
        )
        print_records(records)
        return result.returncode or 1

    if records:
        print(
            "Experimental root registry: FAILED -- the Experimental target "
            "builds, but stale active/parked entries remain"
        )
        print_records(records)
        return 1

    print(
        "Experimental root registry: CLEAN -- "
        "lake build DavisKahan.Experimental succeeded; 0 active, 0 parked"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
