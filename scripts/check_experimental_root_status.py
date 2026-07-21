#!/usr/bin/env python3
"""Validate the machine-readable active/parked Experimental root registry."""
from __future__ import annotations
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "dev/experimental-root-status.json"
ALLOWED = {"active", "parked"}

def main() -> int:
    data = json.loads(REGISTRY.read_text(encoding="utf8"))
    errors: list[str] = []
    seen: set[str] = set()
    counts = {status: 0 for status in ALLOWED}
    for record in data.get("roots", []):
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
    if errors:
        print("Experimental root registry: FAILED")
        for error in errors:
            print(f"  - {error}")
        return 1
    print(
        "Experimental root registry: CLEAN -- "
        f"{counts['active']} active, {counts['parked']} parked"
    )
    for record in data["roots"]:
        print(f"  {record['status']:6}  {record['module']}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
