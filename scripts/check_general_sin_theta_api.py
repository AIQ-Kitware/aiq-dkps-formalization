#!/usr/bin/env python3
"""Check the declared general sine-theta public surface against its manifest."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

SOURCE_FILES = (
    "DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean",
    "DavisKahan/Sources/DavisKahan1970/GeneralSinThetaExtensions.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalReducing.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalGenuine.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalGenuineGeneralized.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalReal.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalBounded.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalGapConvenience.lean",
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/NaturalTwoSubspace.lean",
)


def find_root() -> pathlib.Path:
    here = pathlib.Path.cwd().resolve()
    for candidate in (here, *here.parents):
        if (candidate / "lakefile.toml").exists() or (candidate / "lakefile.lean").exists():
            return candidate
    raise SystemExit("repository root not found")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    root = find_root()
    manifest_path = root / "dev/general-sin-theta-public-api.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf8"))
    text = "\n".join(
        (root / rel).read_text(encoding="utf8")
        for rel in SOURCE_FILES if (root / rel).exists()
    )

    missing: list[str] = []
    canonical_roles: dict[tuple[str, str, str], str] = {}
    duplicate_roles: list[tuple[str, str, str]] = []
    for endpoint in manifest["endpoints"]:
        name = endpoint["name"]
        short = name.rsplit(".", 1)[-1]
        if not re.search(rf"\b(?:alias|theorem|def|structure)\s+{re.escape(short)}\b", text):
            missing.append(name)
        if endpoint.get("canonical"):
            key = (endpoint["scalar"], endpoint["input"], endpoint["trial"])
            old = canonical_roles.get(key)
            if old is not None:
                duplicate_roles.append((old, name, "/".join(key)))
            else:
                canonical_roles[key] = name

    result = {
        "manifest": str(manifest_path.relative_to(root)),
        "endpoint_count": len(manifest["endpoints"]),
        "missing": missing,
        "duplicate_canonical_roles": duplicate_roles,
        "ok": not missing and not duplicate_roles,
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"General sine-theta API endpoints: {result['endpoint_count']}")
        for name in missing:
            print("MISSING:", name)
        for first, second, role in duplicate_roles:
            print(f"DUPLICATE {role}: {first} / {second}")
        print("API manifest:", "CLEAN" if result["ok"] else "OPEN")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
