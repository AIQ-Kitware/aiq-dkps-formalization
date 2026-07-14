#!/usr/bin/env python3
"""Enable the local Spectra submodule as a Lake path dependency.

The dependency is deliberately staged.  By default this command refuses to
modify ``lakefile.toml`` until the root and Spectra toolchain pins match.  Use
``--force`` only on a compatibility branch where the mismatch is intentional.
"""

from __future__ import annotations

import argparse
from pathlib import Path

BEGIN = "# BEGIN local Spectra development dependency"
END = "# END local Spectra development dependency"
BLOCK = f'''{BEGIN}
[[require]]
name = "Spectra"
path = "external/Spectra"
{END}
'''


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "lakefile.toml").exists():
            return candidate
    raise SystemExit("could not locate lakefile.toml")


def read_pin(path: Path) -> str:
    return path.read_text().strip() if path.exists() else "<missing>"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    root = find_repo_root(args.repo.resolve())
    spectra = root / "external/Spectra"
    if not (spectra / ".git").exists() and not (spectra / "lakefile.lean").exists():
        raise SystemExit("external/Spectra is not initialized; run bootstrap_spectra_submodule.sh")

    root_pin = read_pin(root / "lean-toolchain")
    spectra_pin = read_pin(spectra / "lean-toolchain")
    if root_pin != spectra_pin and not args.force:
        raise SystemExit(
            "toolchain mismatch: root uses " + root_pin + ", Spectra uses " + spectra_pin
            + ". Port Spectra on the compatibility branch first, or rerun with --force."
        )

    lakefile = root / "lakefile.toml"
    text = lakefile.read_text()
    if BEGIN in text:
        print("Spectra Lake dependency is already enabled")
        return 0

    needle = '''[[require]]
name = "mathlib"
scope = "leanprover-community"
'''
    if needle not in text:
        raise SystemExit("could not find the canonical Mathlib require block in lakefile.toml")
    text = text.replace(needle, needle + "\n" + BLOCK, 1)
    lakefile.write_text(text)
    print("enabled local Spectra path dependency in lakefile.toml")
    print("next: lake update Spectra")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
