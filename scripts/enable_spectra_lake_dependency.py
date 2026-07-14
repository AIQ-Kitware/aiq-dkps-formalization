#!/usr/bin/env python3
"""Enable and normalize the local Spectra Lake path dependency.

Lake resolves duplicate transitive package requirements according to root
requirement order. Spectra currently carries an older Mathlib manifest, so the
DKPS root Mathlib requirement must appear *after* Spectra and after every other
root ``[[require]]`` block. This keeps the DKPS Mathlib dependency graph
(authoritative for the root Lean toolchain) from being replaced by Spectra's
older Batteries/Aesop/etc. revisions.

The script is idempotent and also repairs lakefiles produced by the earlier
version that inserted Spectra after Mathlib.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

SPECTRA_BEGIN = "# BEGIN local Spectra development dependency"
SPECTRA_END = "# END local Spectra development dependency"
SPECTRA_BLOCK = f'''{SPECTRA_BEGIN}
[[require]]
name = "Spectra"
path = "external/Spectra"
{SPECTRA_END}
'''

MATHLIB_BEGIN = "# BEGIN authoritative root Mathlib dependency"
MATHLIB_END = "# END authoritative root Mathlib dependency"
MATHLIB_BLOCK = f'''{MATHLIB_BEGIN}
# Keep this requirement last among all [[require]] blocks. Spectra currently
# pins an older Mathlib dependency graph; the root DKPS pins must win.
[[require]]
name = "mathlib"
scope = "leanprover-community"
{MATHLIB_END}
'''

SPECTRA_MARKED_RE = re.compile(
    rf"(?ms)^\s*{re.escape(SPECTRA_BEGIN)}\n.*?^{re.escape(SPECTRA_END)}\n?"
)
MATHLIB_MARKED_RE = re.compile(
    rf"(?ms)^\s*{re.escape(MATHLIB_BEGIN)}\n.*?^{re.escape(MATHLIB_END)}\n?"
)

# Compatibility with earlier generated authority comments.
OLD_AUTHORITY_COMMENT_RE = re.compile(
    r'''(?mx)
    ^\# Root dependency authority:[^\n]*\n
    ^\# all \[\[require\]\] blocks\.[^\n]*\n
    ^\# graph; placing the root requirement last makes the DKPS pins authoritative\.\n?
    '''
)

# Compatibility with canonical unmarked blocks and hand-written path blocks.
MATHLIB_UNMARKED_RE = re.compile(
    r'''(?mx)
    ^\[\[require\]\]\n
    name\s*=\s*"mathlib"\n
    scope\s*=\s*"leanprover-community"\n?
    '''
)
SPECTRA_UNMARKED_RE = re.compile(
    r'''(?mx)
    ^\[\[require\]\]\n
    name\s*=\s*"Spectra"\n
    path\s*=\s*"external/Spectra"\n?
    '''
)


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "lakefile.toml").exists():
            return candidate
    raise SystemExit("could not locate lakefile.toml")


def read_pin(path: Path) -> str:
    return path.read_text().strip() if path.exists() else "<missing>"


def normalize_lakefile(text: str) -> str:
    """Place Spectra before the authoritative root Mathlib requirement."""
    had_mathlib = bool(MATHLIB_MARKED_RE.search(text) or MATHLIB_UNMARKED_RE.search(text))
    if not had_mathlib:
        raise SystemExit(
            "could not find the canonical Mathlib require block in lakefile.toml"
        )

    text = SPECTRA_MARKED_RE.sub("\n", text)
    text = MATHLIB_MARKED_RE.sub("\n", text)
    text = OLD_AUTHORITY_COMMENT_RE.sub("", text)
    text = SPECTRA_UNMARKED_RE.sub("\n", text)
    text = MATHLIB_UNMARKED_RE.sub("\n", text)

    marker = "[[lean_lib]]"
    index = text.find(marker)
    if index < 0:
        raise SystemExit("could not find the first [[lean_lib]] table in lakefile.toml")

    prefix = text[:index].rstrip()
    suffix = text[index:].lstrip()
    return prefix + "\n\n" + SPECTRA_BLOCK + "\n" + MATHLIB_BLOCK + "\n" + suffix


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    root = find_repo_root(args.repo.resolve())
    spectra = root / "external/Spectra"
    if not (spectra / ".git").exists() and not (spectra / "lakefile.lean").exists():
        raise SystemExit(
            "external/Spectra is not initialized; run bootstrap_spectra_submodule.sh"
        )

    root_pin = read_pin(root / "lean-toolchain")
    spectra_pin = read_pin(spectra / "lean-toolchain")
    if root_pin != spectra_pin and not args.force:
        raise SystemExit(
            "toolchain mismatch: root uses "
            + root_pin
            + ", Spectra uses "
            + spectra_pin
            + ". Port Spectra on the compatibility branch first, or rerun with --force."
        )

    lakefile = root / "lakefile.toml"
    old = lakefile.read_text()
    new = normalize_lakefile(old)
    if new == old:
        print("Spectra Lake dependency is enabled and dependency order is already normalized")
    else:
        lakefile.write_text(new)
        print("enabled Spectra and made the root Mathlib dependency authoritative")

    print("next: run `lake update` (not `lake update Spectra`)")
    print("then rerun the narrow Spectra bridge build")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
