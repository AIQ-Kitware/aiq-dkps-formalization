#!/usr/bin/env python3
"""Remove the staged local Spectra path dependency from lakefile.toml."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

BEGIN = "# BEGIN local Spectra development dependency"
END = "# END local Spectra development dependency"


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "lakefile.toml").exists():
            return candidate
    raise SystemExit("could not locate lakefile.toml")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = find_repo_root(args.repo.resolve())
    path = root / "lakefile.toml"
    text = path.read_text()
    pattern = rf"\n?{re.escape(BEGIN)}.*?{re.escape(END)}\n?"
    new = re.sub(pattern, "\n", text, flags=re.DOTALL)
    if new == text:
        print("Spectra Lake dependency was not enabled")
        return 0
    path.write_text(new)
    print("disabled local Spectra path dependency in lakefile.toml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
