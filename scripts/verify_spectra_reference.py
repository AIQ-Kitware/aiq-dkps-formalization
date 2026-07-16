#!/usr/bin/env python3
"""Verify the Spectra reference submodule and vendored snapshot pin."""
from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPECTED_URL = "https://github.com/adambornemann-glitch/Spectra.git"
EXPECTED_COMMIT = "8dbaaf6728d1342ae16acf79fd7eef7c59b37e63"


def git(*args: str, cwd: pathlib.Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def fail(message: str) -> int:
    print(message, file=sys.stderr)
    return 1


def main() -> int:
    modules = ROOT / ".gitmodules"
    if not modules.is_file():
        return fail("missing .gitmodules")

    path = git("config", "-f", ".gitmodules", "--get", "submodule.external/Spectra.path")
    url = git("config", "-f", ".gitmodules", "--get", "submodule.external/Spectra.url")
    if path != "external/Spectra":
        return fail(f"unexpected submodule path: {path}")
    if url != EXPECTED_URL:
        return fail(f"unexpected submodule URL: {url}")

    stage = git("ls-files", "--stage", "external/Spectra").split()
    if len(stage) < 2 or stage[0] != "160000":
        return fail("external/Spectra is not recorded as a gitlink")
    if stage[1] != EXPECTED_COMMIT:
        return fail(f"gitlink is {stage[1]}, expected {EXPECTED_COMMIT}")

    checkout = ROOT / "external" / "Spectra"
    if checkout.is_dir():
        observed = git("rev-parse", "HEAD", cwd=checkout)
        if observed != EXPECTED_COMMIT:
            return fail(f"submodule checkout is {observed}, expected {EXPECTED_COMMIT}")

    print(f"verified external/Spectra reference at {EXPECTED_COMMIT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
