#!/usr/bin/env python3
"""Rebuild every generated accounting/interaction artifact for the paper."""

from __future__ import annotations

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent


def run(name: str) -> None:
    subprocess.run([sys.executable, str(HERE / name)], check=True, cwd=HERE.parent)


def main() -> None:
    run("build_accounting.py")
    run("build_interactions.py")


if __name__ == "__main__":
    main()
