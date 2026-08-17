#!/usr/bin/env python3
"""Refresh paper-local working analyses and tracked manuscript snapshots."""

from __future__ import annotations

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent


def run(name: str) -> None:
    subprocess.run([sys.executable, str(HERE / name)], check=True, cwd=HERE.parent)


def main() -> None:
    run("build_dependency_analysis.py")
    run("build_source_census.py")
    run("build_formalization_theory_graph.py")
    run("build_provenance.py")
    run("build_formalization_provenance_credit.py")
    run("build_accounting.py")
    subprocess.run(
        [sys.executable, str(HERE.parent / "build_resource_valuation_20260817.py")],
        check=True,
        cwd=HERE.parent,
    )
    run("build_interactions.py")


if __name__ == "__main__":
    main()
