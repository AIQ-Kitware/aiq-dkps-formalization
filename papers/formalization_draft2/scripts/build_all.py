#!/usr/bin/env python3
"""Refresh paper-local working analyses and tracked manuscript snapshots."""

from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent


def run(name: str, *args: str) -> None:
    subprocess.run([sys.executable, str(HERE / name), *args], check=True, cwd=HERE.parent)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cutoff",
        default=None,
        help="Git ref/commit defining the inclusive accounting history cutoff (default: config, normally HEAD).",
    )
    args = parser.parse_args()

    run("build_dependency_analysis.py")
    run("build_source_census.py")
    run("build_formalization_theory_graph.py")
    run("build_provenance.py")
    run("build_formalization_provenance_credit.py")
    accounting_args = ("--cutoff", args.cutoff) if args.cutoff else ()
    run("build_accounting.py", *accounting_args)
    subprocess.run(
        [sys.executable, str(HERE.parent / "build_resource_valuation_20260817.py")],
        check=True,
        cwd=HERE.parent,
    )
    run("build_interactions.py")


if __name__ == "__main__":
    main()
