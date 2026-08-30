#!/usr/bin/env python3
"""Deterministic staging -> Tau Ceti export.

Copies a `ForTauCeti.*` staging cluster into a Tau Ceti checkout, applying
exactly one class of transformation: rewriting sibling module imports
`ForTauCeti.X` -> `TauCeti.X` and mapping the file path `ForTauCeti/X.lean` ->
`<tauceti>/TauCeti/X.lean`.  Everything else -- declaration namespaces,
provenance, copyright header, proof bodies -- is copied verbatim, because
declarations already carry their final `TauCeti` / `ContinuousLinearMap` names.

The transformation, the import firewall, the refusal to overwrite a file that is
not a declared export target, and NEW/MATCH/DIFF reporting are
`aiq-lean source export`, driven by `dev/tauceti/extraction-manifest.json`.

What stays here is the checkout policy.  The Tau Ceti checkout is an explicit,
optional input; this repository no longer carries one as a submodule.  `--check`
may read the Lake package copy, but **`--write` demands an editable checkout the
operator controls**: Lake's package directory is a cache, is not a Git working
tree anyone should commit into, and `lake update` may replace it without warning.

Usage:
    python3 scripts/export_for_tauceti.py --cluster approximation-number --check
    python3 scripts/export_for_tauceti.py --cluster approximation-number --write \\
        --tauceti-root ~/code/TauCeti
"""
from __future__ import annotations

import argparse
import pathlib
import sys

try:
    from aiq_lean_tools.module_export import ModuleExportPolicy, export_modules
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _external_checkouts import MissingCheckout, tauceti_root  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "dev/tauceti/extraction-manifest.json"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cluster", help="export one manifest cluster (default: all)")
    parser.add_argument("--check", action="store_true",
                        help="compare the Tau Ceti copy against the transformed staging source")
    parser.add_argument("--write", action="store_true", help="perform the copy")
    parser.add_argument("--tauceti-root", default=None,
                        help="path to a Tau Ceti checkout (or set TAUCETI_ROOT)")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)

    if args.write and args.check:
        parser.error("--check and --write are mutually exclusive")

    try:
        target = tauceti_root(args.tauceti_root, require_editable=args.write, required=True)
    except MissingCheckout as ex:
        print(f"ERROR: {ex}", file=sys.stderr)
        return 2

    report = export_modules(
        ModuleExportPolicy.load(MANIFEST_PATH),
        source_root=ROOT,
        target_root=target,
        cluster=args.cluster,
        write=args.write,
    )
    if args.json:
        import json

        json.dump(report.to_json(), sys.stdout, indent=2)
        print()
        return 0 if report.ok else 1

    for row in report.items:
        print(f"{row.status:<10} {row.source_module} -> {row.target_module}")
    for finding in report.findings:
        print(f"{finding.level.upper():8s}[{finding.code}] {finding.message} {finding.location}")
    verb = "written" if args.write else "checked"
    print(f"export {verb} against {target}: {len(report.items)} module(s); "
          f"{'OK' if report.ok else 'FAILED'}")
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
