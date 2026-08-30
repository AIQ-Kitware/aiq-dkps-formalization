#!/usr/bin/env python3
"""Pre-flight signature check for the challenge comparator.

The comparator exports the challenge (`Conformance`) and solution (`Leaderboard`)
declarations with `lean4export` and compares them **without alpha-normalizing
universe parameters or the instance telescope**.  So a conformance can `lake
build` green, be `#print axioms`-clean, and *still* fail with `statement do not
match` -- the two documented classes being a shifted universe slot (an added or
reordered `variable`, since unused type variables reserve slots) and a missing
instance in the binder telescope.

The comparison itself is `aiq-lean signatures check`, which reads a
`comparator/*.json` config directly: it compares the raw positional universe list
from `#print` (which `#check` alpha-normalizes away, so `#check` alone cannot see
a slot shift) and the fully explicit type from `pp.all #check`.  Empty Lean output
is an error there, never a pass, because two empty captures diff as identical.

This script is the DKPS composition: which configs exist, and running them all.
The real comparator (with landrun) remains ground truth; this only tells you,
cheaply, whether it is worth running.

Usage:
  python3 scripts/check_comparator_signatures.py                       # all comparator/*.json
  python3 scripts/check_comparator_signatures.py comparator/candidate-01-gram-rigidity.json
  python3 scripts/check_comparator_signatures.py --no-build            # modules already built

Exit status is nonzero if any theorem mismatches or errors.

See dev/journals/comparator-statement-export-matching-2026-06-14.md.
"""
from __future__ import annotations

import argparse
import sys
from dataclasses import replace
from pathlib import Path

try:
    from aiq_lean_tools.signatures import SignaturePolicy, compare_signatures
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

ROOT = Path(__file__).resolve().parents[1]
COMPARATOR = ROOT / "comparator"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("configs", nargs="*", help="comparator config paths (default: all)")
    parser.add_argument("--no-build", action="store_true",
                        help="assume the challenge and solution modules are already built")
    args = parser.parse_args(argv)

    configs = [Path(c) for c in args.configs] or sorted(COMPARATOR.glob("*.json"))
    if not configs:
        print(f"no comparator configs found under {COMPARATOR.relative_to(ROOT)}", file=sys.stderr)
        return 1

    # One policy over every config, so the whole set is built once rather than
    # twice per config.  Every pair is given the same `build_targets`, which is
    # what makes the runner's target dedup collapse them into a single
    # `lake build`.
    pairs = []
    for config in configs:
        for pair in SignaturePolicy.load(config).pairs:
            pairs.append((config.name, pair))
    targets = tuple(sorted({
        module for _, pair in pairs for module in (pair.left_module, pair.right_module)
    }))
    policy = SignaturePolicy(
        tuple(replace(pair, name=name, build_targets=targets) for name, pair in pairs),
        build=not args.no_build,
    )
    report = compare_signatures(policy, root=ROOT, build=not args.no_build)
    rows = [(row.pair, row) for row in report.comparisons]
    extra = [
        (finding.location or "", finding)
        for finding in report.findings
        if not any(finding in row.findings for row in report.comparisons)
    ]

    width = max((len(row.declaration) for _, row in rows), default=10)
    print("=" * 70)
    print("Signature pre-flight summary")
    print("=" * 70)
    print(f"{'STATUS':8} {'THEOREM':{width}}  CONFIG")
    failures = 0
    for name, row in rows:
        failures += row.status != "PASS"
        print(f"{row.status:8} {row.declaration:{width}}  {name}")
        for finding in row.findings:
            print(f"           {finding.code}: {finding.message}")
    for name, finding in extra:
        failures += finding.level == "error"
        print(f"{finding.level.upper():8} [{finding.code}] {finding.message}  {name}")
    if failures:
        print(f"\n{failures} of {len(rows)} comparison(s) differ or could not be resolved. "
              "The comparator will reject these.")
        return 1
    print("\nAll theorems match on universe signature and full type. "
          "Safe to run the full comparator.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
