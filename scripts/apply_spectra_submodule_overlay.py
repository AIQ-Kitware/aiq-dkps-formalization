#!/usr/bin/env python3
"""Apply the textual part of the Spectra collaboration overlay idempotently."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

AGENTS_BEGIN = "<!-- BEGIN Spectra collaboration policy -->"
AGENTS_END = "<!-- END Spectra collaboration policy -->"
AGENTS_BLOCK = f"""{AGENTS_BEGIN}
## Spectra collaboration and dependency policy

`Spectra` is the preferred external foundation for complex Hilbert-space
projection-valued measures, spectral calculus, possibly unbounded
self-adjoint operators, bounded polar decomposition, trace class, and
Hilbert--Schmidt infrastructure. Davis--Kahan geometry and paper-facing
perturbation theorems remain owned by this repository.

The active collaboration checkout is a Git submodule at `external/Spectra`.
Follow these rules:

- Do not copy Spectra source into `vendor/lean/` merely to make local progress.
  Use the submodule for coordinated development and contribute generally useful
  changes upstream.
- Mathlib is already a direct dependency. Never vendor excerpts from the pinned
  Mathlib checkout as though they were third-party source.
- Keep `.gitmodules` pointed at the public upstream Spectra repository. Use the
  submodule's `fork` remote for contribution branches.
- Never edit Spectra while it is on detached `HEAD`. Work on a named branch,
  normally based on the current DKPS compatibility branch.
- Do not import the root `Spectra` module. Import the narrowest required modules
  so unrelated physics and analysis developments do not enter the dependency
  cone.
- Keep a thin bridge in `DavisKahan/` for DKPS-specific names and interfaces.
  PVM range subspaces, reducing-subspace lemmas, general graph geometry, and
  other reusable operator theory should be proposed upstream.
- The submodule alone does not make Spectra a production dependency. Enable the
  Lake path dependency only after the root and submodule toolchains are aligned
  and the narrow import smoke test is green.
- Record the exact Spectra gitlink in every result that depends on it. Never
  claim a Spectra-backed declaration is accepted without building it against
  the pinned submodule commit.

See [`dev/spectra-integration-survey-2026-07-14.md`](dev/spectra-integration-survey-2026-07-14.md)
for the audited capability map, ownership boundary, and contribution plan.
{AGENTS_END}
"""

README_BEGIN = "<!-- BEGIN Spectra collaboration checkout -->"
README_END = "<!-- END Spectra collaboration checkout -->"
README_BLOCK = f"""{README_BEGIN}
## Spectra collaboration checkout

The full Hilbert-space Davis--Kahan roadmap needs spectral-measure and
unbounded-operator infrastructure that is being developed in the external
[`Spectra`](https://github.com/adambornemann-glitch/Spectra) project. During the
collaboration phase, this repository tracks Spectra as the Git submodule
`external/Spectra` rather than copying selected source files.

Initialize it with:

```bash
git submodule update --init --recursive
```

For a first checkout, or to configure the upstream and contribution remotes:

```bash
scripts/bootstrap_spectra_submodule.sh --create-fork
```

The submodule is intentionally staged separately from the Lake dependency.
After porting the Spectra compatibility branch to this repository's Lean and
Mathlib pins, enable and test the narrow dependency cone with:

```bash
python3 scripts/enable_spectra_lake_dependency.py
scripts/spectra_import_smoke.sh
```

See `dev/spectra-integration-survey-2026-07-14.md` for the division of labor,
reviewed modules, version-skew risks, and planned upstream contributions.
{README_END}
"""

REGISTRY_BEGIN = "<!-- BEGIN Spectra collaboration reference -->"
REGISTRY_END = "<!-- END Spectra collaboration reference -->"
REGISTRY_BLOCK = f"""{REGISTRY_BEGIN}
## Active external dependency candidate: `adambornemann-glitch/Spectra`

- Repository: <https://github.com/adambornemann-glitch/Spectra>
- Audited commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- License: Apache-2.0 in the repository and inspected source modules.
- Integration mode: Git submodule during active collaboration; later a pinned
  Lake Git dependency if the required APIs merge upstream.
- Full audit: `dev/spectra-integration-survey-2026-07-14.md`.

Spectra is the leading candidate for the complex PVM, spectral-theorem,
unbounded self-adjoint, bounded polar-decomposition, trace-class, and
Hilbert--Schmidt substrate. It does not contain the Davis--Kahan graph, angle,
Sylvester, or four-theorem geometry. General PVM range-subspace and reducing
subspace infrastructure should be contributed upstream; paper-facing
perturbation results remain in this repository.

Do not copy Spectra files into `vendor/lean/` as the production integration
strategy, and do not classify declarations from the project's existing Mathlib
dependency as third-party vendor material.
{REGISTRY_END}
"""

LAKE_BEGIN = "# BEGIN staged Spectra collaboration note"
LAKE_END = "# END staged Spectra collaboration note"
LAKE_BLOCK = f"""{LAKE_BEGIN}
# Spectra is developed in the external/Spectra Git submodule. It is not
# enabled as a Lake dependency until its compatibility branch matches this
# workspace's Lean and Mathlib pins. Use
# scripts/enable_spectra_lake_dependency.py after that gate is green.
{LAKE_END}
"""


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "lakefile.toml").exists():
            return candidate
    raise SystemExit("could not locate repository root")


def insert_before(path: Path, marker: str, block: str, before: str) -> None:
    text = path.read_text()
    if marker in text:
        return
    if before not in text:
        raise SystemExit(f"could not find insertion point in {path}")
    path.write_text(text.replace(before, block + "\n" + before, 1))


def patch_readme(path: Path) -> None:
    text = path.read_text()
    if "external/Spectra" not in text:
        needle = (
            "├── dev/                   # engineering memory: benchmark questions + "
            "debug postmortems (agent-readable)\n"
        )
        if needle in text:
            text = text.replace(
                needle,
                needle
                + "├── external/Spectra       # Git submodule for collaborative "
                "spectral/operator infrastructure\n",
                1,
            )
    if README_BEGIN not in text:
        needle = "## Build\n"
        if needle not in text:
            raise SystemExit("could not find README build section")
        text = text.replace(needle, README_BLOCK + "\n" + needle, 1)
    path.write_text(text)


def patch_lake(path: Path) -> None:
    text = path.read_text()
    if LAKE_BEGIN in text:
        return
    needle = '''[[require]]
name = "mathlib"
scope = "leanprover-community"
'''
    if needle not in text:
        raise SystemExit("could not find Mathlib require block")
    path.write_text(text.replace(needle, needle + "\n" + LAKE_BLOCK, 1))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = find_repo_root(args.repo.resolve())

    insert_before(
        root / "AGENTS.md",
        AGENTS_BEGIN,
        AGENTS_BLOCK,
        "## Lean source conventions\n",
    )
    patch_readme(root / "README.md")
    patch_lake(root / "lakefile.toml")

    registry = root / "dev/external-lean-references.md"
    if registry.exists():
        insert_before(
            registry,
            REGISTRY_BEGIN,
            REGISTRY_BLOCK,
            "## Reference-only sources: no visible license\n",
        )

    cleanup = root / "scripts/remove_redundant_mathlib_vendor_snapshots.py"
    if cleanup.exists():
        subprocess.run(["python3", str(cleanup), "--repo", str(root)], check=True)

    print("applied Spectra collaboration policy and staged dependency notes")
    print("next: scripts/bootstrap_spectra_submodule.sh --create-fork")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
