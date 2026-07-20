#!/usr/bin/env python3
"""Build and audit the full unbounded genuine-spectrum sine-theta chain."""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys


TARGETS = [
    "DavisKahan.Interop.Spectra.OrderedHalfLine",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineCutoffInterface",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineSpectralCutoff",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineBoundedTruncation",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedFromCutoffs",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedEngine",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineAllGap",
    "DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineAllGap",
]

AUDIT_FILE = pathlib.Path(
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullUnboundedAudit.lean"
)

PROTECTED_PREFIXES = [
    pathlib.Path("DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation"),
    pathlib.Path("DavisKahan/Experimental/InfiniteDimensional/Riccati"),
    pathlib.Path("DavisKahan/Sources/DavisKahan1970/Section8.lean"),
]


def run(command: list[str], cwd: pathlib.Path) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(command), flush=True)
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def find_repo_root() -> pathlib.Path:
    here = pathlib.Path.cwd().resolve()
    for candidate in [here, *here.parents]:
        if (candidate / "lakefile.toml").exists() or (candidate / "lakefile.lean").exists():
            return candidate
    raise SystemExit("Could not locate the repository root from the current directory")


def git_changed_files(root: pathlib.Path) -> list[pathlib.Path]:
    result = run(["git", "status", "--short"], root)
    if result.returncode != 0:
        print(result.stdout, end="")
        return []
    changed: list[pathlib.Path] = []
    for line in result.stdout.splitlines():
        if len(line) >= 4:
            changed.append(pathlib.Path(line[3:]))
    return changed


def is_protected(path: pathlib.Path) -> bool:
    text = path.as_posix()
    return any(text == prefix.as_posix() or text.startswith(prefix.as_posix())
               for prefix in PROTECTED_PREFIXES)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--build",
        action="store_true",
        help="Build the dependency chain before running the audit",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit the final summary as JSON",
    )
    args = parser.parse_args()

    root = find_repo_root()
    summary: dict[str, object] = {
        "repo_root": str(root),
        "targets": TARGETS,
        "build_ok": None,
        "audit_ok": False,
        "trusted_dependency_clean": False,
        "protected_changes": [],
    }

    changed = git_changed_files(root)
    protected = [str(path) for path in changed if is_protected(path)]
    summary["protected_changes"] = protected

    if args.build:
        result = run(["lake", "build", *TARGETS], root)
        print(result.stdout, end="")
        summary["build_ok"] = result.returncode == 0
        if result.returncode != 0:
            if args.json:
                print(json.dumps(summary, indent=2, sort_keys=True))
            return result.returncode

    audit = run(["lake", "env", "lean", str(AUDIT_FILE)], root)
    print(audit.stdout, end="")
    summary["audit_ok"] = audit.returncode == 0

    forbidden = "sorryAx"
    clean = audit.returncode == 0 and forbidden not in audit.stdout
    summary["trusted_dependency_clean"] = clean

    if protected:
        print("Protected Agent 4 or Section 8 paths have local changes:")
        for path in protected:
            print("  -", path)

    if clean:
        print("Full unbounded sine-theta trusted-dependency gate: CLEAN")
    else:
        print("Full unbounded sine-theta trusted-dependency gate: OPEN")

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))

    return 0 if clean and not protected else 1


if __name__ == "__main__":
    sys.exit(main())
