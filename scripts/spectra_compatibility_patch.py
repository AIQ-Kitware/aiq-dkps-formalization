#!/usr/bin/env python3
"""Manage the recorded DKPS compatibility patch for the vendored Spectra tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "Spectra"
UPSTREAM_META = ROOT / "vendor" / "Spectra.UPSTREAM.md"
PATCH = (
    ROOT
    / "vendor"
    / "patches"
    / "Spectra"
    / "0001-dkps-lean-v4.32-mathlib-compatibility.patch"
)
PATCH_SHA = PATCH.with_suffix(PATCH.suffix + ".sha256")
PRISTINE_SUPERPROJECT_COMMIT = "cd47c879fe146c2be6f698f4dea8161ac294001a"
UPSTREAM_COMMIT = "8dbaaf6728d1342ae16acf79fd7eef7c59b37e63"


def run(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        check=check,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def patch_bytes() -> bytes:
    return PATCH.read_bytes()


def current_vendor_diff() -> bytes:
    proc = subprocess.run(
        [
            "git",
            "-c",
            f"safe.directory={ROOT}",
            "diff",
            "--binary",
            "--unified=0",
            PRISTINE_SUPERPROJECT_COMMIT,
            "--",
            "vendor/Spectra",
        ],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.stdout


def expected_digest() -> str:
    fields = PATCH_SHA.read_text().split()
    if len(fields) != 2 or fields[1] != PATCH.name:
        raise RuntimeError(f"malformed patch digest file: {PATCH_SHA}")
    return fields[0]


def verify_digest() -> None:
    actual = hashlib.sha256(patch_bytes()).hexdigest()
    expected = expected_digest()
    if actual != expected:
        raise RuntimeError(
            f"compatibility patch digest mismatch: expected {expected}, got {actual}"
        )


def verify_metadata() -> None:
    metadata = UPSTREAM_META.read_text()
    if UPSTREAM_COMMIT not in metadata:
        raise RuntimeError(f"{UPSTREAM_META} does not record {UPSTREAM_COMMIT}")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    spectra = [p for p in manifest["packages"] if p.get("name") == "Spectra"]
    if len(spectra) != 1 or spectra[0].get("dir") != "vendor/Spectra":
        raise RuntimeError("root lake-manifest.json does not resolve Spectra from vendor/Spectra")

    run(
        "git",
        "-c",
        f"safe.directory={ROOT}",
        "cat-file",
        "-e",
        f"{PRISTINE_SUPERPROJECT_COMMIT}^{{commit}}",
    )

    reference_git = ROOT / "external" / "Spectra" / ".git"
    if reference_git.exists():
        proc = run(
            "git",
            "-c",
            f"safe.directory={ROOT / 'external' / 'Spectra'}",
            "-C",
            str(ROOT / "external" / "Spectra"),
            "rev-parse",
            "HEAD",
        )
        actual = proc.stdout.strip()
        if actual != UPSTREAM_COMMIT:
            raise RuntimeError(
                f"external/Spectra is at {actual}, expected {UPSTREAM_COMMIT}"
            )


def state() -> str:
    diff = current_vendor_diff()
    if not diff:
        return "pristine"
    if diff == patch_bytes():
        return "applied"
    return "diverged"


def verify() -> None:
    verify_digest()
    verify_metadata()
    current = state()
    if current != "applied":
        raise RuntimeError(
            "vendor/Spectra is not exactly the recorded compatibility state "
            f"(detected {current})"
        )
    print("Spectra compatibility patch: verified")
    print(f"  upstream: {UPSTREAM_COMMIT}")
    print(f"  pristine superproject base: {PRISTINE_SUPERPROJECT_COMMIT}")
    print(f"  patch sha256: {expected_digest()}")


def apply_patch() -> None:
    verify_digest()
    verify_metadata()
    current = state()
    if current == "applied":
        print("Spectra compatibility patch is already applied")
        return
    if current != "pristine":
        raise RuntimeError("vendor/Spectra has unrecorded changes; refusing to apply patch")
    run("git", "-c", f"safe.directory={ROOT}", "apply", "--unidiff-zero", "--check", str(PATCH))
    run("git", "-c", f"safe.directory={ROOT}", "apply", "--unidiff-zero", str(PATCH))
    verify()


def remove_patch() -> None:
    verify_digest()
    current = state()
    if current == "pristine":
        print("Spectra compatibility patch is already removed")
        return
    if current != "applied":
        raise RuntimeError("vendor/Spectra has unrecorded changes; refusing to reverse patch")
    run(
        "git",
        "-c",
        f"safe.directory={ROOT}",
        "apply",
        "--unidiff-zero",
        "--reverse",
        "--check",
        str(PATCH),
    )
    run(
        "git",
        "-c",
        f"safe.directory={ROOT}",
        "apply",
        "--unidiff-zero",
        "--reverse",
        str(PATCH),
    )
    if state() != "pristine":
        raise RuntimeError("reverse application did not restore the pristine vendor base")
    print("Spectra compatibility patch removed; pristine vendor base restored")


def refresh() -> None:
    diff = current_vendor_diff()
    if not diff:
        raise RuntimeError("vendor/Spectra has no compatibility changes to record")
    PATCH.write_bytes(diff)
    digest = hashlib.sha256(diff).hexdigest()
    PATCH_SHA.write_text(f"{digest}  {PATCH.name}\n")
    print(f"refreshed {PATCH.relative_to(ROOT)}")
    print(f"sha256: {digest}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("verify", "apply", "remove", "refresh", "status"))
    args = parser.parse_args()
    try:
        if args.command == "verify":
            verify()
        elif args.command == "apply":
            apply_patch()
        elif args.command == "remove":
            remove_patch()
        elif args.command == "refresh":
            refresh()
        else:
            verify_digest()
            verify_metadata()
            print(state())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as exc:
        if isinstance(exc, subprocess.CalledProcessError):
            detail = exc.stderr.strip() or exc.stdout.strip()
            if detail:
                print(detail, file=sys.stderr)
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
