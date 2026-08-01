#!/usr/bin/env python3
"""Compile-gated contract for the full Part III math-ahead batch.

Static checks protect declaration signatures and reject unfinished proof terms,
but they do not establish that Lean accepts a declaration.  Therefore the
default mode also elaborates every changed module with ``lake env lean`` and
returns success only when both the static and compiler checks pass.

Use ``--module PATH`` while repairing one dependency root.  Use
``--static-only`` only for artifact construction in an environment without
Lean; its success message is deliberately labelled STATIC and must never be
reported as proof completion.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "dev/full-part-iii-math-ahead-restoration-manifest-2026-07-20.json"

DECL_RE = re.compile(
    r"^(?:private\s+|noncomputable\s+|protected\s+|"
    r"@[A-Za-z0-9_\[\], .\"'()]+\s+)*"
    r"(?:theorem|lemma|def|noncomputable def|structure|class|instance|abbrev)"
    r"\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
ADMISSION_RE = re.compile(r"(?<![A-Za-z0-9_.'])(?:sorry|admit)(?![A-Za-z0-9_'])")
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def strip_comments_preserving_lines(text: str) -> str:
    def blank_block(match: re.Match[str]) -> str:
        value = match.group(0)
        return "\n" * value.count("\n")

    text = BLOCK_COMMENT_RE.sub(blank_block, text)
    return LINE_COMMENT_RE.sub("", text)


def declaration_blocks(text: str) -> dict[str, str]:
    matches = list(DECL_RE.finditer(text))
    return {
        match.group(1): text[
            match.start() : matches[index + 1].start()
            if index + 1 < len(matches)
            else len(text)
        ]
        for index, match in enumerate(matches)
    }


def normalized_signature(block: str) -> str:
    positions = []
    for marker in (" :=", "\n  where", "\nwhere"):
        position = block.find(marker)
        if position >= 0:
            positions.append(position)
    if not positions:
        raise ValueError("declaration has no body marker")
    return re.sub(r"\s+", " ", block[: min(positions)]).strip()


def static_errors(manifest: dict[str, object]) -> list[str]:
    errors: list[str] = []

    for source in sorted((ROOT / "DavisKahan").rglob("*.lean")):
        if "Challenge" in source.parts:
            continue
        stripped = strip_comments_preserving_lines(
            source.read_text(encoding="utf8", errors="replace")
        )
        for match in ADMISSION_RE.finditer(stripped):
            line = stripped.count("\n", 0, match.start()) + 1
            errors.append(
                f"unfinished proof term: {source.relative_to(ROOT)}:{line}"
            )

    cache: dict[str, dict[str, str]] = {}
    for record in manifest["restored_declarations"]:
        path = record["path"]
        if path not in cache:
            source = ROOT / path
            if not source.exists():
                errors.append(f"restored source is missing: {path}")
                cache[path] = {}
                continue
            cache[path] = declaration_blocks(source.read_text(encoding="utf8"))
        block = cache[path].get(record["name"])
        if block is None:
            errors.append(f"restored declaration is missing: {path}:{record['name']}")
            continue
        try:
            signature = normalized_signature(block)
        except ValueError as ex:
            errors.append(f"cannot parse signature: {path}:{record['name']}: {ex}")
            continue
        digest = hashlib.sha256(signature.encode("utf8")).hexdigest()
        if digest != record["signature_sha256"]:
            errors.append(f"statement changed: {path}:{record['name']}")

    return errors


def rebaseline(manifest: dict[str, object], reason: str) -> list[str]:
    """Recompute stored hashes for declarations whose statement has changed.

    **This rewrites the contract, so it is deliberately not automatic.**  The
    manifest is a record of what was restored on 2026-07-20 and its whole value
    is that it does not drift silently.  A rebaseline is correct only when the
    divergence is a deliberate, checked change -- and the reason goes into
    `source_corrections` beside the 2026-07-20 entries, so the record says what
    happened rather than merely agreeing with the code again.
    """
    changed: list[str] = []
    cache: dict[str, dict[str, str]] = {}
    for record in manifest["restored_declarations"]:
        path = record["path"]
        if path not in cache:
            source = ROOT / path
            if not source.exists():
                continue
            cache[path] = declaration_blocks(source.read_text(encoding="utf8"))
        block = cache[path].get(record["name"])
        if block is None:
            continue
        try:
            digest = hashlib.sha256(
                normalized_signature(block).encode("utf8")).hexdigest()
        except ValueError:
            continue
        if digest != record["signature_sha256"]:
            record["signature_sha256"] = digest
            changed.append(f"{path}:{record['name']}")
    if changed:
        manifest.setdefault("source_corrections", []).append({
            "correction": reason,
            "date": "2026-07-31",
            "declarations": sorted({name.split(":")[-1] for name in changed}),
            "path": sorted({name.split(":")[0] for name in changed}),
        })
    return changed


def manifest_modules(manifest: dict[str, object]) -> list[str]:
    modules = {record["path"] for record in manifest["restored_declarations"]}
    modules.update(manifest.get("additional_compilation_modules", ()))
    return sorted(modules)


def compile_modules(modules: list[str]) -> list[str]:
    if shutil.which("lake") is None:
        return ["lake executable is unavailable; compiler certification was not run"]

    errors: list[str] = []
    for index, module in enumerate(modules, 1):
        print(f"[{index}/{len(modules)}] lake env lean {module}", flush=True)
        completed = subprocess.run(
            ["lake", "env", "lean", module],
            cwd=ROOT,
            check=False,
        )
        if completed.returncode != 0:
            errors.append(f"compiler failure ({completed.returncode}): {module}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--static-only",
        action="store_true",
        help="check signatures and proof markers without invoking Lean",
    )
    parser.add_argument(
        "--rebaseline",
        metavar="REASON",
        help="recompute the stored signature hash of every declaration whose statement "
             "has changed, recording REASON in `source_corrections`.  Use ONLY after "
             "confirming by hand that each change is deliberate and mathematically "
             "sound; this rewrites the contract the gate enforces.",
    )
    parser.add_argument(
        "--module",
        action="append",
        default=[],
        help="compile only this restored module; may be repeated",
    )
    args = parser.parse_args()

    manifest = json.loads(MANIFEST.read_text(encoding="utf8"))
    if args.rebaseline:
        changed = rebaseline(manifest, args.rebaseline)
        if not changed:
            print("nothing to rebaseline: every stored signature already matches")
            return 0
        MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf8")
        print(f"rebaselined {len(changed)} signature(s):")
        for name in changed:
            print(f"  - {name}")
        print("\nRe-run without --rebaseline to check the result.")
        return 0
    errors = static_errors(manifest)
    if errors:
        print("Full Part III math-ahead static contract: FAILED")
        for error in errors:
            print(f"  - {error}")
        return 1

    count = manifest["restored_declaration_count"]
    if args.static_only:
        print(
            "Full Part III math-ahead static contract: STATIC CLEAN -- "
            f"{count} guarded signatures match the manifest; "
            "no unfinished proof terms outside Challenge; "
            "Lean compilation not checked"
        )
        return 0

    available = manifest_modules(manifest)
    if args.module:
        requested = []
        for module in args.module:
            candidate = pathlib.Path(module)
            if candidate.is_absolute() or ".." in candidate.parts:
                print(f"module path must be repository-relative: {module}")
                return 2
            normalized = candidate.as_posix()
            source = ROOT / normalized
            if source.suffix != ".lean" or not source.is_file():
                print(f"Lean source does not exist: {normalized}")
                return 2
            if normalized not in requested:
                requested.append(normalized)
        modules = requested
    else:
        modules = available

    compile_failures = compile_modules(modules)
    if compile_failures:
        print("Full Part III math-ahead compiler contract: FAILED")
        for error in compile_failures:
            print(f"  - {error}")
        return 1

    print(
        "Full Part III math-ahead compiler contract: CLEAN -- "
        f"{count} guarded signatures match the manifest; "
        f"{len(modules)} restored modules compile; "
        "no unfinished proof terms outside Challenge"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
