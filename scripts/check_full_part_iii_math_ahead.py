#!/usr/bin/env python3
"""Protect the full Part III math-ahead batch from statement weakening.

The checker verifies two independent properties:

* no executable Davis--Kahan source outside the immutable challenge tree uses
  an unfinished proof term; and
* every declaration restored by the math-ahead batch retains the exact
  normalized signature recorded in the batch manifest.

Proof bodies may change freely while an agent repairs them against the pinned
Lean and Mathlib APIs.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import re

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


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf8"))
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

    if errors:
        print("Full Part III math-ahead contract: FAILED")
        for error in errors:
            print(f"  - {error}")
        return 1

    print(
        "Full Part III math-ahead contract: CLEAN -- "
        f"{manifest['restored_declaration_count']} signatures preserved; "
        "no unfinished proof terms outside Challenge"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
