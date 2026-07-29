#!/usr/bin/env python3
"""Static checks for the pending math-ahead package rebased on 53297a4.

**Promotion is success, not absence.** A manifest entry names a *scratch* module
under `DavisKahan/Experimental/MathAhead/`, and `AGENTS.md` is explicit that the
task for such a sketch is to promote it: take the proof out of the scratch file
and into its source-facing home. So a manifest file that has left its scratch
path is the campaign working, and this checker must not report it as a defect.

It did, for all twelve that had been promoted -- including the ones deleted by
the commit literally titled `P-PROMOTE finish`. A gate that goes red when the
work succeeds gets ignored, and then it cannot report the failure it exists for.

An entry is therefore satisfied when the module is present at its scratch path
**or** a module of the same name exists somewhere else in the tree, which is
reported as `PROMOTED` for the record. Only an entry that is nowhere at all is a
failure -- that is real loss, and it is what this check is now for.
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "dev/overlays/pending-mathahead-rebased-53297a4-gpt56.manifest.txt"
LEAN_ROOT = ROOT / "DavisKahan/Experimental/MathAhead"
BAD = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
# trees that cannot count as a promotion home: staged-for-deletion and vendored
NOT_A_HOME = ("dev/topurge/", "retired/", "external/", ".lake/")


def parse_manifest() -> list[tuple[str, str | None]]:
    """Manifest entries as `(scratch path, recorded promotion target or None)`.

    A line may record where a sketch landed:

    ```text
    DavisKahan/Experimental/MathAhead/Lemma63.lean -> DavisKahan/Sources/...
    ```

    That is needed when promotion *renamed* the module, which the basename
    search below cannot follow.
    """
    entries = []
    for line in MANIFEST.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        scratch, _, target = line.partition("->")
        entries.append((scratch.strip(), target.strip() or None))
    return entries


def promoted_home(path: str, recorded: str | None) -> Path | None:
    """Where a manifest module ended up after promotion, if it is not in place."""
    if recorded is not None:
        return Path(recorded) if (ROOT / recorded).exists() else None
    name = Path(path).name
    for candidate in sorted(ROOT.rglob(name)):
        rel = candidate.relative_to(ROOT).as_posix()
        if rel == path or rel.startswith(NOT_A_HOME):
            continue
        return candidate.relative_to(ROOT)
    return None


def main() -> int:
    entries = parse_manifest()
    paths = [scratch for scratch, _ in entries]
    absent = [(s, t) for s, t in entries if not (ROOT / s).exists()]
    promoted = [(s, home) for s, t in absent if (home := promoted_home(s, t))]
    missing = [s for s, t in absent if not promoted_home(s, t)]
    lean_files = sorted(LEAN_ROOT.rglob("*.lean"))
    escapes = []
    internal_import_missing = []
    for path in lean_files:
        text = path.read_text()
        for match in BAD.finditer(text):
            escapes.append((path.relative_to(ROOT), text.count("\n", 0, match.start()) + 1, match.group(0)))
        for line_no, line in enumerate(text.splitlines(), 1):
            if not line.startswith("import DavisKahan.") and not line.startswith("import ForMathlib."):
                continue
            module = line.split(None, 1)[1].strip()
            target = ROOT / Path(*module.split(".")).with_suffix(".lean")
            if not target.exists():
                internal_import_missing.append((path.relative_to(ROOT), line_no, module))

    print(f"Manifest files: {len(paths)}")
    print(f"Manifest files in place: {len(paths) - len(absent)}/{len(paths)}")
    print(f"Manifest files promoted out of scratch: {len(promoted)}")
    print(f"Lean files in rebased campaign: {len(lean_files)}")
    print(f"Proof-escape markers: {len(escapes)}")
    print(f"Missing internal imports: {len(internal_import_missing)}")

    for path, home in promoted:
        print(f"PROMOTED: {path} -> {home}")
    for path in missing:
        print(f"MISSING FILE: {path}")
    for path, line, token in escapes:
        print(f"PROOF ESCAPE: {path}:{line}: {token}")
    for path, line, module in internal_import_missing:
        print(f"MISSING IMPORT: {path}:{line}: {module}")

    return 1 if missing or escapes or internal_import_missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
