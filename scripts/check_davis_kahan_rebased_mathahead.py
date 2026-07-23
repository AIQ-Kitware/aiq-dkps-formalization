#!/usr/bin/env python3
"""Static checks for the pending math-ahead package rebased on 53297a4."""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "dev/overlays/pending-mathahead-rebased-53297a4-gpt56.manifest.txt"
LEAN_ROOT = ROOT / "DavisKahan/Experimental/MathAhead"
BAD = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")


def main() -> int:
    paths = [line.strip() for line in MANIFEST.read_text().splitlines() if line.strip()]
    missing = [path for path in paths if not (ROOT / path).exists()]
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
    print(f"Manifest files present: {len(paths) - len(missing)}/{len(paths)}")
    print(f"Lean files in rebased campaign: {len(lean_files)}")
    print(f"Proof-escape markers: {len(escapes)}")
    print(f"Missing internal imports: {len(internal_import_missing)}")

    for path in missing:
        print(f"MISSING FILE: {path}")
    for path, line, token in escapes:
        print(f"PROOF ESCAPE: {path}:{line}: {token}")
    for path, line, module in internal_import_missing:
        print(f"MISSING IMPORT: {path}:{line}: {module}")

    return 1 if missing or escapes or internal_import_missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
