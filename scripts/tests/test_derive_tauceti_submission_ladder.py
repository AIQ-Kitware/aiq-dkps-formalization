#!/usr/bin/env python3
"""Standard-library tests for the `--sync` writer in
scripts/derive_tauceti_submission_ladder.py.

The parsing here is the part that can silently do the wrong thing: `--sync`
rewrites a document in place, so a section-boundary bug would eat prose rather
than report an error.  These tests pin the three behaviours that matter --
prose between a tally and its bullets survives, a rung's bullet list is
replaced wholesale, and syncing twice changes nothing.
"""
from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "derive_tauceti_submission_ladder.py"
SPEC = importlib.util.spec_from_file_location("derive_tauceti_submission_ladder", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)

DOC = """# Ladder

Cumulative after F: 41 of 100 `ForTauCeti` modules.

### Rung A — First

**2 new, cumulative closed slice 2.**

Prose between the tally and the list, which a human wrote and `--sync` must not
touch.

  - `Analysis.B`
  - `Analysis.A`

Trailing prose for rung A.

### Rung B — Second

**1 new, cumulative closed slice 3.**

  - `Analysis.C`
"""

DATA = {
    "total_modules": 100,
    "rungs": [
        {"rung": "A", "title": "First", "new": 2, "closed_slice": 2,
         "new_modules": ["Analysis.A", "Analysis.B"], "unknown_seeds": []},
        {"rung": "B", "title": "Second", "new": 1, "closed_slice": 3,
         "new_modules": ["Analysis.C"], "unknown_seeds": []},
    ],
    "off_ladder": [],
}


class RungSectionTest(unittest.TestCase):
    def test_sections_span_to_the_next_heading(self) -> None:
        lines = DOC.splitlines()
        sections = M.rung_sections(DOC)
        self.assertEqual([s[0] for s in sections], ["A", "B"])
        a_key, a_start, a_end = sections[0]
        self.assertTrue(lines[a_start].startswith("### Rung A"))
        self.assertTrue(lines[a_end].startswith("### Rung B"))

    def test_bullet_block_is_the_first_contiguous_run(self) -> None:
        lines = DOC.splitlines()
        _, start, end = M.rung_sections(DOC)[0]
        span = M.bullet_block(lines, start, end)
        self.assertIsNotNone(span)
        self.assertEqual([lines[i] for i in range(*span)],
                         ["  - `Analysis.B`", "  - `Analysis.A`"])

    def test_bullet_block_is_none_when_a_rung_lists_nothing(self) -> None:
        lines = ["### Rung Z — Empty", "", "**0 new, cumulative closed slice 9.**", ""]
        self.assertIsNone(M.bullet_block(lines, 0, len(lines)))


class SyncTest(unittest.TestCase):
    def _sync(self, text: str) -> str:
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "ladder.md"
            path.write_text(text)
            old = M.LADDER
            try:
                M.LADDER = path
                M.sync(DATA)
                return path.read_text()
            finally:
                M.LADDER = old

    def test_prose_around_the_list_survives(self) -> None:
        out = self._sync(DOC)
        self.assertIn("Prose between the tally and the list", out)
        self.assertIn("Trailing prose for rung A.", out)

    def test_bullet_list_is_rewritten_in_derived_order(self) -> None:
        out = self._sync(DOC)
        a = out.index("### Rung A")
        b = out.index("### Rung B")
        self.assertIn("  - `Analysis.A`\n  - `Analysis.B`", out[a:b])

    def test_stale_total_and_tally_are_corrected(self) -> None:
        stale = DOC.replace("of 100 `ForTauCeti` modules", "of 7 `ForTauCeti` modules")
        stale = stale.replace("**2 new, cumulative closed slice 2.**",
                              "**99 new, cumulative closed slice 99.**")
        out = self._sync(stale)
        self.assertIn("of 100 `ForTauCeti` modules", out)
        self.assertIn("**2 new, cumulative closed slice 2.**", out)
        self.assertNotIn("99", out)

    def test_a_missing_module_is_restored(self) -> None:
        short = DOC.replace("  - `Analysis.A`\n", "")
        out = self._sync(short)
        self.assertIn("  - `Analysis.A`", out)

    def test_sync_is_idempotent(self) -> None:
        once = self._sync(DOC)
        self.assertEqual(self._sync(once), once)


if __name__ == "__main__":
    unittest.main()
