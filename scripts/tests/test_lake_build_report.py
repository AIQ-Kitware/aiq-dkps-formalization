#!/usr/bin/env python3
"""Standard-library tests for scripts/lake_build_report.py."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "lake_build_report.py"
SPEC = importlib.util.spec_from_file_location("lake_build_report", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class ParseTest(unittest.TestCase):
    def test_lake_forwarded_diagnostic(self) -> None:
        diagnostic = MODULE.parse_diagnostic_header(
            "error: DavisKahan/Test.lean:60:17: Invalid field `foo`"
        )
        self.assertIsNotNone(diagnostic)
        assert diagnostic is not None
        self.assertEqual(diagnostic.severity, "error")
        self.assertEqual(diagnostic.file, "DavisKahan/Test.lean")
        self.assertEqual(diagnostic.line, 60)
        self.assertEqual(diagnostic.column, 17)
        self.assertEqual(diagnostic.message, "Invalid field `foo`")

    def test_direct_lean_diagnostic(self) -> None:
        diagnostic = MODULE.parse_diagnostic_header(
            "DavisKahan/Test.lean:9:4: warning: declaration uses 'sorry'"
        )
        self.assertIsNotNone(diagnostic)
        assert diagnostic is not None
        self.assertEqual(diagnostic.severity, "warning")
        self.assertEqual(diagnostic.file, "DavisKahan/Test.lean")
        self.assertEqual(diagnostic.line, 9)
        self.assertEqual(diagnostic.column, 4)

    def test_wrapper_noise_is_not_a_diagnostic(self) -> None:
        result = MODULE.parse_output(
            [
                "error: DavisKahan/Test.lean:3:2: bad term",
                "context line",
                "error: Lean exited with code 1",
                "Some required targets logged failures:",
                "- DavisKahan.Test",
                "error: build failed",
            ]
        )
        self.assertEqual(len(result.diagnostics), 1)
        self.assertEqual(result.diagnostics[0].body, ["context line"])
        self.assertEqual(len(result.synthetic_lines), 4)

    def test_exact_deduplication(self) -> None:
        result = MODULE.parse_output(
            [
                "error: DavisKahan/Test.lean:3:2: bad term",
                "same body",
                "error: DavisKahan/Test.lean:3:2: bad term",
                "same body",
            ]
        )
        unique = MODULE.deduplicate(result.diagnostics)
        self.assertEqual(len(unique), 1)
        self.assertEqual(unique[0].repeats, 2)

    def test_one_based_tab_aware_column(self) -> None:
        self.assertEqual(MODULE.display_column("\tfoo", 2, 4), 4)
        self.assertEqual(MODULE.display_column("abcd", 1, 2), 0)
        self.assertEqual(MODULE.display_column("abcd", 4, 2), 3)

    def test_windows_style_path(self) -> None:
        diagnostic = MODULE.parse_diagnostic_header(
            r"error: C:\\repo\\DavisKahan\\Test.lean:12:7: bad term"
        )
        self.assertIsNotNone(diagnostic)
        assert diagnostic is not None
        self.assertEqual(diagnostic.line, 12)
        self.assertEqual(diagnostic.column, 7)
        self.assertTrue(diagnostic.file.endswith("Test.lean"))


if __name__ == "__main__":
    unittest.main()
