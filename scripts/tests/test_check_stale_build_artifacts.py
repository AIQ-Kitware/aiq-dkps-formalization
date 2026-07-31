#!/usr/bin/env python3
"""Tests for `scripts/check_stale_build_artifacts.py`.

The gate's whole claim is that an `.olean` outlives its `.lean`, so the tests
build that state directly rather than through `lake`: a source and an artifact
is fine, an artifact alone is a finding, and `--fix` takes the *whole* artifact
set rather than the `.olean` only.

Run directly: `python3 scripts/tests/test_check_stale_build_artifacts.py`.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_stale_build_artifacts as gate  # noqa: E402


class StaleArtifactTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        self._saved = (gate.ROOT, gate.BUILD, gate.IR, gate.LIBS)
        gate.ROOT = self.root
        gate.BUILD = self.root / ".lake/build/lib/lean"
        gate.IR = self.root / ".lake/build/ir"
        gate.LIBS = ("DavisKahan",)
        gate.BUILD.mkdir(parents=True)
        sys.argv = ["gate"]

    def tearDown(self) -> None:
        gate.ROOT, gate.BUILD, gate.IR, gate.LIBS = self._saved
        sys.argv = ["gate"]
        self._tmp.cleanup()

    def artifact(self, rel: str, *extensions: str) -> None:
        for extension in extensions or (".olean",):
            path = gate.BUILD / (rel + extension)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("")

    def source(self, rel: str) -> None:
        path = self.root / (rel + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("")

    def test_artifact_with_a_source_is_fine(self) -> None:
        self.source("DavisKahan/A")
        self.artifact("DavisKahan/A")
        self.assertEqual(gate.main(), 0)

    def test_artifact_without_a_source_is_a_finding(self) -> None:
        self.artifact("DavisKahan/Gone")
        self.assertEqual(gate.main(), 0)          # report mode never fails
        sys.argv = ["gate", "--check"]
        self.assertEqual(gate.main(), 1)

    def test_fix_removes_the_whole_artifact_set(self) -> None:
        """A leftover `.trace` beside a deleted `.olean` is its own failure."""
        self.artifact("DavisKahan/Gone", ".olean", ".ilean", ".trace", ".hash")
        sys.argv = ["gate", "--fix"]
        self.assertEqual(gate.main(), 0)
        for extension in (".olean", ".ilean", ".trace", ".hash"):
            self.assertFalse((gate.BUILD / ("DavisKahan/Gone" + extension)).exists(),
                             f"{extension} survived --fix")

    def test_fix_spares_a_module_that_still_has_a_source(self) -> None:
        self.source("DavisKahan/Live")
        self.artifact("DavisKahan/Live", ".olean", ".trace")
        self.artifact("DavisKahan/Gone", ".olean")
        sys.argv = ["gate", "--fix"]
        self.assertEqual(gate.main(), 0)
        self.assertTrue((gate.BUILD / "DavisKahan/Live.olean").exists())
        self.assertFalse((gate.BUILD / "DavisKahan/Gone.olean").exists())

    def test_a_renamed_module_leaves_the_old_name_behind(self) -> None:
        """The EXP-CONT shape: `X.Continuation.Core` lands, `X.ContinuationCore` lingers."""
        self.source("DavisKahan/SinTheta/Continuation/Core")
        self.artifact("DavisKahan/SinTheta/Continuation/Core")
        self.artifact("DavisKahan/SinTheta/ContinuationCore")
        sys.argv = ["gate", "--check"]
        self.assertEqual(gate.main(), 1)

    def test_other_libraries_are_not_judged(self) -> None:
        """Dependency artifacts have no source in this repository, by design."""
        self.artifact("Mathlib/Analysis/Whatever")
        sys.argv = ["gate", "--check"]
        self.assertEqual(gate.main(), 0)

    def test_missing_build_tree_is_not_a_finding(self) -> None:
        gate.BUILD = self.root / "nonexistent"
        sys.argv = ["gate", "--check"]
        self.assertEqual(gate.main(), 0)


class RepositoryTest(unittest.TestCase):
    def test_the_real_build_tree_is_clean(self) -> None:
        self.assertEqual(gate.main(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
