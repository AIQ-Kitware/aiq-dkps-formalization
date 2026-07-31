#!/usr/bin/env python3
"""Tests for `scripts/annotate_roadmap_delivery.py`.

The script's claim is that it can tell a delivered roadmap signature from an
outstanding one **and admit when it cannot**.  The third case is the one worth
testing hardest: matching is by a name's final component, so a short name is
ambiguous, and an annotator that quietly picks the first module asserts a
delivery nobody checked.

Run directly: `python3 scripts/tests/test_annotate_roadmap_delivery.py`.
"""

from __future__ import annotations

import io
import contextlib
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import annotate_roadmap_delivery as gate  # noqa: E402


class AnnotateTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        self._saved = (gate.ROOT, gate.ROADMAP, gate.LIBRARIES, dict(gate.ALIASES))
        gate.ROOT = self.root
        gate.ROADMAP = self.root / "ForTauCetiRoadmap"
        gate.LIBRARIES = ("Lib",)
        gate.ALIASES.clear()
        (self.root / "Lib").mkdir(parents=True)
        gate.ROADMAP.mkdir(parents=True)
        sys.argv = ["annotate"]

    def tearDown(self) -> None:
        gate.ROOT, gate.ROADMAP, gate.LIBRARIES = self._saved[:3]
        gate.ALIASES.clear(); gate.ALIASES.update(self._saved[3])
        sys.argv = ["annotate"]
        self._tmp.cleanup()

    def library(self, rel: str, body: str) -> None:
        path = self.root / "Lib" / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")

    def roadmap(self, topic: str, body: str) -> pathlib.Path:
        path = gate.ROADMAP / topic / "Suggested.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def run_main(self, *argv: str) -> tuple[int, str]:
        sys.argv = ["annotate", *argv]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = gate.main()
        return code, out.getvalue()

    def test_a_delivered_signature_is_marked_with_its_module(self) -> None:
        self.library("A.lean", "theorem landed : True := trivial\n")
        path = self.roadmap("T", "theorem landed : True := by sorry\n")
        self.run_main("--write")
        self.assertIn("-- DELIVERED: `Lib.A`", path.read_text())

    def test_an_outstanding_signature_gets_no_marker(self) -> None:
        self.library("A.lean", "theorem other : True := trivial\n")
        path = self.roadmap("T", "theorem never_landed : True := by sorry\n")
        code, output = self.run_main("--write")
        self.assertNotIn("DELIVERED", path.read_text())
        self.assertIn("never_landed", output)

    def test_an_alias_resolves_and_says_so(self) -> None:
        self.library("A.lean", "def realName : Nat := 0\n")
        gate.ALIASES["sketchName"] = ("realName",)
        path = self.roadmap("T", "def sketchName : Nat := by sorry\n")
        self.run_main("--write")
        text = path.read_text()
        self.assertIn("-- DELIVERED: `Lib.A`", text)
        self.assertIn("(as `realName`)", text)

    def test_an_ambiguous_name_is_a_question_not_a_delivery(self) -> None:
        """Two modules declare `abs`; picking one would assert an unchecked delivery."""
        self.library("A.lean", "def abs : Nat := 0\n")
        self.library("B.lean", "def abs : Nat := 1\n")
        path = self.roadmap("T", "def abs : Nat := by sorry\n")
        code, output = self.run_main("--write")
        text = path.read_text()
        self.assertIn("AMBIGUOUS", text)
        self.assertIn("Lib.A", text)
        self.assertIn("Lib.B", text)
        self.assertIn("ambiguous", output)

    def test_rerunning_replaces_rather_than_stacks_markers(self) -> None:
        """The marker is owned by the script; two runs must not leave two lines."""
        self.library("A.lean", "theorem landed : True := trivial\n")
        path = self.roadmap("T", "theorem landed : True := by sorry\n")
        self.run_main("--write")
        self.run_main("--write")
        self.assertEqual(path.read_text().count("-- DELIVERED:"), 1)

    def test_a_marker_moves_when_the_declaration_moves(self) -> None:
        self.library("A.lean", "theorem landed : True := trivial\n")
        path = self.roadmap("T", "theorem landed : True := by sorry\n")
        self.run_main("--write")
        self.assertIn("`Lib.A`", path.read_text())
        (self.root / "Lib" / "A.lean").unlink()
        self.library("Moved/B.lean", "theorem landed : True := trivial\n")
        self.run_main("--write")
        text = path.read_text()
        self.assertIn("`Lib.Moved.B`", text)
        self.assertNotIn("`Lib.A`", text)

    def test_check_fails_when_markers_are_stale(self) -> None:
        self.library("A.lean", "theorem landed : True := trivial\n")
        self.roadmap("T", "theorem landed : True := by sorry\n")
        code, _ = self.run_main("--check")
        self.assertEqual(code, 1)
        self.run_main("--write")
        code, _ = self.run_main("--check")
        self.assertEqual(code, 0)

    def test_an_unused_alias_is_reported(self) -> None:
        """A stale alias silently excuses the next signature to take that name."""
        self.library("A.lean", "def realName : Nat := 0\n")
        gate.ALIASES["nobodyMentionsThis"] = ("realName",)
        self.roadmap("T", "def landed : Nat := by sorry\n")
        code, output = self.run_main("--check")
        self.assertIn("nobodyMentionsThis", output)
        self.assertEqual(code, 1)

    def test_the_sorry_bodies_are_untouched(self) -> None:
        self.library("A.lean", "theorem landed : True := trivial\n")
        path = self.roadmap("T", "theorem landed : True := by sorry\n")
        self.run_main("--write")
        self.assertIn("by sorry", path.read_text())


class RepositoryTest(unittest.TestCase):
    def test_the_real_roadmap_is_annotated(self) -> None:
        sys.argv = ["annotate", "--check"]
        try:
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = gate.main()
            self.assertEqual(code, 0, out.getvalue()[-800:])
        finally:
            sys.argv = ["annotate"]

    def test_every_alias_names_a_real_declaration(self) -> None:
        """An alias pointing at nothing is an unreviewed claim that reads as reviewed."""
        declarations = gate.library_declarations()
        for sketch, targets in gate.ALIASES.items():
            self.assertTrue(any(t in declarations for t in targets),
                            f"ALIASES[{sketch}] names nothing that exists: {targets}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
