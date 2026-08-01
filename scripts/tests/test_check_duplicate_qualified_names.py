"""Tests for `scripts/check_duplicate_qualified_names.py`.

The gate was written after the defect, not before it: on 2026-08-01 `ForTauCeti` held two
`TauCeti.SymmetricGauge` structures, 1141 and 831 lines, with 14 colliding fully-qualified
names.  The live board tracks the decision as `FTC-SYMGAUGE-COLLIDE`; these tests pin the
parser's behaviour so that the *next* collision is caught on the commit that adds it.

Run directly: `python3 scripts/tests/test_check_duplicate_qualified_names.py`.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_duplicate_qualified_names as dup  # noqa: E402


class ParserTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def names(self, body: str) -> set[str]:
        path = self.dir / "M.lean"
        path.write_text(body, encoding="utf-8")
        return dup.declarations(path)

    def test_a_declaration_is_qualified_by_its_namespaces(self) -> None:
        self.assertEqual(
            self.names("namespace A\nnamespace B\ntheorem foo : True := trivial\nend B\nend A\n"),
            {"A.B.foo"})

    def test_end_pops_only_its_own_namespace(self) -> None:
        """`end` for a `section` must not pop a namespace, or every later name is wrong."""
        body = ("namespace A\nsection S\ntheorem foo : True := trivial\nend S\n"
                "theorem bar : True := trivial\nend A\n")
        self.assertEqual(self.names(body), {"A.foo", "A.bar"})

    def test_private_declarations_are_exempt(self) -> None:
        """Module-local by construction; `check_private_shadows_public` owns that case."""
        self.assertEqual(
            self.names("namespace A\nprivate theorem foo : True := trivial\nend A\n"), set())

    def test_prose_in_comments_is_not_a_declaration(self) -> None:
        """The real false positive: `TauCeti.needs` came from the sentences
        "instance needs `CompleteSpace E`" and "lemma needs; ...". """
        body = ("namespace TauCeti\n"
                "/-- This instance needs `CompleteSpace E`, which is deliberate. -/\n"
                "-- and this lemma needs the coefficients ordered\n"
                "theorem real : True := trivial\nend TauCeti\n")
        self.assertEqual(self.names(body), {"TauCeti.real"})

    def test_block_comments_are_stripped_before_line_comments(self) -> None:
        """A docstring containing `--` must not have its closing `-/` eaten."""
        body = ("namespace A\n/-- a -- b -/\ntheorem foo : True := trivial\nend A\n")
        self.assertEqual(self.names(body), {"A.foo"})

    def test_structures_and_instances_count(self) -> None:
        body = ("namespace A\nstructure S where\n  x : Nat\n"
                "instance inst : Inhabited Nat := ⟨0⟩\nend A\n")
        self.assertEqual(self.names(body), {"A.S", "A.inst"})


class RepositoryTest(unittest.TestCase):
    def test_experimental_is_excluded(self) -> None:
        """`Experimental/` restates production names on purpose; `DK-EXPDUP` owns that."""
        for scope in dup.SCOPES:
            for path in dup.lean_files(scope):
                self.assertNotIn("Experimental", path.parts)

    def test_the_tree_is_at_or_under_its_baseline(self) -> None:
        """The ratchet. Rising means a NEW collision; falling means lower the baseline."""
        found = dup.offenders()
        self.assertLessEqual(len(found), dup.DUPLICATE_BASELINE, sorted(found))

    def test_the_baseline_is_the_known_symmetricgauge_collision_and_nothing_else(self) -> None:
        """If a finding ever appears that is NOT this pair, the baseline is hiding it."""
        for name, files in dup.offenders().items():
            self.assertTrue(all("SymmetricGauge.lean" in f for f in files),
                            f"{name} is a collision the baseline was not measured for: {files}")

    def test_it_is_wired_into_the_gate_runner(self) -> None:
        import run_gates
        self.assertIn("check_duplicate_qualified_names", {g.name for g in run_gates.gates()})


if __name__ == "__main__":
    unittest.main(verbosity=2)
