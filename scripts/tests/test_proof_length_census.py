#!/usr/bin/env python3
"""Tests for `scripts/proof_length_census.py`.

Two things need pinning.  The **length** measure is offered as authoritative, so
it is tested against hand-counted fixtures.  The **scaffolding** measure is
offered as parameterized precisely because it could not be reproduced, so what is
tested there is the sensitivity itself: the same proof must land in different
buckets under different definitions, because a reader of a single percentage
would never guess that.

Run directly: `python3 scripts/tests/test_proof_length_census.py`.
"""

from __future__ import annotations

import pathlib
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import proof_length_census as census  # noqa: E402


SIMPLE = """\
theorem short_one : True := by
  trivial

theorem long_one (h : True) : True := by
  have a := h
  have b := h
  have c := h
  exact h
"""

SCAFFOLD_HEAVY = """\
theorem bound (h : True) : True := by
  set x := 1 with hx
  let y := 2
  obtain ⟨u, v⟩ := And.intro h h
  exact h
"""

MULTILINE_SET = """\
theorem wide (h : True) : True := by
  set x := (1 : Nat)
      + 2
      + 3 with hx
  exact h
"""


class LengthTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)
        census.SCAFFOLD = re.compile(census.SCAFFOLD_DEFNS["published"])

    def tearDown(self) -> None:
        census.SCAFFOLD = re.compile(census.SCAFFOLD_DEFNS["published"])
        self._tmp.cleanup()

    def write(self, body: str) -> pathlib.Path:
        path = self.dir / "F.lean"
        path.write_text(body, encoding="utf-8")
        return path

    def by_name(self, body: str) -> dict[str, census.Proof]:
        return {p.name: p for p in census.proofs_in(self.write(body))}

    def test_both_proofs_are_found(self) -> None:
        found = self.by_name(SIMPLE)
        self.assertIn("short_one", found)
        self.assertIn("long_one", found)

    def test_length_counts_the_body_not_the_signature(self) -> None:
        """`long_one`'s body is four tactic lines; its signature is not part of it."""
        self.assertEqual(self.by_name(SIMPLE)["long_one"].length, 4)

    def test_a_one_line_proof_is_one_line(self) -> None:
        self.assertEqual(self.by_name(SIMPLE)["short_one"].length, 1)

    def test_scaffolding_is_counted(self) -> None:
        proof = self.by_name(SCAFFOLD_HEAVY)["bound"]
        self.assertEqual(proof.length, 4)
        self.assertEqual(proof.scaffold_lines, 3)      # set, let, obtain
        self.assertEqual(proof.scaffold_percent, 75)

    def test_a_multiline_binding_counts_every_line(self) -> None:
        """The continuation rule: a `set` running to four lines is four lines."""
        proof = self.by_name(MULTILINE_SET)["wide"]
        self.assertGreater(proof.scaffold_lines, 1)

    def test_have_is_not_scaffolding_under_the_published_definition(self) -> None:
        """`long_one` is three `have`s and an `exact`; the published rule sees none."""
        self.assertEqual(self.by_name(SIMPLE)["long_one"].scaffold_lines, 0)

    def test_the_definition_changes_the_answer(self) -> None:
        """The finding the script exists to make visible, pinned as behaviour.

        The same proof must move between buckets as the definition changes.  If
        this test ever passes trivially -- all definitions agreeing -- then the
        parameterization is pointless and the docstring's argument is wrong.
        """
        path = self.write(SIMPLE)
        percentages = set()
        for name, pattern in census.SCAFFOLD_DEFNS.items():
            census.SCAFFOLD = re.compile(pattern)
            proof = {p.name: p for p in census.proofs_in(path)}["long_one"]
            percentages.add(proof.scaffold_percent)
        self.assertGreater(len(percentages), 1,
                           "every definition agrees -- the sensitivity finding is gone")

    def test_experimental_is_excluded(self) -> None:
        self.assertNotIn("Experimental", str(census.ROOT))


NESTED = """\
theorem chained (h : True) : True := by
  have free : True := by
    have standalone := trivial
    exact standalone
  have a : True := h
  have b : True := by
    have inner := a
    exact inner
  have c : True := by
    have inner2 := a
    have inner3 := b
    exact inner2
  exact h
"""


class ExtractionCostTest(unittest.TestCase):
    """The metric that decides refactorability, as against the scaffolding split.

    A step referencing `k` earlier local names needs `k` extra arguments to lift
    into a standalone lemma.  A proof can be 2% scaffolding and still resist
    extraction because every step names several earlier ones -- which is the
    finding this metric exists to make measurable.
    """

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)
        census.SCAFFOLD = re.compile(census.SCAFFOLD_DEFNS["published"])

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def proof(self, body: str, name: str):
        path = self.dir / "F.lean"
        path.write_text(body, encoding="utf-8")
        return {p.name: p for p in census.proofs_in(path)}[name]

    def test_a_step_using_no_earlier_name_costs_nothing(self) -> None:
        """The rare free lunch: these are the ones that actually lift."""
        costs = census.extraction_cost(self.proof(NESTED, "chained"))
        self.assertIn(0, costs)

    def test_a_step_using_earlier_names_costs_them(self) -> None:
        costs = census.extraction_cost(self.proof(NESTED, "chained"))
        self.assertTrue(any(c >= 1 for c in costs),
                        "no step was charged for the earlier `have`s it uses")

    def test_one_line_steps_are_not_counted(self) -> None:
        """Only multi-line steps are extraction candidates at all."""
        single = "theorem t (h : True) : True := by\n  have a : True := h\n  exact a\n"
        self.assertEqual(census.extraction_cost(self.proof(single, "t")), [])


class RepositoryTest(unittest.TestCase):
    def setUp(self) -> None:
        census.SCAFFOLD = re.compile(census.SCAFFOLD_DEFNS["published"])

    def test_the_length_census_runs_over_both_libraries(self) -> None:
        for library in ("ForTauCeti", "DavisKahan"):
            found = census.census(library)
            self.assertGreater(len(found), 100, library)

    def test_the_long_proofs_are_not_cheaply_extractable(self) -> None:
        """Pins the DK-LONGPROOF finding: low scaffolding does not mean liftable.

        If this ever drops to a median of 0, the long proofs really have become
        chains of independent steps and the campaign should be re-sized upward.
        """
        import statistics
        costs = [c for p in census.census("DavisKahan") if p.length > 150
                 for c in census.extraction_cost(p)]
        self.assertGreater(len(costs), 100)
        self.assertGreater(statistics.median(costs), 0,
                           "long-proof steps no longer reference earlier locals -- re-size")

    def test_davis_kahan_has_the_long_proofs(self) -> None:
        """The finding `{lane:DK-LONGPROOF}` was posted on, pinned so a later
        refactor that closes it makes this test fail and be updated."""
        for_tau_ceti = [p for p in census.census("ForTauCeti") if p.length > 150]
        davis_kahan = [p for p in census.census("DavisKahan") if p.length > 150]
        self.assertGreater(len(davis_kahan), len(for_tau_ceti),
                           "DavisKahan no longer holds more long proofs -- re-read DK-LONGPROOF")


if __name__ == "__main__":
    unittest.main(verbosity=2)
