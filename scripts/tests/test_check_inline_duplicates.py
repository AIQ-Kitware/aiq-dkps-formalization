#!/usr/bin/env python3
"""Tests for `scripts/check_inline_duplicates.py`.

**The acceptance test is the point of the lane, and it is the git one.**  Eight
inline duplicates were removed by hand on 2026-07-31 under `{lane:DK-LONGPROOF-1}`
and `{lane:DK-LONGPROOF-3}`.  Their pre-fix revisions are in history, and the
script has to re-find them from those revisions.  A candidate finder that finds
nothing reads exactly like a clean tree -- the failure `check_submission_prose`
had earlier the same day -- so "it runs and reports zero" must never be able to
pass for success here.

The git test **fails** rather than skips when a pinned revision is missing.  A
skip would go green in a shallow clone and after any history rewrite, which is
precisely when someone needs to be told the acceptance evidence is gone.

Run directly: `python3 scripts/tests/test_check_inline_duplicates.py`.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_inline_duplicates as dupes  # noqa: E402


#: (revision, path, {step name -> signal that must fire}).  Every entry is a
#: duplicate that was actually removed, not a synthetic example.
GROUND_TRUTH = [
    ("b2e47c5af13ae44ef01d712d928f0f076249eb6b",
     "DavisKahan/SpectralTheory/GraphSubspace.lean",
     {
         "hRsa": "general",           # -> IsSelfAdjoint.ringInverse
         "hBsa": "general",           # -> IsSelfAdjoint.star_mul_self
         "hB'sa": "general",          # -> IsSelfAdjoint.mul_star_self
         "hnorm_sq_eq": "general",    # -> CStarRing.norm_self_mul_star
         "hPR": "repeated",           # three copies, two of them cross-theorem
         "hXR": "general",            # -> ringInverse_semiconj
     }),
    ("d4e2452ddf7eb84dfe310964a44d9f3aa8a445a9",
     "DavisKahan/Sources/DavisKahan1970/DoubleAngleTangentOperator.lean",
     {
         "htau0": "general",          # -> doubleAngleTangent_nonneg
         "htauNonneg": "general",     # -> doubleAngleTangent_nonneg
         "htanv0": "self-contained",  # -> doubleAngleTangent_nonneg
     }),
]


def at_revision(revision: str, path: str) -> str:
    return subprocess.run(["git", "show", f"{revision}:{path}"],
                          cwd=dupes.ROOT, capture_output=True, text=True,
                          check=True).stdout


class GroundTruthTest(unittest.TestCase):
    """The script must re-find every duplicate that was removed by hand."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def findings(self, revision: str, path: str) -> dict[str, list[str]]:
        try:
            source = at_revision(revision, path)
        except subprocess.CalledProcessError as exc:      # pragma: no cover
            self.fail(f"revision {revision[:8]} is not in this clone, so the acceptance "
                      f"evidence for this script cannot be checked. History was rewritten "
                      f"or the clone is shallow. Do not skip this -- re-pin it. ({exc})")
        target = self.dir / pathlib.Path(path).name
        target.write_text(source, encoding="utf-8")
        steps = dupes.steps_in(target)
        found = dupes.classify(steps, min_body=2)
        out: dict[str, list[str]] = {}
        for step in found:
            out.setdefault(step.name, []).extend(step.signals)
        return out

    def test_every_removed_duplicate_is_re_found(self) -> None:
        for revision, path, expected in GROUND_TRUTH:
            found = self.findings(revision, path)
            for name, signal in expected.items():
                self.assertIn(name, found,
                              f"{pathlib.Path(path).name}: {name} was a real duplicate "
                              f"and the script no longer flags it")
                self.assertIn(signal, found[name],
                              f"{pathlib.Path(path).name}: {name} is flagged but not by "
                              f"`{signal}`, which is the signal it was chosen to exercise")

    def test_the_third_hPR_copy_is_found(self) -> None:
        """Reading found two copies; the script found three.

        If this ever drops back to two, the `repeated` signal has narrowed and
        the argument for the script over careful reading has weakened.
        """
        revision, path, _ = GROUND_TRUTH[0]
        source = at_revision(revision, path)
        target = self.dir / "G.lean"
        target.write_text(source, encoding="utf-8")
        found = dupes.classify(dupes.steps_in(target), min_body=2)
        self.assertEqual(len([s for s in found if s.name == "hPR"]), 3)


SAMPLE = """\
theorem outer (X : T) : True := by
  set P : T := f X with hPdef
  have hgen : g (h P) = h P := by
    rw [one]
    rw [two]
  have hlocal : k hgen = 0 := by
    rw [three]
    rw [four]
  trivial
"""

SCOPING = """\
theorem outer (n : Nat) : True := by
  have first : Nat := by
    intro i
    exact i
  have second : forall i : Nat, i = i := by
    intro i
    rfl
  trivial
"""

TWINS = """\
theorem alpha (X : T) : True := by
  have h : a X = b X := by
    rw [one]
    rw [two]
  trivial

theorem beta (X : T) : True := by
  have h : a X = b X := by
    rw [three]
    rw [four]
  trivial
"""


class SignalTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def steps(self, body: str) -> dict[str, dupes.Step]:
        path = self.dir / "S.lean"
        path.write_text(body, encoding="utf-8")
        return {s.name: s for s in dupes.classify(dupes.steps_in(path), min_body=2)}

    def test_a_statement_over_a_set_binding_is_general_after_substitution(self) -> None:
        """`P` is local, but `P := f X` unfolds to globals, so the step is general."""
        self.assertIn("general", self.steps(SAMPLE)["hgen"].signals)

    def test_a_statement_naming_an_earlier_step_is_not_general(self) -> None:
        found = self.steps(SAMPLE)
        self.assertNotIn("general", found.get("hlocal", dupes.Step(
            "hlocal", "", [], "", pathlib.Path("."), 0)).signals)

    def test_an_intro_does_not_leak_out_of_its_own_step(self) -> None:
        """The bug that lost `htauNonneg`: `intro i` inside `first` must not make
        `second`'s own `i` read as a dependency on `first`."""
        self.assertIn("general", self.steps(SCOPING)["second"].signals)

    def test_identical_statements_in_two_theorems_are_repeated(self) -> None:
        self.assertIn("repeated", self.steps(TWINS)["h"].signals)

    def test_a_one_line_step_is_below_the_floor(self) -> None:
        single = "theorem t (X : T) : True := by\n  have h : a X = b X := rfl\n  trivial\n"
        path = self.dir / "S.lean"
        path.write_text(single, encoding="utf-8")
        self.assertEqual(dupes.classify(dupes.steps_in(path), min_body=2), [])

    def test_max_body_separates_duplicates_from_liftable_blocks(self) -> None:
        path = self.dir / "S.lean"
        path.write_text(SAMPLE, encoding="utf-8")
        steps = dupes.steps_in(path)
        self.assertEqual(dupes.classify(steps, min_body=2, max_body=1), [])
        self.assertTrue(dupes.classify(steps, min_body=2, max_body=99))

    def test_only_filters_to_one_signal(self) -> None:
        """`SAMPLE` has one general step and one that is not; `--only general`
        must drop the second while the unfiltered scan keeps both."""
        path = self.dir / "S.lean"
        path.write_text(SAMPLE, encoding="utf-8")
        steps = dupes.steps_in(path)
        unfiltered = {s.name for s in dupes.classify(steps, min_body=2)}
        general = {s.name for s in dupes.classify(steps, min_body=2, only="general")}
        self.assertIn("hgen", general)
        self.assertNotIn("hlocal", general)
        self.assertIn("hlocal", unfiltered)

    def test_only_repeated_drops_a_lone_statement(self) -> None:
        path = self.dir / "S.lean"
        path.write_text(SAMPLE, encoding="utf-8")
        self.assertEqual(
            dupes.classify(dupes.steps_in(path), min_body=2, only="repeated"), [])


class HelperTest(unittest.TestCase):
    def test_split_ignores_brackets(self) -> None:
        self.assertEqual(dupes.split_top_level("f (a : T) : B", ":"), ("f (a : T) ", " B"))

    def test_split_returns_none_when_absent(self) -> None:
        self.assertIsNone(dupes.split_top_level("f (a := b)", ":="))

    def test_substitution_is_transitive(self) -> None:
        binds = {"R": "Ring.inverse N", "N": "1 + star X * X"}
        self.assertIn("star X", dupes.substitute("star R = R", binds))

    def test_substitution_terminates_on_a_cycle(self) -> None:
        """A self-referential binding must not spin; it just stops."""
        dupes.substitute("a", {"a": "a + 1"}, rounds=3)


class RepositoryTest(unittest.TestCase):
    def test_every_library_has_sources(self) -> None:
        for library in dupes.LIBRARIES:
            self.assertGreater(len(dupes.lean_files(library)), 0, library)

    def test_the_library_list_is_derived_from_the_lakefile(self) -> None:
        """It was hardcoded to two of nine and nothing said so.

        Seven libraries -- 136 files -- were never scanned.  If someone adds a
        `[[lean_lib]]` this must pick it up without an edit here.
        """
        declared = {block.split('name = "')[1].split('"')[0]
                    for block in dupes.LAKEFILE.read_text(encoding="utf-8")
                                              .split("[[lean_lib]]")[1:]
                    if 'name = "' in block}
        expected = {n for n in declared
                    if (dupes.ROOT / n).is_dir() and n not in dupes.NOT_PRODUCTION}
        self.assertEqual(set(dupes.LIBRARIES), expected)
        self.assertGreater(len(dupes.LIBRARIES), 2,
                           "the hardcoded two-library list is back")

    def test_non_production_libraries_are_excluded(self) -> None:
        """`ForTauCetiRoadmap` is all `sorry`; `Challenge` is calibration."""
        for name in dupes.NOT_PRODUCTION:
            self.assertNotIn(name, dupes.LIBRARIES)

    def test_experimental_is_excluded(self) -> None:
        for library in dupes.LIBRARIES:
            for path in dupes.lean_files(library):
                self.assertNotIn("Experimental", path.parts)

    def test_it_is_not_wired_into_the_gate_runner(self) -> None:
        """Deliberate: it fires on correct code, so as a gate it would train
        everyone to ignore the suite.  If someone adds it, they must decide
        consciously and update this test and the docstring."""
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
        import run_gates
        self.assertIn("check_inline_duplicates",
                      {g.name for g in run_gates.gates()},
                      "the script should still live in scripts/ as check_*.py")
        self.assertIn("check_inline_duplicates", run_gates.ADVISORY,
                      "check_inline_duplicates must be ADVISORY: it reports candidates, "
                      "not defects, and cannot be allowed to fail the suite")


if __name__ == "__main__":
    unittest.main(verbosity=2)
