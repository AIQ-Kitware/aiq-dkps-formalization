"""Tests for `scripts/check_rw_chains.py`.

**The counting bug is the reason this script exists, so it is the first thing pinned.**
`{lane:RUB-RWCHAIN}` was posted at 63 chains against a real 53, and a later re-measurement
said 18 where the answer was 14.  Both times the cause was the same: a `rw [show P by
tac]` is ONE rewrite, but its tactic block contains commas at the same bracket depth as a
chain's separators, so a naive comma count invents entries that were never there.

`GROUND_TRUTH` below is the real instance -- `LinearPMap/Closed.lean:707`, which scored as
an eleven-lemma chain while being a single `show`.  It is pinned at a revision so that the
test keeps meaning something after the file changes, and it **fails rather than skips**
when the revision is missing: a skip goes green in a shallow clone, which is exactly when
someone needs to be told the evidence is gone.

Run directly: `python3 scripts/tests/test_check_rw_chains.py`.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_rw_chains as rw  # noqa: E402


#: (revision, path, line, what the naive count says, what it really is)
GROUND_TRUTH = ("adf714e4", "ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean", 707, 11, 1)


class CountingTest(unittest.TestCase):
    def n(self, source: str) -> int:
        chains = rw.chains_in(source)
        self.assertEqual(len(chains), 1, "fixture should hold exactly one `rw`")
        return chains[0].entries

    def test_a_plain_chain_counts_its_entries(self) -> None:
        self.assertEqual(self.n("  rw [a, b, c]\n"), 3)

    def test_a_single_rewrite_is_one(self) -> None:
        self.assertEqual(self.n("  rw [a]\n"), 1)

    def test_commas_inside_application_parens_are_not_separators(self) -> None:
        """`Summable.tsum_add (h.mul_left s) (h.div_const s)` is ONE entry."""
        self.assertEqual(self.n("  rw [f (g x) (h y), k]\n"), 2)

    def test_commas_inside_a_by_block_are_not_separators(self) -> None:
        """The bug, minimally: a tactic block's commas are not chain separators."""
        self.assertEqual(self.n("  rw [show P by ext p, constructor, simp]\n"), 1)

    def test_a_by_block_does_not_hide_earlier_entries(self) -> None:
        """Entries BEFORE the `by` still count -- the block only swallows what follows."""
        self.assertEqual(self.n("  rw [a, b, show P by tac, tac2]\n"), 3)

    def test_by_must_be_a_whole_token(self) -> None:
        """`by_cases` is not `by`; matching it would silently truncate real chains."""
        self.assertEqual(self.n("  rw [by_cases_lemma, b, c, d]\n"), 4)

    def test_nested_brackets_do_not_end_the_chain(self) -> None:
        self.assertEqual(self.n("  rw [f [a, b], c]\n"), 2)

    def test_a_term_rewrite_is_marked_as_such(self) -> None:
        self.assertTrue(rw.chains_in("  rw [show P by tac]\n")[0].is_term)
        self.assertFalse(rw.chains_in("  rw [a, b]\n")[0].is_term)


class GroundTruthTest(unittest.TestCase):
    """The real over-count, re-found from history."""

    def test_the_closed_lean_show_is_one_rewrite_not_eleven(self) -> None:
        revision, path, line, naive, real = GROUND_TRUTH
        try:
            source = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=rw.ROOT,
                                    capture_output=True, text=True, check=True).stdout
        except subprocess.CalledProcessError as exc:      # pragma: no cover
            self.fail(f"revision {revision} is not in this clone, so the evidence for the "
                      f"over-count this script exists to prevent cannot be checked. "
                      f"Re-pin it; do not skip. ({exc})")
        at = [c for c in rw.chains_in(source) if c.line == line]
        self.assertEqual(len(at), 1, f"no `rw` at {path}:{line} in {revision}")
        self.assertTrue(at[0].is_term)
        self.assertEqual(at[0].entries, real)
        self.assertGreaterEqual(1 + at[0].body.count(","), naive,
                                "the naive comma count should still be the inflated one, "
                                "otherwise this test no longer pins the bug")


class RepositoryTest(unittest.TestCase):
    def test_experimental_is_excluded(self) -> None:
        """`Experimental/` is open research, not held to the submission rubric."""
        for path in rw.lean_files("DavisKahan"):
            self.assertNotIn("Experimental", path.parts)

    def test_the_submission_library_is_at_or_under_its_documented_remainder(self) -> None:
        """`RUB-RWCHAIN` closed at three, each kept for a reason written in-source.

        A fourth appearing means someone added a chain to `ForTauCeti`, which is the
        regression this number is here to catch.
        """
        found = [c for c in
                 (c for p in rw.lean_files("ForTauCeti")
                  for c in rw.chains_in(p.read_text(errors="ignore"), p))
                 if c.entries >= 7]
        self.assertLessEqual(len(found), 3, [f"{c.path.name}:{c.line}" for c in found])

    def test_it_is_advisory_in_the_gate_runner(self) -> None:
        """A seven-lemma chain is a candidate, not a defect: three live ones are correct.
        Wired in as failing, it would train everyone to ignore the suite."""
        import run_gates
        self.assertIn("check_rw_chains", {g.name for g in run_gates.gates()})
        self.assertIn("check_rw_chains", run_gates.ADVISORY)


if __name__ == "__main__":
    unittest.main(verbosity=2)
