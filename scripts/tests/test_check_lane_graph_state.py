"""Regression tests for lane-state detection in `check_lane_graph.py`.

The defect this locks down was observed, not imagined.  On 2026-07-30
`FTC-CLM-TWINS` was printed under **READY TO TAKE** while `edward (aiq-gpu)`
held a pushed claim on it, because `HELD_RE` was anchored at the very start of
the status prose and the cell read `step (1) claimed by …`.  That is the D-DOC
collision -- two agents sent at one lane -- with the *tool* at fault rather than
the agents: the claim was pushed, visible, and correctly written, and the board
still advertised the lane as free.

Two properties are load-bearing and each has a test below.

**`unclaimed` must never read as held.**  Nine rows in `dev/LANES.md` open with
it.  A pattern that catches them would advertise nine available lanes as taken,
which is the same collision pointing the other way -- work nobody picks up.  The
`\\b` before the keyword is what guarantees this, since `unclaimed` has no word
boundary between `un` and `claimed`.

**The prefix must stay inside the first clause.**  Two live rows prove why: one
reads `slice 1 done …; slices 2 and 3 unclaimed`, and one reads
`unblocked … by jon: no lane is ever blocked on upstream acceptance`.  The
second is an *unblocking* row whose quoted policy contains the words
`blocked on`; without the colon as a clause boundary it flipped to held.  That
regression was introduced and caught while writing this fix, which is why the
colon case is pinned here rather than left to a comment.

Finally, `TERMINAL_RE` is deliberately *not* widened the same way, and no test
here asks it to be.  The directions are not symmetric: over-reporting **held**
only makes an agent ask before taking, while over-reporting **done** marks a
lane terminal and hides the work still inside it -- the failure `RUB-NS-PAPER`
documented and `E-ALIAS` then repeated.  Statuses that look terminal but do not
match are reported to a human instead, and `SuspectReportTest` covers that.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_lane_graph.py"
SPEC = importlib.util.spec_from_file_location("check_lane_graph", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


def held(prose: str) -> bool:
    return bool(M.HELD_RE.match(prose))


def suspect(prose: str) -> bool:
    return bool(M.SUSPECT_RE.match(prose))


class HeldDetectionTest(unittest.TestCase):
    """A pushed claim must register however the agent phrased it."""

    def test_the_row_that_was_actually_missed(self) -> None:
        # Verbatim shape of edward's FTC-CLM-TWINS cell on 2026-07-30.
        self.assertTrue(held("step (1) claimed by `edward (aiq-gpu)` 2026-07-30"))

    def test_slice_prefixed_claim(self) -> None:
        self.assertTrue(held("slice 2 claimed by namek, row pushed first"))

    def test_plain_claim_still_matches(self) -> None:
        self.assertTrue(held("claimed 2026-07-30 — edits not yet started"))

    def test_in_progress_and_blocked_on_still_match(self) -> None:
        self.assertTrue(held("in progress 2026-07-30"))
        self.assertTrue(held("blocked on FTT-PROMOTE"))


class UnclaimedMustStayOpenTest(unittest.TestCase):
    """The opposite collision: an open lane advertised as taken."""

    def test_unclaimed_does_not_match_claimed(self) -> None:
        self.assertFalse(held("unclaimed — 290 sites, sliceable by file"))
        self.assertFalse(held("unclaimed — measured, not started"))

    def test_semicolon_bounds_the_prefix(self) -> None:
        # `claimed` appears, but only after the first clause has ended.
        self.assertFalse(held("slice 1 done at `3e608566`; slices 2 and 3 unclaimed"))

    def test_colon_bounds_the_prefix(self) -> None:
        # An UNblocking row quoting a policy that contains "blocked on".
        self.assertFalse(
            held("unblocked 2026-07-30 by jon: **no lane is ever blocked on "
                 "upstream acceptance.**"))

    def test_em_dash_bounds_the_prefix(self) -> None:
        self.assertFalse(held("ready now — dk-failed is done, so this is takeable"))


class SuspectReportTest(unittest.TestCase):
    """Unclassifiable statuses are surfaced, never guessed at."""

    def test_a_completion_the_anchor_cannot_see_is_reported(self) -> None:
        # These read as open to TERMINAL_RE, which is correct -- the lane is not
        # finished -- but the wording deserves a human's eye.
        self.assertTrue(suspect("statement 2 done 2026-07-30 by `jon (yardrat)`"))
        self.assertTrue(suspect("step (1) done 2026-07-30 at `37e7f346`"))

    def test_a_plainly_open_status_is_not_reported(self) -> None:
        self.assertFalse(suspect("unclaimed — parallel slice, take independently"))
        self.assertFalse(suspect("ready, no prerequisite"))


class BoardStaysConsistentTest(unittest.TestCase):
    """The real file must classify without cycles or dangling prerequisites."""

    def test_check_mode_passes_on_the_live_file(self) -> None:
        self.assertEqual(M.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
