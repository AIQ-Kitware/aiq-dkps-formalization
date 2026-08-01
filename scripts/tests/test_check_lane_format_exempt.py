"""Tests for the markerless-row exemption in `check_lane_format.py`.

The ratchet's own comment says *"the number may only fall"*, and until 2026-08-01
the checker made that impossible to obey.  Its state check prescribes a remedy --
*"Drop the `{lane:}` marker from the superseded ROW"* -- and carrying that remedy
out converts a marked row into a markerless one, so **clearing a fatal finding
raised the ratchet**.  Twenty-two rows arrived that way in one merge.

The exemption resolves it on the check's own stated rationale: markerless rows
matter because *"a second agent will take work you are already doing"*, and
nobody claims a lane that is already finished.  So a markerless row naming a
lane that is TERMINAL elsewhere is exempt; a markerless row naming an open lane,
or naming no lane at all, still counts.

That distinction is the whole of the feature, and both directions are pinned
below.  The exemption is also *reported* rather than applied silently -- a
suppression nobody can see is indistinguishable from a check that stopped
looking, which is the failure `check_submission_prose` had on 2026-07-31.

Run directly: `python3 scripts/tests/test_check_lane_format_exempt.py`.
"""

from __future__ import annotations

import io
import contextlib
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_lane_format as fmt  # noqa: E402


#: Five content columns: the checker splits on unescaped `|` and requires 7 parts.
HEADER = (
    "| who | files | needs | date | status |\n"
    "|---|---|---|---|---|\n"
)


def row(owner: str, status: str) -> str:
    return f"| {owner} | files | needs | 2026-08-01 | {status} |\n"


class ExemptionTest(unittest.TestCase):
    """A superseded claim row is exempt; a live one is not."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)
        self._real = fmt.LANES
        self._baseline = fmt.MARKERLESS_BASELINE
        fmt.MARKERLESS_BASELINE = 0

    def tearDown(self) -> None:
        fmt.LANES = self._real
        fmt.MARKERLESS_BASELINE = self._baseline
        self._tmp.cleanup()

    def run_on(self, body: str) -> tuple[int, str]:
        path = self.dir / "LANES.md"
        path.write_text(HEADER + body, encoding="utf-8")
        fmt.LANES = path
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = fmt.main(["--check"])
        return code, out.getvalue()

    def test_a_superseded_claim_row_is_exempt(self) -> None:
        """The remedy the state check prescribes must not raise the ratchet."""
        body = (row("agent -- lane FOO, CLAIMED.", "**claimed**")
                + row("agent -- lane FOO, DONE.", "**done** `{lane:FOO}`"))
        code, text = self.run_on(body)
        self.assertIn("1 markerless row(s) exempted", text)
        self.assertEqual(code, 0, text)

    def test_a_claim_on_an_open_lane_still_counts(self) -> None:
        """The collision this check exists to prevent is still reported."""
        body = row("agent -- lane BAR, CLAIMED.", "**claimed**")
        code, text = self.run_on(body)
        self.assertIn("markerless claim/completion rows", text)
        self.assertEqual(code, 1, text)

    def test_a_claim_on_a_merely_held_lane_still_counts(self) -> None:
        """`held` is not `terminal`; someone can still collide with it."""
        body = (row("agent -- lane BAZ, CLAIMED.", "**claimed**")
                + row("other -- lane BAZ, CLAIMED.", "**claimed** `{lane:BAZ}`"))
        code, text = self.run_on(body)
        self.assertIn("markerless claim/completion rows", text)
        self.assertEqual(code, 1, text)

    def test_a_row_naming_no_lane_still_counts(self) -> None:
        """No lane named means nothing to exempt it against."""
        body = row("agent -- CLAIMED, but says no lane name.", "**claimed**")
        code, text = self.run_on(body)
        self.assertIn("markerless claim/completion rows", text)
        self.assertEqual(code, 1, text)

    def test_the_exemption_is_reported_not_silent(self) -> None:
        """A suppression nobody can see reads like a check that stopped looking."""
        body = (row("agent -- lane FOO, CLAIMED.", "**claimed**")
                + row("agent -- lane FOO, DONE.", "**done** `{lane:FOO}`"))
        _, text = self.run_on(body)
        self.assertIn("exempted", text)
        self.assertIn("terminal elsewhere", text)


class MarkerOrderTest(ExemptionTest):
    """The row's OWN marker must come first in its status cell."""

    def test_own_marker_after_a_referenced_one_is_fatal(self) -> None:
        """The exact bug, reproduced: a DONE row for FOO that mentions BAR first
        registers as BAR, marks BAR terminal, and leaves FOO advertised as READY."""
        body = row("agent -- lane FOO, DONE.",
                   "**done** see also `{lane:BAR}` -- and `{lane:FOO}`")
        code, text = self.run_on(body)
        self.assertIn("owner cell says lane FOO", text)
        self.assertIn("FIRST marker is {lane:BAR}", text)
        self.assertEqual(code, 1, text)

    def test_referencing_other_lanes_after_your_own_is_fine(self) -> None:
        """28 live rows do this; it is the convention, not a defect."""
        body = row("agent -- lane FOO, DONE.",
                   "**done** `{lane:FOO}` -- supersedes `{lane:BAR}` and `{lane:BAZ}`")
        code, text = self.run_on(body)
        self.assertNotIn("FIRST marker", text)
        self.assertEqual(code, 0, text)

    def test_a_row_that_never_marks_its_own_lane_is_not_flagged_here(self) -> None:
        """A posting row may register a lane it does not own; that is the markerless
        check's business, not this one, and double-reporting would be noise."""
        body = row("agent -- lane FOO, DONE.", "**done** `{lane:BAR}`")
        _, text = self.run_on(body)
        self.assertNotIn("FIRST marker", text)


class LiveBoardTest(unittest.TestCase):
    def test_the_real_board_is_at_or_under_its_baseline(self) -> None:
        """The ratchet is the point; this fails when someone adds a bare row."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = fmt.main(["--check"])
        self.assertEqual(code, 0, out.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=2)
