#!/usr/bin/env python3
"""Tests for `scripts/run_gates.py`.

The runner's one job is to pass `--check` to the gates that accept it and not to
the ones that do not, **without a hardcoded list** -- because a hardcoded list is
the thing that goes stale, which is the defect the whole runner exists to stop
repeating.  So the tests are about classification and about what the runner does
with each class.

Run directly: `python3 scripts/tests/test_run_gates.py`.
"""

from __future__ import annotations

import io
import contextlib
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import run_gates  # noqa: E402


SOFT_GATE = '''
import argparse, sys
def main():
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    print("a finding")
    return 1 if args.check else 0
sys.exit(main())
'''

STRICT_WITH_FLAG = '''
import argparse, sys
p = argparse.ArgumentParser()
p.add_argument("--check", action="store_true")
p.parse_args()
print("clean")
sys.exit(0)
'''

STRICT_NO_FLAG = '''
import sys
print("clean")
sys.exit(0)
'''

FAILING_NO_FLAG = '''
import sys
print("a real finding")
sys.exit(1)
'''

REJECTS_UNKNOWN_FLAGS = '''
import argparse, sys
argparse.ArgumentParser().parse_args()
sys.exit(0)
'''


class ClassificationTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self._tmp.name)
        self._saved = (run_gates.ROOT, run_gates.SCRIPTS, set(run_gates.SLOW))
        run_gates.ROOT = self.dir
        run_gates.SCRIPTS = self.dir
        run_gates.SLOW.clear()
        sys.argv = ["run_gates"]

    def tearDown(self) -> None:
        run_gates.ROOT, run_gates.SCRIPTS = self._saved[0], self._saved[1]
        run_gates.SLOW.clear(); run_gates.SLOW.update(self._saved[2])
        sys.argv = ["run_gates"]
        self._tmp.cleanup()

    def write(self, name: str, body: str) -> pathlib.Path:
        path = self.dir / f"check_{name}.py"
        path.write_text(body, encoding="utf-8")
        return path

    def run_main(self, *argv: str) -> tuple[int, str]:
        sys.argv = ["run_gates", *argv]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = run_gates.main()
        return code, out.getvalue()

    def test_soft_gate_is_recognised(self) -> None:
        gate = run_gates.Gate(self.write("soft", SOFT_GATE))
        self.assertTrue(gate.soft)
        self.assertTrue(gate.takes_check)
        self.assertIn("--check", gate.command())

    def test_strict_with_flag_is_recognised(self) -> None:
        gate = run_gates.Gate(self.write("strictflag", STRICT_WITH_FLAG))
        self.assertFalse(gate.soft)
        self.assertTrue(gate.takes_check)
        self.assertIn("--check", gate.command())

    def test_strict_without_flag_gets_no_flag(self) -> None:
        """The whole point: passing --check here would be `unrecognized arguments`."""
        gate = run_gates.Gate(self.write("noflag", STRICT_NO_FLAG))
        self.assertFalse(gate.takes_check)
        self.assertNotIn("--check", gate.command())

    def test_a_soft_gate_with_a_finding_fails_the_run(self) -> None:
        """Without the runner this gate exits 0 and the finding is invisible."""
        self.write("soft", SOFT_GATE)
        code, output = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("a finding", output)

    def test_a_gate_that_rejects_unknown_flags_is_not_given_one(self) -> None:
        self.write("picky", REJECTS_UNKNOWN_FLAGS)
        code, _ = self.run_main()
        self.assertEqual(code, 0)

    def test_a_failing_gate_fails_the_run(self) -> None:
        self.write("bad", FAILING_NO_FLAG)
        self.write("good", STRICT_NO_FLAG)
        code, output = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("check_bad", output)

    def test_all_clean_passes(self) -> None:
        self.write("a", STRICT_NO_FLAG)
        self.write("b", STRICT_WITH_FLAG)
        code, output = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("gates: OK", output)

    def test_fast_skips_slow_gates_and_says_so(self) -> None:
        """A green --fast run must never read as a green run."""
        self.write("slowone", FAILING_NO_FLAG)
        run_gates.SLOW.add("check_slowone")
        code, output = self.run_main("--fast")
        self.assertEqual(code, 0)
        self.assertIn("SKIPPED", output)
        self.assertIn("not a green run", output)

    def test_an_advisory_finding_is_shown_but_does_not_fail_the_run(self) -> None:
        """The distinction `check_merge_losses` forced: reported, never fatal."""
        self.write("noisy", FAILING_NO_FLAG)
        run_gates.ADVISORY["check_noisy"] = "fires on ordinary activity"
        try:
            code, output = self.run_main()
        finally:
            run_gates.ADVISORY.pop("check_noisy", None)
        self.assertEqual(code, 0)
        self.assertIn("NOTE", output)
        self.assertIn("a real finding", output)      # still shown
        self.assertIn("gates: OK", output)

    def test_filter_selects_a_subset(self) -> None:
        self.write("alpha", FAILING_NO_FLAG)
        self.write("beta", STRICT_NO_FLAG)
        code, _ = self.run_main("-k", "beta")
        self.assertEqual(code, 0)

    def test_list_runs_nothing_and_counts_the_classes(self) -> None:
        self.write("soft", SOFT_GATE)
        self.write("noflag", FAILING_NO_FLAG)      # would fail if it were run
        code, output = self.run_main("--list")
        self.assertEqual(code, 0)
        self.assertIn("1 soft", output)


class RepositoryTest(unittest.TestCase):
    def test_every_real_gate_classifies(self) -> None:
        """No repository gate falls outside the four classes."""
        real = run_gates.gates()
        self.assertGreater(len(real), 20)
        for gate in real:
            self.assertIn(gate.kind, {
                "advisory (reported, cannot fail the run)",
                "strict, --check withheld (it is a completion target)",
                "soft (strict only with --check)",
                "strict, accepts --check",
                "strict, no flag",
            })

    def test_check_is_stronger_list_names_gates_that_exist(self) -> None:
        names = {gate.name for gate in run_gates.gates()}
        for withheld in run_gates.CHECK_IS_STRONGER:
            self.assertIn(withheld, names,
                          f"CHECK_IS_STRONGER names a gate that does not exist: {withheld}")

    def test_a_gate_with_a_stronger_check_is_not_given_the_flag(self) -> None:
        """Accepting `--check` does not tell you what `--check` means."""
        gates = {g.name: g for g in run_gates.gates()}
        for name in run_gates.CHECK_IS_STRONGER:
            self.assertNotIn("--check", gates[name].command())

    def test_advisory_list_names_gates_that_exist(self) -> None:
        """Same stale-name hazard as SLOW: an advisory exemption for a gate that
        no longer exists would silently exempt the next gate to take that name."""
        names = {gate.name for gate in run_gates.gates()}
        for advisory in run_gates.ADVISORY:
            self.assertIn(advisory, names,
                          f"ADVISORY names a gate that does not exist: {advisory}")

    def test_slow_list_names_gates_that_exist(self) -> None:
        """A stale name here would silently stop skipping something."""
        names = {gate.name for gate in run_gates.gates()}
        for slow in run_gates.SLOW:
            self.assertIn(slow, names, f"SLOW names a gate that does not exist: {slow}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
