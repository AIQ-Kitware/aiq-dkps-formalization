#!/usr/bin/env python3
"""Tests for `scripts/check_experimental_coverage.py`.

The gate's value is that an `Experimental` module must be *either* reachable
from the root *or* named with a reason, and that the two kinds of reason —
"this subtree is deliberately not aggregated" and "this module does not
compile" — stay distinguishable.  These tests pin both, plus the two ways an
exception list rots: a stale name, and an exclusion that silently covers a new
module.

Run directly: `python3 scripts/tests/test_check_experimental_coverage.py`.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_experimental_coverage as gate  # noqa: E402


def write(root: pathlib.Path, rel: str, body: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")


class CoverageTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        self._saved = (gate.ROOT, gate.EXPERIMENTAL, dict(gate.EXCLUDED),
                       dict(gate.EXCLUDED_PREFIXES))
        gate.ROOT = self.root
        gate.EXPERIMENTAL = self.root / "DavisKahan/Experimental"
        gate.EXCLUDED.clear()
        gate.EXCLUDED_PREFIXES.clear()
        write(self.root, "DavisKahan/Experimental.lean",
              "import DavisKahan.Experimental.All\n")
        write(self.root, "DavisKahan/Experimental/All.lean", "")

    def tearDown(self) -> None:
        gate.ROOT, gate.EXPERIMENTAL = self._saved[0], self._saved[1]
        gate.EXCLUDED.clear(); gate.EXCLUDED.update(self._saved[2])
        gate.EXCLUDED_PREFIXES.clear(); gate.EXCLUDED_PREFIXES.update(self._saved[3])
        self._tmp.cleanup()

    def test_reachable_module_is_fine(self) -> None:
        write(self.root, "DavisKahan/Experimental/All.lean",
              "import DavisKahan.Experimental.A\n")
        write(self.root, "DavisKahan/Experimental/A.lean", "")
        self.assertEqual(gate.main(), 0)

    def test_unreachable_module_is_a_finding(self) -> None:
        write(self.root, "DavisKahan/Experimental/A.lean", "")
        self.assertEqual(gate.main(), 0)          # report mode never fails
        sys.argv = ["gate", "--check"]
        try:
            self.assertEqual(gate.main(), 1)
        finally:
            sys.argv = ["gate"]

    def test_named_exclusion_excuses_it(self) -> None:
        write(self.root, "DavisKahan/Experimental/A.lean", "")
        gate.EXCLUDED["DavisKahan.Experimental.A"] = "does not compile"
        self.assertEqual(gate.main(), 0)

    def test_prefix_exclusion_excuses_a_subtree(self) -> None:
        write(self.root, "DavisKahan/Experimental/Scratch/A.lean", "")
        write(self.root, "DavisKahan/Experimental/Scratch/B.lean", "")
        gate.EXCLUDED_PREFIXES["DavisKahan.Experimental.Scratch."] = "not aggregated"
        self.assertEqual(gate.main(), 0)

    def test_reaching_a_broken_module_is_inherited(self) -> None:
        """A module importing a broken one cannot compile, so it is excused too."""
        write(self.root, "DavisKahan/Experimental/A.lean", "")
        write(self.root, "DavisKahan/Experimental/B.lean",
              "import DavisKahan.Experimental.A\n")
        gate.EXCLUDED["DavisKahan.Experimental.A"] = "does not compile"
        self.assertEqual(gate.main(), 0)

    def test_stale_exclusion_is_reported(self) -> None:
        gate.EXCLUDED["DavisKahan.Experimental.Gone"] = "removed long ago"
        sys.argv = ["gate", "--check"]
        try:
            self.assertEqual(gate.main(), 1)
        finally:
            sys.argv = ["gate"]

    def test_transitive_reachability_counts(self) -> None:
        write(self.root, "DavisKahan/Experimental/All.lean",
              "import DavisKahan.Experimental.B\n")
        write(self.root, "DavisKahan/Experimental/B.lean",
              "import DavisKahan.Experimental.A\n")
        write(self.root, "DavisKahan/Experimental/A.lean", "")
        self.assertEqual(gate.main(), 0)


class RepositoryTest(unittest.TestCase):
    def test_the_real_tree_is_covered(self) -> None:
        self.assertEqual(gate.main(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
