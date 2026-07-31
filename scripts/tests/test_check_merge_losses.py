#!/usr/bin/env python3
"""Tests for `scripts/check_merge_losses.py`.

Each test builds a real throwaway git repository with a real merge, because the
thing under test is a claim about `git rev-parse <merge>^@` and about which side
of a conflict resolution survived.  Mocking git would test the mock.

Run directly: `python3 scripts/tests/test_check_merge_losses.py`.
"""

from __future__ import annotations

import contextlib
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_merge_losses as gate  # noqa: E402


def git(*args: str) -> str:
    return subprocess.run(("git",) + args, capture_output=True, text=True,
                          check=False).stdout


@contextlib.contextmanager
def repository():
    """A throwaway git repository as the working directory.

    The `chdir` back is in a `finally` deliberately: without it a single failing
    assertion leaves every later test running inside a deleted directory, and
    six tests report five cascading errors that say nothing about the code.
    """
    previous = os.getcwd()
    with tempfile.TemporaryDirectory() as directory:
        try:
            os.chdir(directory)
            git("init", "-q", "-b", "main")
            git("config", "user.email", "t@t"); git("config", "user.name", "t")
            yield pathlib.Path(directory)
        finally:
            os.chdir(previous)


def commit(path: str, body: str, message: str) -> None:
    target = pathlib.Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(body, encoding="utf-8")
    git("add", "-A")
    git("commit", "-q", "-m", message)


class MergeLossTest(unittest.TestCase):
    def setUp(self) -> None:
        gate.declarations_at.cache_clear()
        sys.argv = ["gate", "--ref", "main"]

    def tearDown(self) -> None:
        gate.declarations_at.cache_clear()
        sys.argv = ["gate"]

    def test_a_clean_merge_reports_nothing(self) -> None:
        with repository():
            commit("A.lean", "theorem base : True := trivial\n", "base")
            git("checkout", "-q", "-b", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem side_only : True := trivial\n", "side")
            git("checkout", "-q", "main")
            commit("B.lean", "theorem main_only : True := trivial\n", "main")
            git("merge", "-q", "--no-edit", "side")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 0)

    def test_a_side_dropped_at_the_merge_is_reported(self) -> None:
        """The failure this exists for: resolve by taking one side wholesale."""
        with repository():
            commit("A.lean", "theorem base : True := trivial\n", "base")
            git("checkout", "-q", "-b", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem only_on_side : True := trivial\n", "side")
            git("checkout", "-q", "main")
            commit("A.lean", "theorem base : True := trivial\ntheorem only_on_main : True := trivial\n", "main")
            git("merge", "--no-edit", "-q", "-X", "ours", "side")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 1)

    def test_a_restored_declaration_is_not_a_finding(self) -> None:
        """Dropped at the merge, added back afterwards -- HEAD is what matters."""
        with repository():
            commit("A.lean", "theorem base : True := trivial\n", "base")
            git("checkout", "-q", "-b", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem only_on_side : True := trivial\n", "side")
            git("checkout", "-q", "main")
            commit("A.lean", "theorem base : True := trivial\ntheorem only_on_main : True := trivial\n", "main")
            git("merge", "--no-edit", "-q", "-X", "ours", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem only_on_main : True := trivial\n"
                             "theorem only_on_side : True := trivial\n", "restore")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 0)

    def test_modifiers_do_not_hide_a_declaration(self) -> None:
        """A missed modifier would make a surviving declaration read as lost."""
        with repository():
            commit("A.lean",
                   "@[simp]\nprivate theorem decorated : True := trivial\n"
                   "noncomputable def slow : Nat := 0\n", "base")
            names = gate.declarations_at("HEAD")
            self.assertIn("decorated", names)
            self.assertIn("slow", names)

    def test_a_rename_on_one_side_reads_as_a_loss_by_design(self) -> None:
        """Documented trade-off, pinned so nobody 'fixes' it into a body diff.

        The shape that actually occurs: a branch renames a declaration, the
        other branch does not, and the merge keeps the new name.  The old name
        was present in one parent and is absent from the result, so it is
        reported -- correctly, on the gate's own terms, and harmlessly, because
        a human reading the list sees the successor immediately.
        """
        with repository():
            commit("A.lean", "theorem old_name : True := trivial\n", "base")
            git("checkout", "-q", "-b", "side")
            commit("A.lean", "theorem new_name : True := trivial\n", "rename on the side branch")
            git("checkout", "-q", "main")
            commit("B.lean", "theorem elsewhere : True := trivial\n", "unrelated work on main")
            git("merge", "--no-edit", "-q", "side")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 1)

    def test_a_rename_after_a_merge_is_not_reported(self) -> None:
        """The complement, and the reason the gate is narrower than it sounds.

        Only what a *merge* dropped is in scope.  An ordinary rename in an
        ordinary commit is invisible here, which keeps the list to the size a
        human will actually adjudicate.
        """
        with repository():
            commit("A.lean", "theorem base : True := trivial\n", "base")
            git("checkout", "-q", "-b", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem old_name : True := trivial\n", "side")
            git("checkout", "-q", "main")
            commit("B.lean", "theorem elsewhere : True := trivial\n", "main")
            git("merge", "--no-edit", "-q", "side")
            commit("A.lean", "theorem base : True := trivial\ntheorem new_name : True := trivial\n", "rename")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 0)

    def test_no_merges_is_not_a_finding(self) -> None:
        with repository():
            commit("A.lean", "theorem base : True := trivial\n", "base")
            sys.argv = ["gate", "--ref", "main", "--check"]
            self.assertEqual(gate.main(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
