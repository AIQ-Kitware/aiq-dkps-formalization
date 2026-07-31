#!/usr/bin/env python3
"""Tests for `scripts/check_private_shadows_public.py`.

The gate's whole value is that it distinguishes a `private` copy of an imported
declaration from a `private` helper that happens to exist.  These tests pin that
distinction, the transitivity of the import closure, and the two failure modes
the baseline is for.

Run directly: `python3 scripts/tests/test_check_private_shadows_public.py`.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_private_shadows_public as gate  # noqa: E402


def write(root: pathlib.Path, rel: str, body: str) -> pathlib.Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


class ScanTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        self._saved = gate.ROOT
        gate.ROOT = self.root

    def tearDown(self) -> None:
        gate.ROOT = self._saved
        self._tmp.cleanup()

    def scan(self, *paths: pathlib.Path) -> list[tuple[str, list[str]]]:
        return gate.scan(list(paths))

    def test_private_copy_of_direct_import_is_reported(self) -> None:
        base = write(self.root, "L/Base.lean", "theorem foo : True := trivial\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Base\nprivate theorem foo : True := trivial\n",
        )
        self.assertEqual(self.scan(base, user), [("L/User.lean", ["foo"])])

    def test_private_helper_with_a_fresh_name_is_not_reported(self) -> None:
        base = write(self.root, "L/Base.lean", "theorem foo : True := trivial\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Base\nprivate theorem helper : True := trivial\n",
        )
        self.assertEqual(self.scan(base, user), [])

    def test_a_prime_hides_the_copy(self) -> None:
        """Documented limitation, pinned so it cannot change silently."""
        base = write(self.root, "L/Base.lean", "theorem foo : True := trivial\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Base\nprivate theorem foo' : True := trivial\n",
        )
        self.assertEqual(self.scan(base, user), [])

    def test_closure_is_transitive(self) -> None:
        base = write(self.root, "L/Base.lean", "theorem foo : True := trivial\n")
        mid = write(self.root, "L/Mid.lean", "import L.Base\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Mid\nprivate theorem foo : True := trivial\n",
        )
        self.assertEqual(self.scan(base, mid, user), [("L/User.lean", ["foo"])])

    def test_unimported_module_does_not_count(self) -> None:
        other = write(self.root, "L/Other.lean", "theorem foo : True := trivial\n")
        user = write(self.root, "L/User.lean", "private theorem foo : True := trivial\n")
        self.assertEqual(self.scan(other, user), [])

    def test_a_private_name_is_not_public_in_its_own_module(self) -> None:
        """A module's own `private` name must not make a downstream copy look fine."""
        base = write(self.root, "L/Base.lean", "private theorem foo : True := trivial\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Base\nprivate theorem foo : True := trivial\n",
        )
        self.assertEqual(self.scan(base, user), [])

    def test_instances_count_as_public(self) -> None:
        base = write(self.root, "L/Base.lean", "instance foo : Inhabited Nat := ⟨0⟩\n")
        user = write(
            self.root,
            "L/User.lean",
            "import L.Base\nprivate def foo : Nat := 0\n",
        )
        self.assertEqual(self.scan(base, user), [("L/User.lean", ["foo"])])

    def test_public_import_syntax_is_followed(self) -> None:
        base = write(self.root, "L/Base.lean", "theorem foo : True := trivial\n")
        user = write(
            self.root,
            "L/User.lean",
            "public import L.Base\nprivate theorem foo : True := trivial\n",
        )
        self.assertEqual(self.scan(base, user), [("L/User.lean", ["foo"])])


class RepositoryTest(unittest.TestCase):
    def test_the_real_tree_is_at_its_baseline(self) -> None:
        self.assertEqual(gate.main(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
