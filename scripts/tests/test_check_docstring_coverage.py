"""Regression tests for `scripts/check_docstring_coverage.py`.

Every case here pins a shape that has actually broken a Lean-parsing scanner in
this repository.  The gate's own header records three of them; the fourth cost
the most, because unlike the others it produced a **green** result:

* an **inline attribute** -- `@[simp] theorem foo ...` on one line -- must be
  seen.  Anchoring the keyword after *modifiers* alone (an attribute bracket is
  not a modifier) made the scanner skip such lines entirely rather than report
  them, and it reported `OK` over 158 undocumented declarations across 59 files.
  That is the dominant declaration style here, so the blind spot covered a large
  fraction of the surface;
* **block-comment depth** must be tracked, so module-docstring prose whose
  wrapping puts `theorem` or `lemma` at the start of a line is not mistaken for a
  declaration.  Ignoring this inflated a published `ForTauCeti` figure roughly
  twofold;
* an **anonymous instance** has no name, so a scan keyed on names drops it
  silently;
* lines that may sit *between* a docstring and the declaration it documents --
  `@[...]`, `omit`, `set_option`, `open`, `variable`, `attribute` -- must be
  skipped by the look-back, or a documented declaration is reported undocumented.
"""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_docstring_coverage.py"
SPEC = importlib.util.spec_from_file_location("check_docstring_coverage", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


def findings(text: str) -> list[dict]:
    """Run the scanner over `text` and return its findings."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        return M.scan(path, "Test.lean")
    finally:
        path.unlink()


def names(text: str) -> set[str]:
    return {f["name"] for f in findings(text)}


class InlineAttributeTest(unittest.TestCase):
    """The defect that reported OK over 158 declarations."""

    def test_inline_attribute_undocumented_is_reported(self) -> None:
        self.assertEqual(names("@[simp] theorem foo : True := trivial\n"), {"foo"})

    def test_inline_attribute_documented_is_not_reported(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\n@[simp] theorem foo : True := trivial\n"), set())

    def test_multiple_attributes_in_one_bracket(self) -> None:
        self.assertEqual(
            names("@[simp, norm_cast] theorem foo : True := trivial\n"), {"foo"})

    def test_attribute_then_modifier(self) -> None:
        self.assertEqual(
            names("@[simp] noncomputable def foo : Nat := 0\n"), {"foo"})

    def test_inline_attribute_on_private_is_not_reported(self) -> None:
        self.assertEqual(
            names("@[simp] private theorem foo : True := trivial\n"), set())


class BlockCommentTest(unittest.TestCase):
    """Prose inside a comment is not a declaration."""

    def test_prose_beginning_with_keyword_is_not_a_declaration(self) -> None:
        self.assertEqual(
            names("/-!\n# Title\n\nThe main\nlemma compares two things.\n-/\n"),
            set())

    def test_declaration_after_module_docstring_is_seen(self) -> None:
        self.assertEqual(
            names("/-!\n# Title\n-/\n\ntheorem foo : True := trivial\n"), {"foo"})


class AnonymousInstanceTest(unittest.TestCase):
    def test_anonymous_instance_is_reported(self) -> None:
        self.assertEqual(names("instance : Inhabited Nat := ⟨0⟩\n"), {"<anonymous>"})

    def test_documented_anonymous_instance_is_not_reported(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\ninstance : Inhabited Nat := ⟨0⟩\n"), set())


class LookBackTest(unittest.TestCase):
    """Lines allowed between a docstring and the declaration it documents."""

    def test_omit_line_between_docstring_and_declaration(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\nomit [Foo] in\ntheorem bar : True := trivial\n"),
            set())

    def test_attribute_line_between_docstring_and_declaration(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\n@[simp]\ntheorem bar : True := trivial\n"), set())

    def test_blank_line_between_docstring_and_declaration(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\n\ntheorem bar : True := trivial\n"), set())

    def test_unrelated_code_between_does_not_count_as_documentation(self) -> None:
        self.assertEqual(
            names("/-- Doc. -/\ntheorem a : True := trivial\ntheorem b : True := trivial\n"),
            {"b"},
        )


if __name__ == "__main__":
    unittest.main()
