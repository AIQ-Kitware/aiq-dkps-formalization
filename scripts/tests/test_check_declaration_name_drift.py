#!/usr/bin/env python3
"""Standard-library tests for scripts/check_declaration_name_drift.py.

The interesting behaviour is name *resolution*: computing the fully-qualified
name of a declaration from the surrounding `namespace`/`section`/`end`
structure. Two regressions are pinned here because both silently produced wrong
names rather than errors:

* a bare `end` closing a `section` must not pop a `namespace`;
* the `end` / `namespace` / `section` patterns must not span newlines --
  matching `\\s*$` under `re.MULTILINE` lets `end` on one line and `section` on
  the next parse as a single `end section`, unbalancing the whole file.
"""
from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_declaration_name_drift.py"
SPEC = importlib.util.spec_from_file_location("check_declaration_name_drift", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


def decls(text: str) -> set[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as handle:
        handle.write(text)
        path = handle.name
    try:
        return M.declarations_in(path)
    finally:
        Path(path).unlink()


class QualifiedNameTest(unittest.TestCase):
    def test_plain_namespace(self) -> None:
        self.assertEqual(
            decls("namespace Foo\ntheorem bar : True := trivial\nend Foo\n"),
            {"Foo.bar"},
        )

    def test_nested_namespace(self) -> None:
        self.assertEqual(
            decls(
                "namespace Foo\nnamespace Baz\nlemma bar : True := trivial\n"
                "end Baz\nend Foo\n"
            ),
            {"Foo.Baz.bar"},
        )

    def test_dotted_namespace(self) -> None:
        self.assertEqual(
            decls("namespace Foo.Baz\ntheorem bar : True := trivial\nend Foo.Baz\n"),
            {"Foo.Baz.bar"},
        )

    def test_root_escape(self) -> None:
        self.assertEqual(
            decls("namespace Foo\ntheorem _root_.qux : True := trivial\nend Foo\n"),
            {"qux"},
        )

    def test_declaration_after_reopened_namespace(self) -> None:
        text = (
            "namespace Foo\n"
            "namespace Inner\n"
            "theorem a : True := trivial\n"
            "end Inner\n"
            "namespace Other\n"
            "theorem b : True := trivial\n"
            "end Other\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.Inner.a", "Foo.Other.b"})


class SectionRegressionTest(unittest.TestCase):
    """A bare `end` closing a `section` must not pop the enclosing namespace."""

    def test_anonymous_section_inside_namespace(self) -> None:
        text = (
            "namespace Foo\n"
            "section\n"
            "theorem a : True := trivial\n"
            "end\n"
            "theorem b : True := trivial\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.a", "Foo.b"})

    def test_named_section_inside_namespace(self) -> None:
        text = (
            "namespace Foo\n"
            "section Support\n"
            "theorem a : True := trivial\n"
            "end Support\n"
            "namespace Bar\n"
            "theorem b : True := trivial\n"
            "end Bar\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.a", "Foo.Bar.b"})

    def test_decorated_section_forms(self) -> None:
        text = (
            "namespace Foo\n"
            "@[expose] public section\n"
            "noncomputable section\n"
            "theorem a : True := trivial\n"
            "end\n"
            "end\n"
            "theorem b : True := trivial\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.a", "Foo.b"})


class NewlineSpanRegressionTest(unittest.TestCase):
    """`end` followed by a blank line and `section` are two separate events."""

    def test_end_then_blank_then_section(self) -> None:
        text = (
            "namespace Foo\n"
            "section\n"
            "theorem a : True := trivial\n"
            "end\n"
            "\n"
            "section\n"
            "theorem b : True := trivial\n"
            "end\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.a", "Foo.b"})

    def test_namespace_name_must_be_on_the_same_line(self) -> None:
        # `namespace` with the name on the next line is not valid Lean; the
        # point is that the regex must not silently accept and mis-parse it.
        text = "namespace\nFoo\ntheorem a : True := trivial\n"
        self.assertEqual(decls(text), {"a"})


class ModifierTest(unittest.TestCase):
    def test_attributes_and_modifiers(self) -> None:
        text = (
            "namespace Foo\n"
            "@[simp]\n"
            "theorem a : True := trivial\n"
            "@[simp] noncomputable def b : Nat := 0\n"
            "private theorem c : True := trivial\n"
            "protected lemma d : True := trivial\n"
            "end Foo\n"
        )
        self.assertEqual(decls(text), {"Foo.a", "Foo.b", "Foo.c", "Foo.d"})

    def test_alias_is_a_declaration(self) -> None:
        self.assertEqual(
            decls("namespace Foo\nalias bar := baz\nend Foo\n"), {"Foo.bar"}
        )


class PrintAxiomsTest(unittest.TestCase):
    def test_extracts_targets(self) -> None:
        text = "#print axioms Foo.bar\n#print axioms Foo.Baz.qux\n"
        self.assertEqual(
            set(M.PRINT_AXIOMS_RE.findall(text)), {"Foo.bar", "Foo.Baz.qux"}
        )

    def test_does_not_span_lines(self) -> None:
        self.assertEqual(M.PRINT_AXIOMS_RE.findall("#print axioms\nFoo.bar\n"), [])


if __name__ == "__main__":
    unittest.main()
