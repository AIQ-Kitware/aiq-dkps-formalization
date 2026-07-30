"""Regression tests for `audit_scan.py --defn`, the definitional-escape detector.

`--defn` exists to separate **opaque terms** from **unproved theorems**.  That
distinction carries real planning weight: a theorem about a `sorry`ed `def` is
*unprovable* rather than merely unproved, because there is no body to unfold, so
definitional escapes must be closed before the proof escapes that sit on them.
A detector that over-reports here does not just inflate a count -- it misdirects
which lane gets taken first, which is what happened.

The original detector was one regex compiled with `re.S`, whose lazy `(.*?)` ran
from a declaration's name to the next `:= sorry` anywhere later in the file.
Every `def` that merely *preceded* an escape was therefore reported as
definitional.  Two live examples, both from
`Experimental/InfiniteDimensional/SinTheta/General.lean`:

* `spectralProjection`, whose body is `(spectralSubspace A s).starProjection`;
* `operatorAbsoluteValue`, which stayed on the list after being given the body
  `CFC.abs T`.

The first test below is exactly that shape and fails against the old regex.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "audit_scan.py"
SPEC = importlib.util.spec_from_file_location("audit_scan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)

ESCAPE = "sor" + "ry"


def names(text: str) -> set[str]:
    return {name for _kind, name in M.definitional_escapes(text)}


class BoundaryTest(unittest.TestCase):
    """The defect: a body must never be attributed across a declaration."""

    def test_def_with_real_body_before_a_later_escape(self) -> None:
        text = (
            "noncomputable def realBody (T : E) : E :=\n"
            "  CFC.abs T\n"
            "\n"
            "theorem laterOne (T : E) : True :=\n"
            f"  {ESCAPE}\n"
        )
        self.assertEqual(names(text), set())

    def test_the_escaped_def_itself_is_still_found(self) -> None:
        text = f"noncomputable def opaqueOne (A : E) : F :=\n  {ESCAPE}\n"
        self.assertEqual(names(text), {"opaqueOne"})

    def test_real_body_and_escaped_def_in_one_file(self) -> None:
        text = (
            "noncomputable def realBody (T : E) : E :=\n"
            "  CFC.abs T\n"
            "\n"
            "noncomputable def opaqueOne (A : E) : F :=\n"
            f"  {ESCAPE}\n"
        )
        self.assertEqual(names(text), {"opaqueOne"})

    def test_many_declarations_between_def_and_escape(self) -> None:
        text = (
            "def a : Nat := 0\n\n"
            "theorem t1 : True := trivial\n\n"
            "theorem t2 : True := trivial\n\n"
            f"theorem t3 : True := {ESCAPE}\n"
        )
        self.assertEqual(names(text), set())


class KindTest(unittest.TestCase):
    """Only term-introducing declarations are definitional."""

    def test_theorem_escape_is_not_definitional(self) -> None:
        self.assertEqual(names(f"theorem foo : True :=\n  {ESCAPE}\n"), set())

    def test_lemma_escape_is_not_definitional(self) -> None:
        self.assertEqual(names(f"lemma foo : True :=\n  {ESCAPE}\n"), set())

    def test_instance_escape_is_definitional(self) -> None:
        text = f"noncomputable instance fooInst : Bar E :=\n  {ESCAPE}\n"
        self.assertEqual(names(text), {"fooInst"})

    def test_anonymous_instance_escape_is_reported(self) -> None:
        """An unnamed instance is still an opaque term; a name-keyed scan drops it."""
        self.assertEqual(names(f"instance : Inhabited Nat :=\n  {ESCAPE}\n"),
                         {"<anonymous>"})

    def test_abbrev_escape_is_definitional(self) -> None:
        self.assertEqual(names(f"abbrev foo : Nat :=\n  {ESCAPE}\n"), {"foo"})


class BodyShapeTest(unittest.TestCase):
    def test_tactic_body_containing_an_escape_is_definitional(self) -> None:
        text = (
            "noncomputable def viaTactic : Nat := by\n"
            "  have h : True := trivial\n"
            f"  exact {ESCAPE}\n"
        )
        self.assertEqual(names(text), {"viaTactic"})

    def test_multiline_signature_before_the_escape(self) -> None:
        text = (
            "noncomputable def spread (A : E →L[K] E)\n"
            "    (s : Set R) :\n"
            "    Submodule K E :=\n"
            f"  {ESCAPE}\n"
        )
        self.assertEqual(names(text), {"spread"})


if __name__ == "__main__":
    unittest.main()
