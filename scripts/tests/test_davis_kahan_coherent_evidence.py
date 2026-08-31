#!/usr/bin/env python3
"""Regression tests for the coherent-evidence rule in the Davis--Kahan result checker.

These exist because the checker once accepted a certificate that no theorem
proves.  `canonical_evidence` recorded, per declaration, a set of source atoms it
covered, and a counted result was terminal when the **union** over its
declarations covered the row.  For `S2-sin-two-theta` that meant:

    unbounded DIRECTED theorems  ->  unbounded scope, gap scope, bounded residual
    bounded AMBIENT theorem      ->  the ambient conclusion
    union                        ->  "ambient conclusion at unbounded scope"

which is a statement no declaration and no proof chain establishes.

The negative test reconstructs exactly that composition and requires rejection.
The positive tests pin the shapes that must keep passing, so the fix cannot be a
blanket "every witness must carry every atom" rule -- the source has separate
clauses, fixed-field siblings, clause-local hypotheses, and theorems stronger
than the paper.
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_davis_kahan_1970_result_inventory.py"
SPEC = importlib.util.spec_from_file_location("check_dk_result_inventory", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


UNBOUNDED = "→ₗ.["
PAPER_NORM = "PaperUnitaryInvariantNorm"


def atoms() -> dict[str, dict]:
    """A miniature source row: one directed and one ambient conclusion, sharing scope."""
    return {
        "R.directed": {"kind": "theorem", "source_role": "mathematical_assertion"},
        "R.ambient": {"kind": "theorem", "source_role": "mathematical_assertion"},
        "R.unbounded": {
            "kind": "scope",
            "source_role": "mathematical_assertion",
            "type_requirements": {"must_contain": [UNBOUNDED], "must_not_contain": []},
        },
        "R.uinorm": {
            "kind": "scope",
            "source_role": "mathematical_assertion",
            "type_requirements": {"must_contain": [PAPER_NORM], "must_not_contain": []},
        },
        "R.ritz": {"kind": "hypothesis", "source_role": "mathematical_assertion"},
    }


def clause(cid, concl, scalar, primary, *, status="established", local=None, corr=None):
    out = {
        "id": cid,
        "conclusion_atoms": list(concl),
        "scalar_scope": scalar,
        "evidence": {"primary": primary, "correspondence": list(corr or [])},
        "status": status,
        "justification": "A miniature clause standing in for one printed source conclusion.",
    }
    if local:
        out["clause_hypothesis_atoms"] = list(local)
    if status == "open":
        out["open_reason"] = (
            "The only available witness is stated at a narrower scope than this result is "
            "certified at, so it does not establish the printed clause; this is what the "
            "flat-union model hid."
        )
    return out


def result(clauses, *, wide=("R.unbounded", "R.uinorm", "R.ritz"), terminal=True, decls=None):
    return {
        "id": "R",
        "source_atom_ids": [
            "R.directed", "R.ambient", "R.unbounded", "R.uinorm", "R.ritz",
        ],
        "result_wide_scope_atoms": list(wide),
        "source_clauses": list(clauses),
        "lean_declarations": list(decls or ["thm.directed", "thm.ambient"]),
        "disposition": "proved_exact" if terminal else "compiled_specialization",
        "verification": "proved_in_build",
        "semantic_certification": "accepted" if terminal else "reopened_math",
    }


def run(item, printed):
    """Run the clause validator, returning the failure message or None.

    `fail` prints the diagnosis to stderr and exits, so the message is there rather
    than in the exception; the tests assert on the diagnosis, because a checker
    that rejects for the wrong reason is not a fixed checker.
    """
    census = set(item["lean_declarations"])
    audit = "\n".join(f"#check @{d}" for d in census)
    buffer = io.StringIO()
    try:
        with contextlib.redirect_stderr(buffer):
            M._validate_source_clauses([item], atoms(), census, audit, "audit.lean", printed)
    except SystemExit:
        return buffer.getvalue().strip() or "FAILED (no diagnosis)"
    return None


class CoherentEvidenceTest(unittest.TestCase):
    maxDiff = None

    def test_rejects_scope_donated_by_a_sibling(self) -> None:
        """THE REGRESSION.  Unbounded directed + bounded ambient must not certify."""
        printed = {
            "thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.ambient": f"(N : {PAPER_NORM}) (A B : H →L[ℂ] H) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("directed.real", ["R.directed"], "real", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient"),
        ])
        message = run(item, printed)
        self.assertIsNotNone(message, "the old cross-declaration composition was accepted")
        self.assertIn("R.unbounded", message)
        self.assertIn("may not donate this scope", message)

    def test_accepts_real_and_complex_siblings(self) -> None:
        printed = {
            "thm.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : both",
            "thm.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : both",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.c"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.c"),
            clause("directed.real", ["R.directed"], "real", "thm.r"),
            clause("ambient.real", ["R.ambient"], "real", "thm.r"),
        ], decls=["thm.c", "thm.r"])
        self.assertIsNone(run(item, printed))

    def test_accepts_separately_discharged_directed_and_ambient_clauses(self) -> None:
        """Two clauses, two theorems -- fine, as long as EACH carries the scope."""
        printed = {
            "thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.ambient": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("directed.real", ["R.directed"], "real", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient"),
        ])
        self.assertIsNone(run(item, printed))

    def test_accepts_a_theorem_stronger_than_the_paper(self) -> None:
        """A witness that does not need one printed hypothesis is not penalised.

        `R.ritz` is a clause-local hypothesis of the directed clause only; the
        ambient witness never mentions it and must not be required to.
        """
        printed = {
            "thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) (ritz) : directed",
            "thm.ambient": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed", local=["R.ritz"]),
            clause("directed.real", ["R.directed"], "real", "thm.directed", local=["R.ritz"]),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient"),
        ], wide=("R.unbounded", "R.uinorm"))
        self.assertIsNone(run(item, printed))

    def test_accepts_a_primary_with_a_correspondence_chain(self) -> None:
        printed = {
            "thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.ambient": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient-representative",
            "lem.transport": "same approximation numbers",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("directed.real", ["R.directed"], "real", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient",
                   corr=["lem.transport"]),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient",
                   corr=["lem.transport"]),
        ], decls=["thm.directed", "thm.ambient", "lem.transport"])
        self.assertIsNone(run(item, printed))

    def test_open_clause_forces_a_nonterminal_result(self) -> None:
        printed = {
            "thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.ambient": f"(N : {PAPER_NORM}) (A B : H →L[ℂ] H) : ambient",
        }
        clauses = [
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("directed.real", ["R.directed"], "real", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient", status="open"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient", status="open"),
        ]
        self.assertIsNotNone(run(result(clauses, terminal=True), printed))
        self.assertIsNone(run(result(clauses, terminal=False), printed))

    def test_requires_both_scalar_fields(self) -> None:
        printed = {"thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : both"}
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.directed"),
        ], decls=["thm.directed"])
        message = run(item, printed)
        self.assertIsNotNone(message)
        self.assertIn("both fields", message)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
