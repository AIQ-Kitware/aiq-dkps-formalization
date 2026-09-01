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
# The carriers that separate the ambient-operator axis from the compression axis.
RITZ_PAIR = "UnboundedRitzPair"      # `trial.compression : Z →ₗ.[𝕜] Z`
TRIAL_BLOCK = "UnboundedTrialBlock"  # `operator : Z →L[𝕜] Z` -- BOUNDED


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
        # The THIRD unbounded axis: the trial/Ritz COMPRESSION may itself be unbounded.
        # Distinct from `R.unbounded`, which is only about the ambient operator.
        "R.unbounded_compression": {
            "kind": "scope",
            "source_role": "mathematical_assertion",
            "type_requirements": {
                "must_contain": [RITZ_PAIR],
                "must_not_contain": [TRIAL_BLOCK],
            },
        },
        "R.lemma": {"kind": "lemma", "source_role": "mathematical_assertion"},
        "R.halfinfinite": {
            "kind": "scope",
            "source_role": "mathematical_assertion",
            "scope_assertion_mode": {
                "mode": "clause_justified",
                "reason": "Different theorem families spell this scope differently.",
            },
        },
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


def result(clauses, *, wide=("R.unbounded", "R.uinorm", "R.ritz"), terminal=True, decls=None,
           canonical=None, atom_ids=None):
    """A miniature counted result.

    `canonical_evidence` is synthesized from the clauses unless a test overrides it:
    a clause's primary IS canonical evidence, and its scalar scope is the primary's
    compiler-derived one.  Tests that want to break either of those pass `canonical`
    explicitly.
    """
    if canonical is None:
        seen: dict[str, str] = {}
        for c in clauses:
            seen.setdefault(c["evidence"]["primary"], c["scalar_scope"])
        canonical = [
            {"declaration": d, "role": "primary_source_witness", "scalar_scope": s,
             "evidence_kind": "proof", "covers_source_atoms": [], "capability_classes": []}
            for d, s in seen.items()
        ]
    return {
        "id": "R",
        "source_atom_ids": list(atom_ids or [
            "R.directed", "R.ambient", "R.unbounded", "R.uinorm", "R.ritz",
        ]),
        "result_wide_scope_atoms": list(wide),
        "source_clauses": list(clauses),
        "lean_declarations": list(decls or ["thm.directed", "thm.ambient"]),
        "canonical_evidence": list(canonical),
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
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : directed",
            "thm.ambient.c": f"(N : {PAPER_NORM}) (A B : H →L[ℂ] H) : ambient",
            "thm.ambient.r": f"(N : {PAPER_NORM}) (A B : E →L[ℝ] E) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient.c"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient.r"),
        ], decls=["thm.directed.c", "thm.directed.r", "thm.ambient.c", "thm.ambient.r"])
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
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : directed",
            "thm.ambient.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient",
            "thm.ambient.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient.c"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient.r"),
        ], decls=["thm.directed.c", "thm.directed.r", "thm.ambient.c", "thm.ambient.r"])
        self.assertIsNone(run(item, printed))

    def test_accepts_a_theorem_stronger_than_the_paper(self) -> None:
        """A witness that does not need one printed hypothesis is not penalised.

        `R.ritz` is a clause-local hypothesis of the directed clause only; the
        ambient witness never mentions it and must not be required to.
        """
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) (ritz) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) (ritz) : directed",
            "thm.ambient.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient",
            "thm.ambient.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : ambient",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c", local=["R.ritz"]),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r", local=["R.ritz"]),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient.c"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient.r"),
        ], wide=("R.unbounded", "R.uinorm"),
           decls=["thm.directed.c", "thm.directed.r", "thm.ambient.c", "thm.ambient.r"])
        self.assertIsNone(run(item, printed))

    def test_accepts_a_primary_with_a_correspondence_chain(self) -> None:
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : directed",
            "thm.ambient.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : ambient-representative",
            "thm.ambient.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : ambient-representative",
            "lem.transport": "same approximation numbers",
        }
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient.c",
                   corr=["lem.transport"]),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient.r",
                   corr=["lem.transport"]),
        ], decls=["thm.directed.c", "thm.directed.r", "thm.ambient.c", "thm.ambient.r",
                  "lem.transport"])
        self.assertIsNone(run(item, printed))

    def test_open_clause_forces_a_nonterminal_result(self) -> None:
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}ℝ] E) : directed",
            "thm.ambient.c": f"(N : {PAPER_NORM}) (A B : H →L[ℂ] H) : ambient",
            "thm.ambient.r": f"(N : {PAPER_NORM}) (A B : E →L[ℝ] E) : ambient",
        }
        decls = ["thm.directed.c", "thm.directed.r", "thm.ambient.c", "thm.ambient.r"]
        clauses = [
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.ambient.c", status="open"),
            clause("ambient.real", ["R.ambient"], "real", "thm.ambient.r", status="open"),
        ]
        self.assertIsNotNone(run(result(clauses, terminal=True, decls=decls), printed))
        self.assertIsNone(run(result(clauses, terminal=False, decls=decls), printed))

    def test_requires_both_scalar_fields(self) -> None:
        printed = {"thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}ℂ] H) : both"}
        item = result([
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.directed"),
        ], decls=["thm.directed"])
        message = run(item, printed)
        self.assertIsNotNone(message)
        self.assertIn("both fields", message)


    # ---- loopholes found by the 2026-08-31 hostile re-review ----

    def test_rejects_a_primary_that_is_only_supporting_evidence(self) -> None:
        """A clause may not be witnessed by a declaration held as supporting evidence.

        Without this the coherence check has no compiler-printed type to work with,
        and the row is certified by a specialization or a presentation wrapper.
        """
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}\u211d] E) : directed",
        }
        clauses = [
            clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
            clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
        ]
        canonical = [
            {"declaration": "thm.directed.c", "role": "primary_source_witness",
             "scalar_scope": "complex", "evidence_kind": "proof",
             "covers_source_atoms": [], "capability_classes": []},
        ]
        item = result(
            clauses, canonical=canonical, wide=("R.unbounded", "R.uinorm"),
            decls=["thm.directed.c", "thm.directed.r"],
            atom_ids=["R.directed", "R.unbounded", "R.uinorm"],
        )
        message = run(item, printed)
        self.assertIsNotNone(message)
        self.assertIn("is not canonical evidence", message)

    def test_rejects_a_clause_scalar_scope_that_contradicts_its_primary(self) -> None:
        """A row must not claim both fields by relabelling one theorem."""
        printed = {"thm.directed": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) : both"}
        clauses = [
            clause("directed.complex", ["R.directed"], "complex", "thm.directed"),
            clause("directed.real", ["R.directed"], "real", "thm.directed"),
            clause("ambient.complex", ["R.ambient"], "complex", "thm.directed"),
            clause("ambient.real", ["R.ambient"], "real", "thm.directed"),
        ]
        canonical = [
            {"declaration": "thm.directed", "role": "primary_source_witness",
             "scalar_scope": "complex", "evidence_kind": "proof",
             "covers_source_atoms": [], "capability_classes": []},
        ]
        message = run(result(clauses, canonical=canonical, decls=["thm.directed"]), printed)
        self.assertIsNotNone(message)
        self.assertIn("disagrees with the compiler-derived scalar scope", message)

    def test_requires_a_clause_for_a_lemma_conclusion(self) -> None:
        """Conclusions stated under `lemma` are printed conclusions too.

        `result_conclusions` keyed on `kind == "theorem"` alone until 2026-08-31, so
        the four Section 6 lemmas and Proposition 4.4 had a vacuous coverage check.
        """
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}\u211d] E) : directed",
        }
        item = result(
            [
                clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
                clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            ],
            wide=("R.unbounded", "R.uinorm"),
            decls=["thm.directed.c", "thm.directed.r"],
            atom_ids=["R.directed", "R.unbounded", "R.uinorm", "R.lemma"],
        )
        message = run(item, printed)
        self.assertIsNotNone(message)
        self.assertIn("R.lemma", message)

    def test_rejects_gap_tokens_absent_from_the_printed_type(self) -> None:
        """Clause-justified scope may not be claimed through hypotheses that are not there."""
        printed = {
            "thm.directed.c": f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) : directed",
            "thm.directed.r": f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}\u211d] E) : directed",
        }
        good = clause("directed.complex", ["R.directed"], "complex", "thm.directed.c")
        good["gap_scope_justification"] = (
            "The primary quantifies over an unbounded ambient operator, which is what "
            "realizes the half-infinite configuration for this family."
        )
        good["gap_scope_hypothesis_tokens"] = [UNBOUNDED]
        bad = clause("directed.real", ["R.directed"], "real", "thm.directed.r")
        bad["gap_scope_justification"] = good["gap_scope_justification"]
        bad["gap_scope_hypothesis_tokens"] = ["FormBoundedSylvesterGap"]
        item = result(
            [good, bad],
            wide=("R.unbounded", "R.uinorm", "R.halfinfinite"),
            decls=["thm.directed.c", "thm.directed.r"],
            atom_ids=["R.directed", "R.unbounded", "R.uinorm", "R.halfinfinite"],
        )
        message = run(item, printed)
        self.assertIsNotNone(message)
        self.assertIn("do not occur in the compiler-printed type", message)

    # ---- the unbounded-compression axis, found by the 2026-08-31 Palomar audit ----

    def test_rejects_a_bounded_compression_under_an_unbounded_ambient_operator(self) -> None:
        """THE REGRESSION.  `unbounded ambient A` + `bounded A_0` is not `A_0 may be unbounded`.

        This is what the certificate accepted for the `S2-tan-theta` directed clause.  Its
        primaries took a `TanTheta.UnboundedTrialBlock`, whose Ritz compression
        `operator : Z ->L Z` is bounded and everywhere defined; the bundle's *name* records
        only that the ambient operator is unbounded.  The witness satisfied the
        ambient-unbounded axis and the bounded-residual axis, and the Appendix scope atom
        carried no requirement at all, so nothing objected.
        """
        printed = {
            "thm.directed.c": (
                f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) "
                f"(D : {TRIAL_BLOCK} A Z) (R : Z \u2192L[\u2102] H) : directed"
            ),
            "thm.directed.r": (
                f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}\u211d] E) "
                f"(D : {TRIAL_BLOCK} A Z) (R : Z \u2192L[\u211d] E) : directed"
            ),
        }
        item = result(
            [
                clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
                clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            ],
            wide=("R.unbounded", "R.uinorm", "R.unbounded_compression"),
            decls=["thm.directed.c", "thm.directed.r"],
            atom_ids=["R.directed", "R.unbounded", "R.uinorm", "R.unbounded_compression"],
        )
        message = run(item, printed)
        self.assertIsNotNone(
            message, "a bounded Ritz compression satisfied the unbounded-compression scope"
        )
        self.assertIn("R.unbounded_compression", message)
        self.assertIn(TRIAL_BLOCK, message)

    def test_accepts_a_genuinely_unbounded_compression(self) -> None:
        """The positive side: an `UnboundedRitzPair` carries the Appendix scope."""
        printed = {
            "thm.directed.c": (
                f"(N : {PAPER_NORM}) (A : H {UNBOUNDED}\u2102] H) "
                f"(D : {RITZ_PAIR} A Z) (R : Z \u2192L[\u2102] H) : directed"
            ),
            "thm.directed.r": (
                f"(N : {PAPER_NORM}) (A : E {UNBOUNDED}\u211d] E) "
                f"(D : {RITZ_PAIR} A Z) (R : Z \u2192L[\u211d] E) : directed"
            ),
        }
        item = result(
            [
                clause("directed.complex", ["R.directed"], "complex", "thm.directed.c"),
                clause("directed.real", ["R.directed"], "real", "thm.directed.r"),
            ],
            wide=("R.unbounded", "R.uinorm", "R.unbounded_compression"),
            decls=["thm.directed.c", "thm.directed.r"],
            atom_ids=["R.directed", "R.unbounded", "R.uinorm", "R.unbounded_compression"],
        )
        self.assertIsNone(run(item, printed))


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
