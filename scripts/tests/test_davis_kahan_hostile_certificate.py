#!/usr/bin/env python3
"""Regression tests for the mutations that broke three successive certificates.

Each test here is a tampering a hostile reviewer actually performed on a real
snapshot, which the checker of the day accepted. They are kept as tests because
every one of them was a *plausible* edit -- none looks like sabotage in a diff,
and each produced a green 29/29 certificate over evidence that had not changed.

    a91fee44   deleting the open-obligation ledger certified unchanged evidence
    a91fee44   any registered declaration satisfied a standing-assumption discharge
    a91fee44   `scope_inheritance` could contradict `extends_results` unnoticed
    951bf23b   another row's discharge theorem counted as this row's discharge
    951bf23b   the Markdown closure queue said "Empty" while two rows were blocked

The checker is exercised through its own predicates rather than by running the
whole file, so a failure names the invariant that regressed.
"""
from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check_davis_kahan_1970_result_inventory.py"
SPEC = importlib.util.spec_from_file_location("check_dk_hostile", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)

INVENTORY = ROOT / "dev/davis-kahan-1970-formalization-result-inventory.json"
ATOMS = ROOT / "dev/davis-kahan-1970-source-atom-inventory.json"


def inventory() -> dict:
    return json.loads(INVENTORY.read_text(encoding="utf-8"))


def atoms() -> dict[str, dict]:
    return {a["id"]: a for a in json.loads(ATOMS.read_text(encoding="utf-8"))["atoms"]}


def row(data: dict, result_id: str) -> dict:
    return next(r for r in data["results"] if r["id"] == result_id)


@contextlib.contextmanager
def rejected(case: unittest.TestCase, expected: str):
    """Assert the checker rejects, and says why.

    `fail()` prints the reason to stderr and exits, so the reason is not on the
    exception -- asserting against `str(SystemExit)` would pass on any rejection
    at all, including one for an unrelated reason.
    """
    buffer = io.StringIO()
    with contextlib.redirect_stderr(buffer):
        with case.assertRaises(SystemExit):
            yield
    case.assertIn(expected, buffer.getvalue())


class LedgerAndRowsMustAgree(unittest.TestCase):
    """Deleting the ledger must not certify evidence that did not change.

    Synthetic on purpose.  Earlier versions read the live inventory for a blocked
    row, so the day the last obligation closed the tests stopped exercising the
    invariant and passed for the wrong reason.
    """

    BLOCKED = "hostile_review_blocked"

    def _fixture(self) -> dict:
        return {
            "results": [
                {"id": "R-1", "semantic_certification": "accepted"},
                {"id": "R-2", "semantic_certification": self.BLOCKED},
            ],
            "open_hostile_review_obligations": {
                "status": "open",
                "obligations": [{"id": "an-open-finding", "results": ["R-2"]}],
            },
        }

    def test_a_consistent_pair_is_accepted(self):
        data = self._fixture()
        self.assertEqual(len(M._open_hostile_obligations(data, data["results"])), 1)

    def test_the_live_inventory_is_consistent(self):
        data = inventory()
        M._open_hostile_obligations(data, data["results"])

    def test_deleting_the_ledger_is_rejected(self):
        data = self._fixture()
        data["open_hostile_review_obligations"] = {"status": "closed", "obligations": []}
        with rejected(self, "no open hostile-review obligation"):
            M._open_hostile_obligations(data, data["results"])

    def test_accepting_a_blocked_row_while_its_obligation_is_open_is_rejected(self):
        data = self._fixture()
        data["results"][1]["semantic_certification"] = "accepted"
        with rejected(self, "still claim a terminal semantic_certification"):
            M._open_hostile_obligations(data, data["results"])

    def test_an_obligation_naming_an_unknown_result_is_rejected(self):
        data = self._fixture()
        data["open_hostile_review_obligations"]["obligations"][0]["results"] = ["R-9"]
        with rejected(self, "unknown result"):
            M._open_hostile_obligations(data, data["results"])


class ScopeInheritanceMustMatchScopeLinks(unittest.TestCase):
    """`local_to + inherited_by` is the same claim as `extends_results`."""

    def _scope_atom(self, *, needs_local: bool = False) -> tuple[dict[str, dict], str]:
        table = atoms()
        atom_id = next(
            a["id"] for a in table.values()
            if isinstance(a.get("scope_inheritance"), dict)
            and a["scope_inheritance"].get("inherited_by")
            and (not needs_local or a["scope_inheritance"].get("local_to"))
        )
        return table, atom_id

    def test_current_state_is_consistent(self):
        table, _ = self._scope_atom()
        M._validate_scope_inheritance(table, inventory()["results"])

    def test_dropping_a_result_from_inherited_by_only_is_rejected(self):
        table, atom_id = self._scope_atom()
        table = copy.deepcopy(table)
        table[atom_id]["scope_inheritance"]["inherited_by"].pop()
        with rejected(self, "must equal"):
            M._validate_scope_inheritance(table, inventory()["results"])

    def test_a_result_cannot_be_both_local_and_inherited(self):
        table, atom_id = self._scope_atom(needs_local=True)
        table = copy.deepcopy(table)
        inheritance = table[atom_id]["scope_inheritance"]
        inheritance["inherited_by"].append(inheritance["local_to"][0])
        with rejected(self, "both local_to and inherited_by"):
            M._validate_scope_inheritance(table, inventory()["results"])

    def test_an_unknown_result_is_rejected(self):
        table, atom_id = self._scope_atom()
        table = copy.deepcopy(table)
        table[atom_id]["scope_inheritance"]["inherited_by"].append("DK-99.9-thm")
        with rejected(self, "unknown result"):
            M._validate_scope_inheritance(table, inventory()["results"])


class DischargeMustBeEvidenceForItsOwnRow(unittest.TestCase):
    """A discharge theorem is evidence for one result, not for any result."""

    def _discharging_row(self, data: dict) -> dict:
        return next(r for r in data["results"] if isinstance(r.get("standing_assumption_discharge"), dict))

    def test_a_declaration_from_another_row_is_rejected(self):
        data = inventory()
        target = self._discharging_row(data)
        other = next(
            e["declaration"]
            for r in data["results"] if r["id"] != target["id"]
            for e in (r.get("standing_assumption_discharge", {}).get("discharged_by") or [])
        )
        target["standing_assumption_discharge"]["discharged_by"][0]["declaration"] = other
        census = {
            e["declaration"]
            for r in data["results"]
            for e in (r.get("standing_assumption_discharge", {}).get("discharged_by") or [])
        }
        with rejected(self, "not registered on this result"):
            M._check_standing_scope_consistency(target, atoms(), census)

    def test_a_discharge_must_say_what_it_concludes(self):
        data = inventory()
        target = self._discharging_row(data)
        entry = target["standing_assumption_discharge"]["discharged_by"][0]
        declaration = entry["declaration"]
        entry.pop("concludes", None)
        with rejected(self, "must record `concludes`"):
            M._check_standing_scope_consistency(target, atoms(), {declaration})

    def test_a_predicate_absent_from_the_statement_is_rejected(self):
        data = inventory()
        target = self._discharging_row(data)
        entry = target["standing_assumption_discharge"]["discharged_by"][0]
        entry["concludes"] = "APredicateNoTheoremMentions"
        with rejected(self, "does not occur in its statement"):
            M._check_standing_scope_consistency(target, atoms(), {entry["declaration"]})


if __name__ == "__main__":
    unittest.main()


class RepresentationChangeMustBeBridged(unittest.TestCase):
    """A clause on a different object than the paper's must name what bridges them.

    Added after a reviewer defeated the first 29/29 by emptying the directed
    clauses' correspondence list, and again by swapping in another registered
    correspondence theorem.  Both produced a green certificate over an unbridged
    representation change.  Extended 2026-09-02 with the tamperings a hostile
    reviewer would try against the closure that replaced it.
    """

    COMPLEX_PRIMARY = "TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex"
    REAL_PRIMARY = "TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_symmetricNorming_real"
    COMPLEX_WITNESS = "TauCeti.DavisKahan1970.approximationNumber_tanTwoDirectedCorner"
    REAL_WITNESS = "TauCeti.DavisKahan1970.approximationNumber_tanTwoDirectedCornerR"
    OLD_CORNER = "reflectionTangentCorner"

    def _directed(self, data: dict) -> list[dict]:
        target = row(data, "S2-tan-two-theta")
        return [c for c in target["source_clauses"] if c.get("correspondence_required")]

    def _clause(self, data: dict, cid: str) -> dict:
        return next(c for c in self._directed(data) if c["id"] == cid)

    def _census_rows(self) -> dict[str, dict]:
        census = json.loads((ROOT / "dev/davis-kahan-1970-full-source-census.json").read_text())
        return {r["id"]: r for r in census["items"]}

    def _clauses_pass(self, data: dict) -> None:
        """Run the clause validator statically (no compiler probe)."""
        _, atom_table = M._load_source_atoms()
        audit = (ROOT / data["semantic_review_sweep"]["compiler_audit_surface"]).read_text()
        M._validate_source_clauses(
            data["results"], atom_table, M._registered_census_declarations(), audit,
            data["semantic_review_sweep"]["compiler_audit_surface"], None,
        )

    # -- the state that must hold ------------------------------------------------

    def test_the_current_clauses_declare_a_witness(self):
        clauses = self._directed(inventory())
        self.assertTrue(clauses, "no clause requires correspondence; this suite would be vacuous")
        for clause in clauses:
            witness = clause["correspondence_witness"]
            self.assertIn(witness["declaration"], clause["evidence"]["correspondence"])

    def test_the_directed_clauses_are_established_on_the_source_shaped_endpoints(self):
        data = inventory()
        self.assertEqual(self._clause(data, "directed.complex")["evidence"]["primary"], self.COMPLEX_PRIMARY)
        self.assertEqual(self._clause(data, "directed.real")["evidence"]["primary"], self.REAL_PRIMARY)
        for clause in self._directed(data):
            self.assertEqual(clause["status"], "established")
        self._clauses_pass(data)

    def test_the_witness_must_mention_both_objects(self):
        for clause in self._directed(inventory()):
            witness = clause["correspondence_witness"]
            statement = M._declaration_statement_text(witness["declaration"])
            self.assertIsNotNone(statement, "the witness has no readable statement")
            for key in ("from_object", "to_object"):
                self.assertTrue(M._mentions(statement, witness[key]), f"{key} absent from the witness statement")

    def test_the_primaries_conclude_on_the_paper_objects_not_the_corner(self):
        for name in (self.COMPLEX_PRIMARY, self.REAL_PRIMARY):
            statement = M._declaration_statement_text(name)
            self.assertIsNotNone(statement)
            self.assertFalse(M._mentions(statement, self.OLD_CORNER), f"{name} still concludes on the implementation corner")
            self.assertFalse(M._mentions(statement, "ReflectionIntertwines"), f"{name} exposes the implementation hypothesis")
        self.assertTrue(M._mentions(M._declaration_statement_text(self.REAL_PRIMARY), "tanTwoDirectedCornerR"))

    # -- the mutations that must go red ------------------------------------------

    def test_1_removing_the_real_endpoint_from_canonical_evidence_is_rejected(self):
        data = inventory()
        target = row(data, "S2-tan-two-theta")
        target["canonical_evidence"] = [
            e for e in target["canonical_evidence"] if e["declaration"] != self.REAL_PRIMARY
        ]
        with rejected(self, "is not canonical evidence of this result"):
            self._clauses_pass(data)

    def test_2_replacing_the_paper_object_with_the_old_corner_is_rejected(self):
        data = inventory()
        self._clause(data, "directed.real")["correspondence_witness"]["from_object"] = self.OLD_CORNER
        with rejected(self, "does not occur in its statement as a whole identifier"):
            self._clauses_pass(data)

    def test_3_the_complex_correspondence_cannot_certify_the_real_clause(self):
        data = inventory()
        clause = self._clause(data, "directed.real")
        clause["correspondence_witness"]["declaration"] = self.COMPLEX_WITNESS
        clause["evidence"]["correspondence"] = [self.COMPLEX_WITNESS]
        clause["correspondence_witness"]["from_object"] = "projectorDifference U V * doubleSecant U V"
        with rejected(self, "does not occur in the clause's primary"):
            self._clauses_pass(data)

    def test_3b_a_complex_witness_does_not_mention_the_real_field(self):
        witness = M._declaration_statement_text(self.COMPLEX_WITNESS)
        real_witness = M._declaration_statement_text(self.REAL_WITNESS)
        self.assertIsNotNone(witness)
        self.assertIsNotNone(real_witness)
        self.assertNotIn("\u211d", witness, "the complex witness is complex-only")
        self.assertIn("\u211d", real_witness, "the real witness is stated over Submodule \u211d")

    def test_4_a_transport_the_proof_does_not_use_is_rejected(self):
        data = inventory()
        clause = self._clause(data, "directed.real")
        # a real transport that exists and is registered elsewhere, but which this
        # primary's proof does not invoke
        clause["transport_chain"].append("TauCeti.DavisKahan1970.complexifyReal_addBounded")
        with rejected(self, "does not invoke"):
            self._clauses_pass(data)

    def test_4b_dropping_a_transport_from_one_ledger_is_rejected(self):
        data = inventory()
        clause = self._clause(data, "directed.real")
        clause["transport_chain"].remove("TauCeti.DavisKahan1970.reducesSubspace_addBounded_complexifyReal")
        with rejected(self, "bridging chain"):
            M._validate_representation_change_agreement(data["results"], self._census_rows())

    def test_5_removing_a_statement_pin_for_a_correspondence_declaration_is_rejected(self):
        data = inventory()
        rows = self._census_rows()
        review = rows["S2-tan-two-theta"]["semantic_review"]
        review["statement_pins"] = [p for p in review["statement_pins"] if p["declaration"] != self.REAL_WITNESS]
        with rejected(self, "without a statement pin"):
            M._validate_representation_change_agreement(data["results"], rows)

    def test_6_a_similarly_named_unrelated_object_is_rejected(self):
        data = inventory()
        clause = self._clause(data, "directed.real")
        clause["correspondence_witness"]["to_object"] = "sinTwoThetaIdealBloc"
        with rejected(self, "does not occur in its statement as a whole identifier"):
            self._clauses_pass(data)
        data = inventory()
        clause = self._clause(data, "directed.real")
        clause["correspondence_witness"]["to_object"] = "sinTwoAngleOperatorR"
        with rejected(self, "does not occur in its statement as a whole identifier"):
            self._clauses_pass(data)

    def test_7_deleting_an_obligation_before_the_row_is_accepted_is_rejected(self):
        data = inventory()
        row(data, "S2-tan-two-theta")["semantic_certification"] = "hostile_review_blocked"
        with rejected(self, "no open hostile-review obligation"):
            M._open_hostile_obligations(data, data["results"])

    def test_8_accepting_the_row_while_the_real_clause_is_open_is_rejected(self):
        data = inventory()
        clause = self._clause(data, "directed.real")
        clause["status"] = "open"
        clause["open_reason"] = "synthetic: the real directed clause is reopened for this test, and nothing else changed"
        with rejected(self, "recorded as terminal, but"):
            self._clauses_pass(data)

    def test_a_witness_not_invoked_by_the_primary_is_rejected(self):
        """The 2026-09-02 morning defect: a witness registered beside a theorem that never used it."""
        data = inventory()
        clause = self._clause(data, "directed.complex")
        other = "TauCeti.DavisKahan1970.reflectionTangentCorner_same_paperTanTwoDirectedCorner"
        clause["correspondence_witness"]["declaration"] = other
        clause["correspondence_witness"]["from_object"] = "projectionBlock"
        clause["correspondence_witness"]["to_object"] = "reflectionTangentCorner"
        clause["evidence"]["correspondence"].append(other)
        with rejected(self, "is not invoked by the proof"):
            self._clauses_pass(data)

    def test_the_census_and_inventory_must_agree_a_change_happened(self):
        data = inventory()
        for clause in self._directed(data):
            clause.pop("correspondence_required", None)
        with rejected(self, "no inventory clause is marked correspondence_required"):
            M._validate_representation_change_agreement(data["results"], self._census_rows())
