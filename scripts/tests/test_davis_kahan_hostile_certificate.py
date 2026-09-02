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
    representation change.
    """

    def _directed(self, data: dict) -> list[dict]:
        target = row(data, "S2-tan-two-theta")
        return [c for c in target["source_clauses"] if c.get("correspondence_required")]

    def test_the_current_clauses_declare_a_witness(self):
        clauses = self._directed(inventory())
        self.assertTrue(clauses, "no clause requires correspondence; this suite would be vacuous")
        for clause in clauses:
            witness = clause["correspondence_witness"]
            self.assertIn(witness["declaration"], clause["evidence"]["correspondence"])

    def test_the_witness_must_mention_both_objects(self):
        clause = self._directed(inventory())[0]
        witness = clause["correspondence_witness"]
        statement = M._declaration_statement_text(witness["declaration"])
        self.assertIsNotNone(statement, "the witness has no readable statement")
        for key in ("from_object", "to_object"):
            self.assertIn(witness[key], statement, f"{key} absent from the witness statement")

    def test_an_unrelated_theorem_does_not_bridge(self):
        """The substitution a reviewer used: another registered correspondence lemma."""
        statement = M._declaration_statement_text(
            "TauCeti.DavisKahan1970.approximationNumber_reflectionTangentCorner"
        )
        self.assertIsNotNone(statement)
        clause = self._directed(inventory())[0]
        self.assertNotIn(
            clause["correspondence_witness"]["to_object"], statement,
            "this lemma would wrongly pass as the bridge to the paper object",
        )

    def test_the_census_and_inventory_must_agree_a_change_happened(self):
        data = inventory()
        census = json.loads((ROOT / "dev/davis-kahan-1970-full-source-census.json").read_text())
        rows = {r["id"]: r for r in census["items"]}
        for clause in self._directed(data):
            clause.pop("correspondence_required", None)
        with rejected(self, "no inventory clause is marked correspondence_required"):
            M._validate_representation_change_agreement(data["results"], rows)
