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
    """Deleting the ledger must not certify evidence that did not change."""

    def test_current_state_is_consistent(self):
        data = inventory()
        M._open_hostile_obligations(data, data["results"])

    def test_deleting_the_ledger_is_rejected(self):
        data = inventory()
        blocked = [
            r["id"] for r in data["results"]
            if M._semantic_certification(r) in M.BLOCKED_SEMANTIC_CERTIFICATIONS
        ]
        self.assertTrue(blocked, "fixture has no blocked row; this test would be vacuous")
        data["open_hostile_review_obligations"]["obligations"] = []
        data["open_hostile_review_obligations"]["status"] = "closed"
        with rejected(self, "no open hostile-review obligation"):
            M._open_hostile_obligations(data, data["results"])

    def test_accepting_a_blocked_row_while_its_obligation_is_open_is_rejected(self):
        data = inventory()
        target = next(
            r for r in data["results"]
            if M._semantic_certification(r) in M.BLOCKED_SEMANTIC_CERTIFICATIONS
        )
        target["semantic_certification"] = "accepted"
        with rejected(self, "still claim a terminal semantic_certification"):
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
