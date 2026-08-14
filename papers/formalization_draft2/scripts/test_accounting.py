#!/usr/bin/env python3

from __future__ import annotations

import csv
import json
import pathlib
import unittest

HERE = pathlib.Path(__file__).resolve().parent.parent
GENERATED = HERE / "generated"


class AccountingArtifactsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.summary = json.loads((GENERATED / "accounting_summary.json").read_text())
        with (GENERATED / "commit_accounting_manifest.csv").open(newline="", encoding="utf-8") as file:
            cls.rows = list(csv.DictReader(file))

    def test_manifest_matches_pinned_history(self):
        self.assertEqual(len(self.rows), self.summary["history_commit_count"])
        self.assertEqual(
            sum(r["accounting_state"] == "exact_measured" for r in self.rows),
            self.summary["ledger_exact_commits_on_history"],
        )

    def test_exact_and_unaccounted_partition_history(self):
        exact = self.summary["ledger_exact_commits_on_history"]
        missing = self.summary["commits_without_exact_accounting"]
        self.assertEqual(exact + missing, self.summary["history_commit_count"])

    def test_preinstrumentation_count_is_temporal_not_pending_assignment(self):
        self.assertEqual(
            self.summary["accounting_states"]["unmeasured_pre_instrumentation"],
            self.summary["commits_before_instrumentation"],
        )

    def test_pending_overlap_never_becomes_exact_by_itself(self):
        for row in self.rows:
            if row["accounting_state"] == "exact_measured":
                self.assertEqual(row["extrapolation_eligible"], "0")

    def test_measured_lower_bound_contains_pending_usage(self):
        measured = self.summary["measured_lower_bound"]
        exact = self.summary["exact_on_history"]
        pending = self.summary["pending_segments_output_tokens"]
        self.assertGreaterEqual(measured["output_tokens"], exact["output_tokens"])
        self.assertGreater(pending, 0)

    def test_lifetime_snapshot_reconciliation_is_explicit(self):
        reconciliation = self.summary["lifetime_snapshot_reconciliation"]
        self.assertIn("snapshot_is_stale", reconciliation)
        self.assertGreater(reconciliation["ledger_rows_current"], 0)


if __name__ == "__main__":
    unittest.main()
