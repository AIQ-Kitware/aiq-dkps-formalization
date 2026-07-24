#!/usr/bin/env python3
"""Tests for the paper-result summary in check_davis_kahan_frontier.py."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_davis_kahan_frontier.py"
SPEC = importlib.util.spec_from_file_location("check_davis_kahan_frontier", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class PaperResultRowsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = {
            "nodes": [
                {
                    "id": "foundation",
                    "kind": "foundation",
                    "dependencies": [],
                    "source_census_ids": ["paper-definition"],
                },
                {
                    "id": "bridge",
                    "kind": "bridge",
                    "dependencies": ["foundation"],
                    "source_census_ids": [],
                },
                {
                    "id": "endpoint-a",
                    "kind": "source",
                    "dependencies": ["bridge"],
                    "source_census_ids": ["paper-theorem"],
                },
                {
                    "id": "endpoint-b",
                    "kind": "source",
                    "dependencies": ["foundation"],
                    "source_census_ids": ["paper-theorem"],
                },
                {
                    "id": "internal-source-role",
                    "kind": "source",
                    "dependencies": [],
                    "source_census_ids": [],
                },
            ]
        }
        self.census = {
            "items": [
                {
                    "id": "paper-definition",
                    "source_anchor": "Definition 1.1",
                    "source_kind": "definition",
                    "title": "Printed definition",
                },
                {
                    "id": "paper-theorem",
                    "source_anchor": "Theorem 2.1",
                    "source_kind": "theorem",
                    "title": "Printed theorem",
                },
            ]
        }

    @staticmethod
    def status(local: dict[str, bool], recursive: dict[str, bool]):
        return {
            node_id: {
                "local_grounded": local[node_id],
                "recursive_grounded": recursive[node_id],
            }
            for node_id in local
        }

    def test_paper_mapping_is_independent_of_kind(self) -> None:
        mapped = MODULE.node_ids_by_census_id(self.manifest)
        self.assertEqual(mapped["paper-definition"], ["foundation"])
        self.assertNotIn("internal-source-role", {
            node_id for node_ids in mapped.values() for node_id in node_ids
        })

    def test_shared_closure_is_counted_once(self) -> None:
        closure = MODULE.dependency_closure(
            self.manifest, ["endpoint-a", "endpoint-b"]
        )
        self.assertEqual(
            closure, ["foundation", "bridge", "endpoint-a", "endpoint-b"]
        )

    def test_cascade_counts_only_local_missing_piece(self) -> None:
        local = {
            "foundation": False,
            "bridge": True,
            "endpoint-a": True,
            "endpoint-b": True,
            "internal-source-role": True,
        }
        recursive = {
            "foundation": False,
            "bridge": False,
            "endpoint-a": False,
            "endpoint-b": False,
            "internal-source-role": True,
        }
        rows = MODULE.paper_result_rows(
            self.manifest, self.census, self.status(local, recursive), True
        )
        theorem = next(row for row in rows if row["id"] == "paper-theorem")
        self.assertEqual(theorem["estimated_missing_pieces"], 1)
        self.assertEqual(theorem["pieces_total"], 4)
        self.assertEqual(theorem["estimated_complete_percent"], 75)
        self.assertFalse(theorem["recursively_grounded"])

    def test_complete_result_is_exactly_one_hundred_percent(self) -> None:
        local = {node["id"]: True for node in self.manifest["nodes"]}
        recursive = dict(local)
        rows = MODULE.paper_result_rows(
            self.manifest, self.census, self.status(local, recursive), True
        )
        for row in rows:
            self.assertEqual(row["estimated_missing_pieces"], 0)
            self.assertEqual(row["estimated_complete_percent"], 100)
            self.assertTrue(row["recursively_grounded"])

    def test_no_lean_does_not_guess_progress(self) -> None:
        rows = MODULE.paper_result_rows(self.manifest, self.census, {}, False)
        self.assertTrue(rows)
        for row in rows:
            self.assertIsNone(row["estimated_missing_pieces"])
            self.assertIsNone(row["estimated_complete_percent"])
            self.assertIsNone(row["recursively_grounded"])


if __name__ == "__main__":
    unittest.main()
