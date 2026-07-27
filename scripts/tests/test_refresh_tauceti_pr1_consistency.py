#!/usr/bin/env python3
"""Tests for scripts/refresh_tauceti_pr1_consistency.py."""
from __future__ import annotations

import copy
import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "refresh_tauceti_pr1_consistency.py"
SPEC = importlib.util.spec_from_file_location("refresh_tauceti_pr1_consistency", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


class RefreshManifestTest(unittest.TestCase):
    def fixture(self) -> dict:
        return {
            "davis_kahan_commit": "old-dk",
            "tauceti_submodule_commit": "old-tc",
            "clusters": [{
                "cluster": "approximation-number",
                "status": "staged",
                "tauceti_population": "old evidence",
                "staging_modules": [
                    "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic",
                    M.OLD_MODULUS,
                ],
            }],
            "records": [{
                "source_module": "old source",
                "source_declarations": ["agent.owned.name", "another.name"],
                "current_namespace": "old namespace",
                "staging_module": M.OLD_MODULUS,
                "final_tauceti_module": (
                    "TauCeti.Analysis.OperatorIdeal.ApproximationNumber.OperatorModulus"
                ),
                "provenance_class": "copied",
                "direct_dependencies": ["Mathlib"],
                "status": "staged-partial",
            }],
        }

    def write_module(self, root: Path, module: str, imports: list[str]) -> None:
        path = M.staging_path(module, root)
        path.parent.mkdir(parents=True, exist_ok=True)
        text = "module\n" + "".join(f"public import {dep}\n" for dep in imports)
        path.write_text(text, encoding="utf-8")

    def make_tree(self, root: Path, with_rank_helper: bool = False) -> None:
        basic_imports = ["ForTauCeti.SetTheory.Cardinal.Lift"]
        if with_rank_helper:
            basic_imports.append("ForTauCeti.LinearAlgebra.Dimension.RankCompLe")
        self.write_module(
            root,
            "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic",
            basic_imports,
        )
        self.write_module(root, "ForTauCeti.SetTheory.Cardinal.Lift", [])
        if with_rank_helper:
            self.write_module(
                root, "ForTauCeti.LinearAlgebra.Dimension.RankCompLe", []
            )
        self.write_module(root, M.NEW_MODULUS, [])

    def test_refreshes_paths_revisions_and_dependency_closure(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_tree(root)
            before = self.fixture()
            after = M.refresh_manifest(before, "new-dk", "new-tc", root)
        self.assertEqual(before["davis_kahan_commit"], "old-dk")
        self.assertEqual(after["davis_kahan_commit"], "new-dk")
        self.assertEqual(after["tauceti_submodule_commit"], "new-tc")
        modules = after["clusters"][0]["staging_modules"]
        self.assertEqual(
            modules,
            [
                "ForTauCeti.SetTheory.Cardinal.Lift",
                "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic",
                M.NEW_MODULUS,
            ],
        )
        self.assertNotIn(M.OLD_MODULUS, modules)
        self.assertEqual(after["records"][0]["staging_module"], M.NEW_MODULUS)
        self.assertEqual(
            after["records"][0]["final_tauceti_module"], M.NEW_FINAL_MODULUS
        )

    def test_discovers_new_rank_helper_without_name_edits(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_tree(root, with_rank_helper=True)
            before = self.fixture()
            names = copy.deepcopy(before["records"][0]["source_declarations"])
            after = M.refresh_manifest(before, "new-dk", "new-tc", root)
        modules = after["clusters"][0]["staging_modules"]
        self.assertIn("ForTauCeti.LinearAlgebra.Dimension.RankCompLe", modules)
        self.assertEqual(after["records"][0]["source_declarations"], names)

    def test_preserves_agent_owned_declaration_names_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_tree(root)
            before = self.fixture()
            names = copy.deepcopy(before["records"][0]["source_declarations"])
            after = M.refresh_manifest(before, "new-dk", "new-tc", root)
        self.assertEqual(after["records"][0]["source_declarations"], names)

    def test_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.make_tree(root)
            first = M.refresh_manifest(self.fixture(), "new-dk", "new-tc", root)
            second = M.refresh_manifest(first, "new-dk", "new-tc", root)
        self.assertEqual(first, second)

    def test_cycle_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            self.write_module(root, "ForTauCeti.A", ["ForTauCeti.B"])
            self.write_module(root, "ForTauCeti.B", ["ForTauCeti.A"])
            with self.assertRaises(M.ConsistencyError):
                M.dependency_closed_modules(["ForTauCeti.A"], root)


class LaneClaimTest(unittest.TestCase):
    def test_inserts_once(self) -> None:
        text = (
            "# Lane claims\n\n"
            "| agent | file(s) | declarations | date | status |\n"
            "|-------|---------|-------------|------|--------|\n"
            "| edward | x | y | 2026-07-27 | claimed |\n"
        )
        once = M.refresh_lanes(text)
        twice = M.refresh_lanes(once)
        self.assertEqual(once, twice)
        self.assertEqual(once.count(M.CLAIM_MARKER), 1)
        self.assertIn("| edward |", once)


if __name__ == "__main__":
    unittest.main()
