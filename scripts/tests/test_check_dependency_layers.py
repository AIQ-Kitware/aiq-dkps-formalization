#!/usr/bin/env python3
"""Standard-library tests for scripts/check_dependency_layers.py."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_dependency_layers.py"
SPEC = importlib.util.spec_from_file_location("check_dependency_layers", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)

EMPTY_ALLOW = {
    "generic_davis_kahan_prefixes": ["DavisKahan.OperatorIdeal"],
    "generic_imports_sources": [],
    "production_imports_experimental": [],
}


class ClassifyTest(unittest.TestCase):
    def test_layers(self) -> None:
        self.assertEqual(M.classify("Mathlib.Analysis.X"), "mathlib")
        self.assertEqual(M.classify("TauCeti.Analysis.X"), "tauceti")
        self.assertEqual(M.classify("ForTauCeti.Analysis.X"), "fortauceti")
        self.assertEqual(M.classify("ForMathlib.X"), "formathlib")
        self.assertEqual(M.classify("Spectra.X"), "spectra")
        self.assertEqual(M.classify("DavisKahan.Sources.Y"), "dk-source")
        self.assertEqual(M.classify("DavisKahan.Experimental.Y"), "dk-experimental")
        self.assertEqual(M.classify("DavisKahan.OperatorIdeal.Y"), "davis-kahan")
        self.assertEqual(M.classify("Acharyya2024.Y"), "paper")


class ParseImportsTest(unittest.TestCase):
    def test_public_and_plain(self) -> None:
        text = (
            "module\n"
            "public import Mathlib.A\n"
            "import ForTauCeti.B\n"
            "  public import TauCeti.C\n"
            "-- import NotReal.D\n"
            "def foo := 1\n"
        )
        self.assertEqual(
            M.parse_imports(text),
            ["Mathlib.A", "ForTauCeti.B", "TauCeti.C"],
        )


class FirewallTest(unittest.TestCase):
    def test_fortauceti_clean(self) -> None:
        graph = {
            "ForTauCeti.X": ["Mathlib.A", "TauCeti.B", "ForTauCeti.Y"],
            "ForTauCeti.Y": ["Mathlib.C"],
        }
        v = M.check(graph, EMPTY_ALLOW, {})
        self.assertEqual(v, [])

    def test_fortauceti_forbidden(self) -> None:
        graph = {
            "ForTauCeti.X": ["Mathlib.A", "DavisKahan.Sources.Z", "Spectra.Q"],
        }
        v = M.check(graph, EMPTY_ALLOW, {})
        rules = sorted({x.rule for x in v})
        self.assertEqual(rules, ["FORTAUCETI_FIREWALL"])
        self.assertEqual(len(v), 2)

    def test_formathlib_forbidden(self) -> None:
        graph = {"ForMathlib.X": ["Mathlib.A", "TauCeti.B"]}
        v = M.check(graph, EMPTY_ALLOW, {})
        self.assertEqual([x.rule for x in v], ["FORMATHLIB_FIREWALL"])

    def test_formathlib_clean(self) -> None:
        graph = {"ForMathlib.X": ["Mathlib.A", "ForMathlib.Y"]}
        self.assertEqual(M.check(graph, EMPTY_ALLOW, {}), [])


class GenericSourceTest(unittest.TestCase):
    def test_backwards_dep_flagged(self) -> None:
        graph = {"DavisKahan.OperatorIdeal.Foo": ["DavisKahan.Sources.Bar"]}
        v = M.check(graph, EMPTY_ALLOW, {})
        self.assertEqual([x.rule for x in v], ["GENERIC_IMPORTS_SOURCE"])

    def test_allowlisted(self) -> None:
        graph = {"DavisKahan.OperatorIdeal.Foo": ["DavisKahan.Sources.Bar"]}
        allow = dict(EMPTY_ALLOW,
                     generic_imports_sources=["DavisKahan.OperatorIdeal.Foo"])
        self.assertEqual(M.check(graph, allow, {}), [])

    def test_non_generic_prefix_not_flagged(self) -> None:
        graph = {"DavisKahan.Riccati.Foo": ["DavisKahan.Sources.Bar"]}
        self.assertEqual(M.check(graph, EMPTY_ALLOW, {}), [])


class ExperimentalTest(unittest.TestCase):
    def test_production_imports_experimental_flagged(self) -> None:
        graph = {"DavisKahan.Riccati.Foo": ["DavisKahan.Experimental.X"]}
        v = M.check(graph, EMPTY_ALLOW, {})
        self.assertEqual([x.rule for x in v], ["PRODUCTION_IMPORTS_EXPERIMENTAL"])

    def test_allowlisted(self) -> None:
        graph = {"DavisKahan.Riccati.Foo": ["DavisKahan.Experimental.X"]}
        allow = dict(EMPTY_ALLOW,
                     production_imports_experimental=["DavisKahan.Riccati.Foo"])
        self.assertEqual(M.check(graph, allow, {}), [])


class ClusterClosureTest(unittest.TestCase):
    def test_closure_violation(self) -> None:
        graph = {
            "ForTauCeti.Cl.A": ["Mathlib.X", "ForMathlib.Sneaky"],
        }
        manifest = {"clusters": [
            {"cluster": "c1", "staging_modules": ["ForTauCeti.Cl.A"]}]}
        v = M.check(graph, EMPTY_ALLOW, manifest)
        # Both the firewall and the cluster-closure rules fire.
        rules = sorted({x.rule for x in v})
        self.assertIn("CLUSTER_CLOSURE", rules)


class ShortestPathTest(unittest.TestCase):
    def test_transitive_path(self) -> None:
        graph = {"A": ["B"], "B": ["C"], "C": ["Spectra.Z"]}
        p = M.shortest_path(graph, "A", lambda m: m == "Spectra.Z")
        self.assertEqual(p, ["A", "B", "C", "Spectra.Z"])


if __name__ == "__main__":
    unittest.main()
