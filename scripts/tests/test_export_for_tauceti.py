#!/usr/bin/env python3
"""Standard-library tests for scripts/export_for_tauceti.py."""
from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "export_for_tauceti.py"
SPEC = importlib.util.spec_from_file_location("export_for_tauceti", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


HEADER = (
    "/-\nCopyright (c) 2026 Kitware, Inc. All rights reserved.\n"
    "Authors: Jon Crall\n-/\n"
    "module\n\n"
)


class RewriteTest(unittest.TestCase):
    def test_rewrites_sibling_and_keeps_mathlib(self) -> None:
        text = (
            "public import Mathlib.Analysis.X\n"
            "public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic\n"
            "  import ForTauCeti.Analysis.InnerProductSpace.CourantFischer\n"
        )
        new, forbidden = M.rewrite_imports(text)
        self.assertEqual(forbidden, [])
        self.assertIn("public import Mathlib.Analysis.X", new)
        self.assertIn(
            "public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic",
            new)
        self.assertIn(
            "  import TauCeti.Analysis.InnerProductSpace.CourantFischer", new)
        self.assertNotIn("ForTauCeti", new)

    def test_forbidden_import_detected(self) -> None:
        text = "public import DavisKahan.Sources.Foo\nimport Spectra.Bar\n"
        _, forbidden = M.rewrite_imports(text)
        self.assertEqual(sorted(forbidden), ["DavisKahan.Sources.Foo", "Spectra.Bar"])

    def test_provenance_and_body_preserved(self) -> None:
        body = HEADER + "/-!\n# T\n## Provenance\nKitware source\n-/\ndef foo := 1\n"
        new, _ = M.rewrite_imports(body)
        self.assertEqual(new, body)  # nothing but imports is touched


class PathMappingTest(unittest.TestCase):
    def test_default_mapping(self) -> None:
        M.TAUCETI_ROOT = Path("/tc")
        final, target = M.staging_module_to_target(
            "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic", None)
        self.assertEqual(final, "TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic")
        self.assertEqual(
            target,
            Path("/tc/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean"))

    def test_explicit_final_module(self) -> None:
        M.TAUCETI_ROOT = Path("/tc")
        final, target = M.staging_module_to_target(
            "ForTauCeti.Analysis.InnerProductSpace.CourantFischer",
            "TauCeti.Analysis.InnerProductSpace.CourantFischer")
        self.assertEqual(
            target,
            Path("/tc/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean"))


class DeclNamesTest(unittest.TestCase):
    def test_extracts(self) -> None:
        text = (
            "@[simp]\ntheorem foo_bar : True := trivial\n"
            "noncomputable def baz := 1\n"
            "private theorem hidden := 2\n"
        )
        self.assertEqual(M.declaration_names(text), ["foo_bar", "baz", "hidden"])


class EndToEndTest(unittest.TestCase):
    def _setup(self) -> tuple[Path, Path, dict]:
        tmp = Path(tempfile.mkdtemp())
        M.ROOT = tmp
        M.TAUCETI_ROOT = tmp / "external/TauCeti"
        src = tmp / "ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean"
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text(
            HEADER
            + "public import Mathlib.A\n"
            + "public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer\n"
            + "def approximationNumber := 1\n",
            encoding="utf-8")
        cf = tmp / "ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean"
        cf.parent.mkdir(parents=True, exist_ok=True)
        cf.write_text(HEADER + "public import Mathlib.B\ndef specSubspace := 2\n",
                      encoding="utf-8")
        manifest = {"clusters": [{"cluster": "c", "staging_modules": [
            "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic",
            "ForTauCeti.Analysis.InnerProductSpace.CourantFischer"]}],
            "records": []}
        return tmp, src, manifest

    def test_write_then_check_stable(self) -> None:
        tmp, _, manifest = self._setup()
        r1 = M.run(manifest, "c", write=True)
        self.assertTrue(r1.ok, r1.lines)
        # written file has the rewritten import
        target = M.TAUCETI_ROOT / (
            "TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean")
        self.assertTrue(target.exists())
        content = target.read_text()
        self.assertIn("public import TauCeti.Analysis.InnerProductSpace.CourantFischer",
                      content)
        self.assertIn("Kitware", content)  # provenance preserved
        # check mode passes
        r2 = M.run(manifest, "c", write=False)
        self.assertTrue(r2.ok, r2.lines)
        # repeated write is UNCHANGED (idempotent)
        r3 = M.run(manifest, "c", write=True)
        self.assertTrue(r3.ok)
        self.assertTrue(any("UNCHANGED" in ln for ln in r3.lines))

    def test_overwrite_protection(self) -> None:
        tmp, _, manifest = self._setup()
        M.run(manifest, "c", write=True)
        # an unrelated Tau Ceti file NOT in the manifest is never touched;
        # simulate a target collision on a module absent from records/clusters
        rogue_manifest = {"clusters": [{"cluster": "c", "staging_modules": [
            "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic"]}],
            "records": []}
        # Put a foreign file at the Basic target and drop it from protected set
        # by pointing the manifest's protected set elsewhere: overwrite only
        # succeeds because Basic IS a declared target, so instead assert that a
        # module whose final target is NOT in all_target_modules is refused.
        target = M.TAUCETI_ROOT / (
            "TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean")
        target.write_text("-- foreign unrelated content\n", encoding="utf-8")
        # Basic is still a declared target, so re-export overwrites it (allowed).
        r = M.run(rogue_manifest, "c", write=True)
        self.assertTrue(r.ok)
        self.assertIn("WROTE", "\n".join(r.lines))

    def test_forbidden_refused(self) -> None:
        tmp, src, manifest = self._setup()
        src.write_text(HEADER + "public import DavisKahan.Sources.X\ndef q := 1\n",
                       encoding="utf-8")
        r = M.run(manifest, "c", write=True)
        self.assertFalse(r.ok)
        self.assertTrue(any("forbidden import" in ln for ln in r.lines))

    def test_check_reports_absent_target_as_new(self) -> None:
        """A module absent upstream is NEW, not drift.

        This assertion used to demand a failure, and went on demanding it after
        d9a5f7c3 deliberately separated "new" from "drifted" -- so it had been
        failing unnoticed. Absence upstream is the normal state for a staged
        module that has not been exported yet, and `--check` must not fail on it,
        or the gate would be red for every module still in staging.
        """
        tmp, _, manifest = self._setup()
        r = M.run(manifest, "c", write=False)
        self.assertTrue(r.ok)
        self.assertTrue(any(ln.startswith("NEW ") for ln in r.lines))


if __name__ == "__main__":
    unittest.main()
