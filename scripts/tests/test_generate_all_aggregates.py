"""Regression tests for `scripts/generate_all_aggregates.py`.

Both cases here pin a failure the generator actually exhibited on 2026-07-29,
and neither would have been caught by a build:

* a **cross-library re-export must survive regeneration**.  Since the Tau Ceti
  migration an aggregate legitimately imports modules that no longer live under
  `DavisKahan/` -- when a module moves to `ForTauCeti`, its import is repointed
  in place so the aggregate keeps reaching the same mathematics.  The generator
  derived its import list purely from the directory listing, so it deleted every
  such line: 21 imports across 9 aggregates.  Nothing downstream reports this,
  because an aggregate that imports *less* still compiles;

* **`--help` must not write.**  The entry point tested `"--check" in sys.argv`,
  so any unrecognised argument was simply "not a check" and fell through to the
  write path.  Asking this tool for its usage rewrote 21 aggregates.

A third case pins the behaviour that keeps the second fix honest: a preserved
re-export whose target file has disappeared is reported and dropped, so a
deleted module cannot hide behind the preservation rule.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "generate_all_aggregates.py"


def load_module(root: Path):
    """Import the generator with its ROOT/BASE rebound at `root`."""
    spec = importlib.util.spec_from_file_location("gen_all_aggregates", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = root
    module.BASE = root / "DavisKahan"
    return module


HEADER = """/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
"""


class GenerateAllAggregatesTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def write(self, rel: str, text: str = "-- module\n") -> Path:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_cross_library_reexport_is_preserved(self) -> None:
        """A migrated module's `ForTauCeti` import must survive regeneration."""
        self.write("DavisKahan/Core/Local.lean")
        # the migrated module: it no longer lives under DavisKahan/, but the
        # aggregate still re-exports it, and the file it names does exist
        self.write("ForTauCeti/Analysis/Migrated.lean")
        self.write(
            "DavisKahan/Core/All.lean",
            HEADER
            + "import ForTauCeti.Analysis.Migrated\n"
            + "import DavisKahan.Core.Local\n"
            + "\n/-! # `DavisKahan/Core` -/\n",
        )

        module = load_module(self.root)
        dangling: list[str] = []
        module.regenerate(self.root / "DavisKahan" / "Core", False, dangling)

        text = (self.root / "DavisKahan/Core/All.lean").read_text()
        self.assertIn("import ForTauCeti.Analysis.Migrated", text)
        self.assertIn("import DavisKahan.Core.Local", text)
        self.assertEqual(dangling, [])

    def test_reexports_sort_by_leaf_name(self) -> None:
        """A re-export keeps the slot of the module it replaced."""
        self.write("DavisKahan/Core/Beta.lean")
        self.write("ForTauCeti/Analysis/Alpha.lean")
        self.write("ForTauCeti/Analysis/Gamma.lean")
        self.write(
            "DavisKahan/Core/All.lean",
            HEADER
            + "import ForTauCeti.Analysis.Alpha\n"
            + "import ForTauCeti.Analysis.Gamma\n"
            + "\n/-! # `DavisKahan/Core` -/\n",
        )

        module = load_module(self.root)
        module.regenerate(self.root / "DavisKahan" / "Core", False, [])

        lines = [ln for ln in (self.root / "DavisKahan/Core/All.lean")
                 .read_text().splitlines() if ln.startswith("import ")]
        self.assertEqual(
            lines,
            [
                "import ForTauCeti.Analysis.Alpha",
                "import DavisKahan.Core.Beta",
                "import ForTauCeti.Analysis.Gamma",
            ],
        )

    def test_dangling_reexport_is_reported_not_copied(self) -> None:
        """A re-export naming a deleted file is dropped and reported."""
        self.write("DavisKahan/Core/Local.lean")
        self.write(
            "DavisKahan/Core/All.lean",
            HEADER
            + "import ForTauCeti.Analysis.Deleted\n"
            + "import DavisKahan.Core.Local\n"
            + "\n/-! # `DavisKahan/Core` -/\n",
        )

        module = load_module(self.root)
        dangling: list[str] = []
        module.regenerate(self.root / "DavisKahan" / "Core", False, dangling)

        text = (self.root / "DavisKahan/Core/All.lean").read_text()
        self.assertNotIn("Deleted", text)
        self.assertEqual(len(dangling), 1)
        self.assertIn("ForTauCeti.Analysis.Deleted", dangling[0])

    def test_help_does_not_write(self) -> None:
        """`--help` must print usage, not take the write path."""
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--help"],
            capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(result.returncode, 0)
        self.assertIn("--check", result.stdout)
        self.assertNotIn("regenerated", result.stdout)

    def test_unknown_flag_is_rejected(self) -> None:
        """An unrecognised argument must fail, not fall through to writing."""
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--bogus"],
            capture_output=True, text=True, timeout=120,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("regenerated", result.stdout)


if __name__ == "__main__":
    unittest.main()
