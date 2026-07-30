/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.All
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Grounded imports for the finishing library

This module deliberately imports the current production aggregate plus the
pinned Mathlib leaves used explicitly by `FinishTanTwoTheta`.

Until 2026-07-30 this also named Spectra leaves.  Spectra is retired and
removed (lane `SPECTRA-FORK`): this module's imports were repointed, the
vendored tree is gone, and `lakefile.toml` no longer requires it.  The
sentence was the last mention of Spectra in this library.
Every nonlocal declaration used by the finishing library is recorded in
`GROUNDING.md`; genuinely new results are declared locally in this library.
-/
