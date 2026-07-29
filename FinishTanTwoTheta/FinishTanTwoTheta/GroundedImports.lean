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
pinned Mathlib and Spectra leaves used explicitly by `FinishTanTwoTheta`.
Every nonlocal declaration used by the finishing library is recorded in
`GROUNDING.md`; genuinely new results are declared locally in this library.
-/
