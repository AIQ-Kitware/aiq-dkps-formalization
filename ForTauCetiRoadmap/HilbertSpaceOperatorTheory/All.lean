/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.HilbertSpaceOperatorFoundations.Suggested
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.MajorizationAndAngles.Suggested
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.SelfAdjointSpectralTheory.Suggested
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.OperatorIdeals.Suggested
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.MatrixSpectralStatistics.Suggested
import ForTauCetiRoadmap.HilbertSpaceOperatorTheory.SpectralSubspacePerturbation.Suggested

/-!
# Compile check for the Hilbert-space operator theory suggested signatures

This file is a convenience import, not a roadmap and not a mathematical development of its
own. Importing it asks Lean to elaborate every `Suggested.lean` file in the roadmap family
under one target. The signatures are the content being checked; their `sorry` bodies are
placeholders and do not establish the proposed theorems.

From the repository root, compile this file directly with:

```sh
lake env lean ForTauCetiRoadmap/HilbertSpaceOperatorTheory/All.lean
```

If the project exposes modules as Lake build targets, the module name is:

```sh
lake build ForTauCetiRoadmap.HilbertSpaceOperatorTheory.All
```
-/
