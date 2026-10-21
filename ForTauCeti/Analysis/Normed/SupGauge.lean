/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-! # The supremum gauge endpoint

Tau Ceti supplies the supremum symmetric gauge and proves its extension formula. This file keeps
only the antitone-sequence specialization used by the DKPS Schatten-family presentation.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

/-- On an antitone sequence the supremum gauge is its leading coordinate. -/
theorem supGauge_extend_of_antitone {a : ℕ → ENNReal} (ha : Antitone a) :
    SymmetricGauge.supGauge.extend a = a 0 := by
  rw [SymmetricGauge.extend_supGauge]
  exact le_antisymm (iSup_le fun n => ha (Nat.zero_le n)) (le_iSup a 0)

end TauCeti
