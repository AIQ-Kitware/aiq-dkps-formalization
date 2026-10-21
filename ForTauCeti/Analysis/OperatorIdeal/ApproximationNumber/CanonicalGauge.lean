/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-! # Real view of the canonical Ky Fan gauge -/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The maintained real approximation number is the real coercion of Tau Ceti's canonical
nonnegative singular value. -/
theorem approximationNumber_eq_singularValue_toReal (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n = (T.singularValue n).toReal := by
  rw [T.approximationNumber_eq_iInf, T.singularValue_def, NNReal.coe_iInf]
  simp only [coe_nnnorm]

/-- The real-valued gauge used by Davis--Kahan estimates is the real coercion of Tau Ceti's
canonical `ℝ≥0` Ky Fan gauge. -/
@[expose]
noncomputable def kyFanGaugeReal (T : E →L[𝕜] F) (k : ℕ) : ℝ :=
  (T.kyFanGauge k).toReal

/-- The first real-valued Ky Fan gauge is the operator norm. -/
@[simp] theorem kyFanGaugeReal_one (T : E →L[𝕜] F) :
    T.kyFanGaugeReal 1 = ‖T‖ := by
  simp [kyFanGaugeReal]

/-- The real gauge is the sum of the repository's real approximation numbers. -/
@[simp] theorem kyFanGaugeReal_eq_sum (T : E →L[𝕜] F) (k : ℕ) :
    T.kyFanGaugeReal k = ∑ n ∈ Finset.range k, T.approximationNumber n := by
  rw [kyFanGaugeReal, T.kyFanGauge_def, NNReal.coe_sum]
  simp_rw [approximationNumber_eq_singularValue_toReal]

end ContinuousLinearMap
