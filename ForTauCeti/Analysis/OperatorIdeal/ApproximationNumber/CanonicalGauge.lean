/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

/-! # Real scalar consequences of canonical singular values and Ky Fan gauges -/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The first real-valued Ky Fan gauge is the operator norm. -/
@[simp] theorem kyFanGaugeReal_one (T : E →L[𝕜] F) :
    (T.kyFanGauge 1 : ℝ) = ‖T‖ := by
  simp

/-- The real coercion of the native gauge is the sum of the real singular values. -/
@[simp] theorem kyFanGaugeReal_eq_sum (T : E →L[𝕜] F) (k : ℕ) :
    (T.kyFanGauge k : ℝ) = ∑ n ∈ Finset.range k, (T.singularValue n : ℝ) := by
  rw [T.kyFanGauge_def, NNReal.coe_sum]


/-- Read equality of the real approximation numbers from the canonical sequence. -/
theorem SameSingularValues.approximationNumber_eq {G H : Type*}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    {S : E →L[𝕜] F} {T : G →L[𝕜] H} (h : S.SameSingularValues T) (n : ℕ) :
    (S.singularValue n : ℝ) = (T.singularValue n : ℝ) := by
  exact congrArg NNReal.toReal ((sameSingularValues_iff _ _).mp h n)

/-- Equal canonical singular-value sequences give equal real Ky Fan gauges. -/
theorem SameSingularValues.kyFanGaugeReal_eq {G H : Type*}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    {S : E →L[𝕜] F} {T : G →L[𝕜] H} (h : S.SameSingularValues T) (k : ℕ) :
    (S.kyFanGauge k : ℝ) = (T.kyFanGauge k : ℝ) :=
  congrArg NNReal.toReal (h.kyFanGauge_eq k)

end ContinuousLinearMap
