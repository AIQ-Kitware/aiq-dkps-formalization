/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

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

/-- Read equality of the real approximation numbers from the canonical sequence. -/
theorem SameSingularValues.approximationNumber_eq {G H : Type*}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    {S : E →L[𝕜] F} {T : G →L[𝕜] H} (h : S.SameSingularValues T) (n : ℕ) :
    S.approximationNumber n = T.approximationNumber n := by
  rw [approximationNumber_eq_singularValue_toReal, approximationNumber_eq_singularValue_toReal]
  exact congrArg NNReal.toReal ((sameSingularValues_iff _ _).mp h n)

/-- Equal canonical singular-value sequences give equal real Ky Fan gauges. -/
theorem SameSingularValues.kyFanGaugeReal_eq {G H : Type*}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    {S : E →L[𝕜] F} {T : G →L[𝕜] H} (h : S.SameSingularValues T) (k : ℕ) :
    S.kyFanGaugeReal k = T.kyFanGaugeReal k :=
  congrArg NNReal.toReal (h.kyFanGauge_eq k)

end ContinuousLinearMap
