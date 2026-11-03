/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
public import DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-!
# Examples of normalized Fan-dominant norms

The finite Ky Fan gauges inhabit `NormalizedUnitaryInvariantNorm`. They are
finite on every bounded operator, and supply the intermediate tests used to
transfer estimates to the weaker `NormalizedSymmetricOperatorIdealFamily`.
The latter transfer requires both displayed norms to exist and does not infer
membership for its input norm family.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **The `k`-th Ky Fan norm as a member of the source norm class.** -/
noncomputable def kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k) :
    NormalizedUnitaryInvariantNorm.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := (show TauCeti.SymmetricOperatorIdealFamily 𝕜 from
    { toOperatorIdealFamily := OperatorIdealFamily.kyFan 𝕜 k hk
      gauge_adjoint := (OperatorIdealFamily.kyFan 𝕜 k hk).gauge_adjoint })
  isKyFanDominant := inferInstanceAs (OperatorIdealFamily.kyFan 𝕜 k hk).IsKyFanDominant
  gauge_rankOne_eq_one := by
    intro E F _ _ _ _ _ _ V hVnorm hVrank
    simp only [SymmetricOperatorIdealFamily.gaugeReal, OperatorIdealFamily.gauge_kyFan,
      ENNReal.coe_toReal]
    have hsum : (V.kyFanGauge k : ℝ)
        = ∑ n ∈ Finset.range k, (V.singularValue n : ℝ) := by
      rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
    rw [hsum]
    have hval : ∀ n ∈ Finset.range k,
        (V.singularValue n : ℝ) = if n = 0 then 1 else 0 := fun n _ =>
      SymmetricNormingFunction.approximationSingularValue_rankOne hVnorm hVrank n
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ))]
    simp [hk]

/-- The gauge of the Ky Fan member is the Ky Fan gauge, definitionally. -/
@[simp]
theorem gauge_kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).gauge A
      = (A.kyFanGauge k : ℝ) :=
  by
    change ((OperatorIdealFamily.kyFan 𝕜 k hk).gauge A).toReal = _
    rw [OperatorIdealFamily.gauge_kyFan, ENNReal.coe_toReal]

/-- Every bounded operator lies in the Ky Fan member's ideal. -/
theorem mem_kyFanNormalizedUnitaryInvariantNorm
     (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).Mem A :=
  by
    change (OperatorIdealFamily.kyFan 𝕜 k hk).gauge A ≠ ⊤
    simp

/-- **The source norm class is inhabited over `ℂ`.**  So every source-exact
façade quantifying over `NormalizedUnitaryInvariantNorm ℂ` says something. -/
theorem nonempty_normalizedUnitaryInvariantNorm_complex :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℂ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 one_pos⟩

/-- **The source norm class is inhabited over `ℝ`.** -/
theorem nonempty_normalizedUnitaryInvariantNorm_real :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℝ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℝ) 1 one_pos⟩

end

end ExactSinTheta
end DavisKahan
end TauCeti
