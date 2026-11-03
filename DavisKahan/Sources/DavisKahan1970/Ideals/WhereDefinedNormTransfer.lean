/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module

public import DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
public import DavisKahan.Sources.DavisKahan1970.Ideals.NormalizedUnitaryInvariantNormExamples

/-!
# Inequalities at the where-defined norm boundary

An estimate valid at every finite Ky Fan norm holds in a normalized symmetric
operator-ideal family whenever both displayed norms exist. This does not infer
ideal membership from majorization. The older unconditional Fan-dominant
endpoints remain useful proof APIs: their Ky Fan instances supply precisely the
estimates needed here.
-/

public section

namespace TauCeti.DavisKahan1970

open TauCeti.DavisKahan.ExactSinTheta
open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F E' F' : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']

/-- Transfer a uniform stronger-norm estimate to a comparison where both norms exist. -/
theorem whereDefinedUIN_of_normalizedUnitaryInvariant
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'} {d : ℝ} (hd : 0 < d)
    (h : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.ScaledGaugeLEWhereDefined d X Y := by
  apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le hd
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ContinuousLinearMap.kyFanGauge_zero, NNReal.coe_zero, mul_zero]
    exact le_rfl
  · have hle := (h (kyFanNormalizedUnitaryInvariantNorm k hk)
      (mem_kyFanNormalizedUnitaryInvariantNorm k hk Y)).2
    simpa only [gauge_kyFanNormalizedUnitaryInvariantNorm] using hle

/-- The same transfer with a positive constant multiplying the right-hand norm. -/
theorem whereDefinedUIN_of_normalizedUnitaryInvariant_mul
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'} {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c)
    (h : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ c * M.gauge Y) :
    N.Mem X → N.Mem Y → d * N.gaugeReal X ≤ c * N.gaugeReal Y := by
  have hscaled : N.ScaledGaugeLEWhereDefined (d / c) X Y :=
    whereDefinedUIN_of_normalizedUnitaryInvariant N (div_pos hd hc) fun M hM => by
      obtain ⟨hmem, hle⟩ := h M hM
      refine ⟨hmem, ?_⟩
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]
      simpa only [mul_comm] using hle
  intro hX hY
  have hle := hscaled hX hY
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hle
  simpa only [mul_comm] using hle

/-- Transfer an analytic symmetric-norming-function estimate without membership transfer. -/
theorem whereDefinedUIN_of_symmetricNorming
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'} {d : ℝ} (hd : 0 < d)
    (h : ∀ M : SymmetricNormingFunction,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.ScaledGaugeLEWhereDefined d X Y := by
  apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le hd
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ContinuousLinearMap.kyFanGauge_zero, NNReal.coe_zero, mul_zero]
    exact le_rfl
  · have hle := (h (kyFanNormingFunction k hk) (kyFanNormingFunction_mem k hk Y)).2
    simpa only [kyFanNormingFunction_gauge] using hle

/-- Symmetric-norming transfer with a positive constant on the right. -/
theorem whereDefinedUIN_of_symmetricNorming_mul
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'} {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c)
    (h : ∀ M : SymmetricNormingFunction,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ c * M.gauge Y) :
    N.Mem X → N.Mem Y → d * N.gaugeReal X ≤ c * N.gaugeReal Y := by
  have hscaled : N.ScaledGaugeLEWhereDefined (d / c) X Y :=
    whereDefinedUIN_of_symmetricNorming N (div_pos hd hc) fun M hM => by
      obtain ⟨hmem, hle⟩ := h M hM
      refine ⟨hmem, ?_⟩
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]
      simpa only [mul_comm] using hle
  intro hX hY
  have hle := hscaled hX hY
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hle
  simpa only [mul_comm] using hle

/-- Uniform where-defined hypotheses imply each stronger-norm comparison.

This uses the hypotheses at the everywhere-defined finite Ky Fan norms. The
membership conclusion belongs to the stronger output norm, not the weak input
family. It is used for Lemma 6.1's universally quantified comparison premises. -/
theorem normalizedUnitaryInvariant_of_all_whereDefinedUIN
    (M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'} {d : ℝ} (hd : 0 < d)
    (h : ∀ N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜,
      N.ScaledGaugeLEWhereDefined d X Y)
    (hY : M.Mem Y) : M.Mem X ∧ d * M.gauge X ≤ M.gauge Y := by
  apply mem_and_scaled_gauge_le_of_all_scaled_kyFan_le M.toSymmetricOperatorIdealFamily hd hY
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ContinuousLinearMap.kyFanGauge_zero, NNReal.coe_zero, mul_zero]
    exact le_rfl
  · let K := kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk
    have hKX : K.toNormalizedSymmetricOperatorIdealFamily.Mem X := by
      exact (K.toNormalizedSymmetricOperatorIdealFamily_mem_iff X).2
        (mem_kyFanNormalizedUnitaryInvariantNorm k hk X)
    have hKY : K.toNormalizedSymmetricOperatorIdealFamily.Mem Y := by
      exact (K.toNormalizedSymmetricOperatorIdealFamily_mem_iff Y).2
        (mem_kyFanNormalizedUnitaryInvariantNorm k hk Y)
    have hle := h K.toNormalizedSymmetricOperatorIdealFamily hKX hKY
    change d * K.toNormalizedSymmetricOperatorIdealFamily.gaugeReal X ≤
      K.toNormalizedSymmetricOperatorIdealFamily.gaugeReal Y at hle
    simpa only [NormalizedUnitaryInvariantNorm.toNormalizedSymmetricOperatorIdealFamily_gaugeReal, K,
      gauge_kyFanNormalizedUnitaryInvariantNorm] using hle

/-- Unscaled form of the uniform-order transfer, for the block-comparison lemmas. -/
theorem normalizedUnitaryInvariant_le_of_all_whereDefinedUIN
    (M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)
    {X : E →L[𝕜] F} {Y : E' →L[𝕜] F'}
    (h : ∀ N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜,
      N.Mem X → N.Mem Y → N.gaugeReal X ≤ N.gaugeReal Y)
    (hY : M.Mem Y) : M.Mem X ∧ M.gauge X ≤ M.gauge Y := by
  obtain ⟨hmem, hle⟩ := normalizedUnitaryInvariant_of_all_whereDefinedUIN M one_pos
    (fun N hX hY => by simpa only [one_mul] using h N hX hY) hY
  exact ⟨hmem, by simpa only [one_mul] using hle⟩

end
end TauCeti.DavisKahan1970
