/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.OperatorIdeal.ApproximationNumbers.Core
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import TauCeti.Analysis.OperatorIdeal.Family.KyFan.Dominance
public import TauCeti.Analysis.OperatorIdeal.Family.Modulus

/-!
# Scalar-generic ideal estimates from Ky Fan gauges

Ideal comparisons use accepted
`SymmetricOperatorIdealFamily` carriers with the native
`OperatorIdealFamily.IsKyFanDominant` property. Analytic kernels request ideal
completeness separately. Real estimates use `SymmetricOperatorIdealFamily.gaugeReal`.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Finite Ky Fan majorization transfers finite ideal membership and the real gauge bound. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} (hB : N.Mem B)
    (h : ∀ k, (A.kyFanGauge k : ℝ) ≤ (B.kyFanGauge k : ℝ)) :
    N.Mem A ∧ N.gaugeReal A ≤ N.gaugeReal B := by
  have hle : N.gauge A ≤ N.gauge B := by
    apply OperatorIdealFamily.gauge_le_of_forall_kyFanGauge_le
    intro k
    exact_mod_cast h k
  exact ⟨ne_top_of_le_ne_top hB hle, ENNReal.toReal_mono hB hle⟩

/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.Mem B)
    (h : ∀ k, δ * (A.kyFanGauge k : ℝ) ≤
      (B.kyFanGauge k : ℝ)) :
    N.Mem A ∧
      δ * N.gaugeReal A ≤
        N.gaugeReal B := by
  let d : 𝕜 := (δ : 𝕜)
  have hd : d ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  have hdnorm : ‖d‖ = δ := by
    simp [d, abs_of_pos hδ]
  have hscaled : ∀ k,
      ((d • A).kyFanGauge k : ℝ) ≤
        (B.kyFanGauge k : ℝ) := by
    intro k
    rw [ContinuousLinearMap.kyFanGauge_smul, NNReal.coe_mul, coe_nnNorm, hdnorm]
    exact h k
  obtain ⟨hdA, hgauge⟩ := mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hB hscaled
  have hA : N.Mem A := by
    have hinv := N.smul_mem d⁻¹ hdA
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul] at hinv
    exact hinv
  refine ⟨hA, ?_⟩
  have hhom : N.gaugeReal (d • A) = ‖d‖ * N.gaugeReal A :=
    N.gaugeReal_smul d hA
  rw [hdnorm] at hhom
  linarith

end ExactSinTheta
end DavisKahan
end TauCeti
