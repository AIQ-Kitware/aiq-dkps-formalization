/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseDefectAttainment
import ForTauCeti.Analysis.InnerProductSpace.Projection.KernelSupport

/-!
# Effective phase directions for weighted nuclear and Charbonnier transport

The weight `C * (F - F*)` detects precisely the effective phase parameters.
On positive principal cosines it vanishes exactly at and above `b/a`.
Right-angle directions have zero weight and independent defect parameters.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The coefficient of the projection parameter in the weighted phase formula. -/
def weightedPhaseWeight (a b : ℝ) (C : E →L[ℂ] E) : E →L[ℂ] E :=
  C * (weightedPhaseFactor a b C - star (weightedPhaseFactor a b C))

omit [FiniteDimensional ℂ E] in
/-- Operators commuting with a self-adjoint cosine commute with its phase weight. -/
theorem weightedPhaseWeight_commute
    (a b : ℝ) (C B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (hCB : Commute C B) :
    Commute (weightedPhaseWeight a b C) B := by
  have hF := hC.commute_cfc hCB (weightedPhaseSymbol a b)
  have hFs := hC.commute_cfc hCB (fun z => star (weightedPhaseSymbol a b z))
  rw [cfc_star] at hFs
  exact hCB.mul_left (hF.sub_left hFs)

omit [FiniteDimensional ℂ E] in
/-- The effective phase weight of a self-adjoint cosine is skew-adjoint. -/
theorem star_weightedPhaseWeight (a b : ℝ) (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) :
    star (weightedPhaseWeight a b C) = -weightedPhaseWeight a b C := by
  have hF := hC.commute_cfc (Commute.refl C) (weightedPhaseSymbol a b)
  have hFs := hC.commute_cfc (Commute.refl C) (fun z => star (weightedPhaseSymbol a b z))
  rw [cfc_star] at hFs
  change Commute (weightedPhaseFactor a b C) C at hF
  change Commute (star (weightedPhaseFactor a b C)) C at hFs
  rw [weightedPhaseWeight, star_mul, star_sub, star_star, hC.star_eq]
  change (star (weightedPhaseFactor a b C) - weightedPhaseFactor a b C) * C = _
  rw [(hFs.sub_left hF).eq]
  noncomm_ring

/-- The phase weight has an explicit eigenvalue on every principal cosine. -/
theorem weightedPhaseWeight_apply_smul
    (a b c : ℝ) (hb : 0 < b) (ha : 0 ≤ a) (hc : c ∈ Set.Icc 0 1)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hx : C x = (c : ℂ) • x) :
    weightedPhaseWeight a b C x =
      (((2 * c * Real.sqrt (1 - (min 1 (a * c / b)) ^ 2) : ℝ) : ℂ) * Complex.I) • x := by
  let F := weightedPhaseFactor a b C
  let z := weightedPhaseSymbol a b (c : ℂ)
  have hFx : F x = z • x :=
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hx
  have hz : ‖z‖ = 1 := norm_circlePhase 1 _ zero_le_one
  have hFs := unitary_star_apply_of_apply_eq_smul
    (⟨F, weightedPhaseFactor_mem_unitary a b C inferInstance⟩ : unitary (E →L[ℂ] E))
    z hz x hFx
  change star F x = star z • x at hFs
  have hsymbol := weightedPhaseSymbol_eq_clip a b c hb ha hc
  change z = _ at hsymbol
  change C (F x - star F x) = _
  rw [hFx, hFs, hsymbol, ← sub_smul, map_smul, hx, smul_smul]
  congr 1
  simp only [star_add, star_mul, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- A positive cosine direction is ineffective exactly at or above the
closed canonical threshold. Nonzero vectors are needed to detect it. -/
theorem weightedPhaseWeight_apply_eq_zero_iff
    (a b c : ℝ) (hb : 0 < b) (ha : 0 ≤ a) (hc : c ∈ Set.Ioc 0 1)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hne : x ≠ 0)
    (hx : C x = (c : ℂ) • x) :
    weightedPhaseWeight a b C x = 0 ↔ b ≤ a * c := by
  rw [weightedPhaseWeight_apply_smul a b c hb ha ⟨hc.1.le, hc.2⟩ C x hx,
    smul_eq_zero_iff_left hne, mul_eq_zero, or_iff_left Complex.I_ne_zero,
    Complex.ofReal_eq_zero, mul_eq_zero, or_iff_right (mul_ne_zero (by norm_num) hc.1.ne')]
  by_cases hsub : b ≤ a * c
  · rw [min_eq_left ((le_div_iff₀ hb).mpr (by simpa using hsub))]
    simp [hsub]
  · have hratio : a * c / b < 1 := (div_lt_one hb).mpr (lt_of_not_ge hsub)
    have hnonneg : 0 ≤ a * c / b := div_nonneg (mul_nonneg ha hc.1.le) hb.le
    rw [min_eq_right hratio.le]
    have hpos : 0 < Real.sqrt (1 - (a * c / b) ^ 2) := by
      apply Real.sqrt_pos.mpr
      nlinarith
    exact iff_of_false hpos.ne' hsub

/-- Right-angle cosine directions have zero phase weight. -/
theorem weightedPhaseWeight_apply_zero
    (a b : ℝ) (hb : 0 < b) (ha : 0 ≤ a)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hx : C x = 0) :
    weightedPhaseWeight a b C x = 0 := by
  have h := weightedPhaseWeight_apply_smul a b 0 hb ha ⟨le_rfl, zero_le_one⟩ C x
    (by simpa only [Complex.ofReal_zero, zero_smul] using hx)
  simpa only [mul_zero, zero_mul, Complex.ofReal_zero, zero_smul] using h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
