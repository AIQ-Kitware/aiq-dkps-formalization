/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.Real.Sqrt

/-!
# Quantitative rectangular polar estimates

The factor is the accepted `ContinuousLinearMap.polarFactor`. This module retains
the Gram-defect invertibility criterion, the pointwise distance identity, and
the rectangular Gram-perturbation bound. The latter applies the native factor
estimate before comparing the modulus and Gram defects. The former inverse-based
factor and its bundled factories are preserved at `e4637c3919ae` under this path.
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A Gram operator at distance less than one from the identity has invertible modulus. -/
theorem isUnit_modulus_of_norm_adjoint_comp_self_sub_one_lt_one {M : E →L[ℂ] F}
    (h : ‖M.adjoint ∘L M - 1‖ < 1) : IsUnit M.modulus := by
  rw [M.modulus_eq_sqrt, CFC.isUnit_sqrt_iff _
    (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self M))]
  rw [show M.adjoint ∘L M = 1 - -(M.adjoint ∘L M - 1) by abel]
  exact isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])

private theorem injective_of_isUnit_modulus {M : E →L[ℂ] F}
    (hM : IsUnit M.modulus) : Function.Injective M := by
  have hmod : M.modulus.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (ContinuousLinearMap.isUnit_iff_bijective.mp hM).1
  have hker : M.ker = ⊥ := by rw [← M.ker_modulus]; exact hmod
  exact LinearMap.ker_eq_bot.mp hker

/-- The sharp pointwise polar distance identity for a bounded-below rectangular operator. -/
theorem norm_sub_polarFactor_apply_eq_of_isUnit_modulus {M : E →L[ℂ] F}
    (hM : IsUnit M.modulus) (x : E) :
    ‖M x - M.polarFactor x‖ = ‖M.modulus x - x‖ := by
  calc
    ‖M x - M.polarFactor x‖ = ‖M.polarFactor (M.modulus x - x)‖ := by
      rw [map_sub, M.polarFactor_modulus_apply]
    _ = ‖M.modulus x - x‖ :=
      M.norm_polarFactor_apply_of_injective (injective_of_isUnit_modulus hM) _

/-- The modulus is at least as close to the identity as the source Gram operator. -/
theorem norm_modulus_sub_one_le (M : E →L[ℂ] F) :
    ‖M.modulus - 1‖ ≤ ‖M.adjoint ∘L M - 1‖ := by
  set a : E →L[ℂ] E := M.adjoint ∘L M with ha_def
  have ha : 0 ≤ a := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self M)
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  -- Both sides are values of the continuous functional calculus at `a`.
  have hshift : cfc (fun s : ℝ => s - 1) a = a - 1 := by
    rw [cfc_sub (fun s : ℝ => s) (fun _ : ℝ => (1 : ℝ)) a, cfc_id' ℝ a, cfc_const_one ℝ a]
  have hmodsqrt : CFC.sqrt a = M.modulus :=
    M.modulus_eq_sqrt.symm
  have hmod : cfc (fun s : ℝ => Real.sqrt s - 1) a = M.modulus - 1 := by
    rw [cfc_sub Real.sqrt (fun _ : ℝ => (1 : ℝ)) a, cfc_const_one ℝ a]
    congr 1
    calc
      cfc Real.sqrt a = CFC.sqrt a := by
        rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
      _ = M.modulus := hmodsqrt
  rw [← hmod, ← hshift]
  refine norm_cfc_le (norm_nonneg _) fun t ht => ?_
  calc ‖Real.sqrt t - 1‖ = |Real.sqrt t - 1| := Real.norm_eq_abs _
    _ ≤ |t - 1| := Real.abs_sqrt_sub_one_le_abs_sub_one t
    _ = ‖t - 1‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖cfc (fun s : ℝ => s - 1) a‖ := norm_apply_le_norm_cfc (fun s : ℝ => s - 1) a ht

/-- The rectangular polar distance is bounded by the defect of the source Gram operator. -/
theorem norm_sub_polarFactor_le_norm_adjoint_comp_self_sub_one (M : E →L[ℂ] F) :
    ‖M - M.polarFactor‖ ≤ ‖M.adjoint ∘L M - 1‖ := by
  have h : ‖M - M.polarFactor‖ ≤ ‖M.modulus - 1‖ := by
    rw [M.polarFactor_eq_factorThru]
    exact norm_sub_factorThru_le (fun x => (M.norm_modulus_apply x).ge)
  exact h.trans M.norm_modulus_sub_one_le

end ContinuousLinearMap
