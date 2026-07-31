/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Geometry.Angle.OperatorAngleComplex
import DavisKahan.Geometry.Angle.OperatorAngleReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import DavisKahan.SpectralTheory.Complexification.FunctionalCalculus

/-!
# The literal operator angle of Davis--Kahan

The accepted sine theorem uses the positive sine operator directly.  The 1970
paper first defines a Hermitian operator angle and then applies scalar
trigonometric functions to it.  This file restores that literal object without
changing the already verified theorem.

For complex Hilbert spaces the canonical angle is
`arcsin |P_U - P_V|` through continuous functional calculus.  Its spectrum is
contained in `[0, pi / 2]`, and applying sine recovers exactly the accepted
sine operator.  For real Hilbert spaces the literal angle is the same object
on the canonical complexification; this is the construction used elsewhere in
the repository for real operator functional calculus.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The symmetric sine operator is a positive contraction. -/
theorem norm_sinAngleOperatorC_le_one (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorC U V‖ ≤ 1 := by
  rw [norm_sinAngleOperatorC]
  show ‖(U.starProjection - V.starProjection : E →L[ℂ] E)‖ ≤ 1
  rw [Submodule.norm_starProjection_sub_eq_max]
  apply max_le
  · calc
      ‖(1 - V.starProjection) ∘L U.starProjection‖
          ≤ ‖1 - V.starProjection‖ * ‖U.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - V.starProjection : E →L[ℂ] E) = Vᗮ.starProjection from
          (Submodule.starProjection_orthogonal' V).symm]
        exact mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  · calc
      ‖(1 - U.starProjection) ∘L V.starProjection‖
          ≤ ‖1 - U.starProjection‖ * ‖V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        rw [show (1 - U.starProjection : E →L[ℂ] E) = Uᗮ.starProjection from
          (Submodule.starProjection_orthogonal' U).symm]
        exact mul_le_mul Uᗮ.starProjection_norm_le V.starProjection_norm_le
          (norm_nonneg _) zero_le_one
      _ = 1 := by ring

/-- The real spectrum of the positive sine operator lies in `[0,1]`. -/
theorem spectrum_sinAngleOperatorC_subset_Icc (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (sinAngleOperatorC U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg (sinAngleOperatorC_nonneg U V) hx, ?_⟩
  have habs : |x| ≤ ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hx
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  refine le_trans (le_abs_self x) (habs.trans ?_)
  calc ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ ≤ 1 * 1 :=
        mul_le_mul (norm_sinAngleOperatorC_le_one U V) hone (norm_nonneg _)
          zero_le_one
    _ = 1 := by ring

/-- The literal Hermitian operator angle between two closed complex subspaces. -/
noncomputable def paperAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.arcsin (sinAngleOperatorC U V)

/-- The literal operator angle is self-adjoint. -/
theorem isSelfAdjoint_paperAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (paperAngleOperatorC U V) := by
  exact cfc_predicate Real.arcsin (sinAngleOperatorC U V)

/-- The literal operator angle is nonnegative. -/
theorem paperAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ paperAngleOperatorC U V := by
  apply cfc_nonneg
  intro x hx
  exact Real.arcsin_nonneg.mpr
    ((spectrum_sinAngleOperatorC_subset_Icc U V hx).1)

/-- Applying sine by functional calculus recovers the accepted sine operator
exactly, not merely an operator with the same norm. -/
theorem cfc_sin_paperAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (paperAngleOperatorC U V) = sinAngleOperatorC U V := by
  have hsa : IsSelfAdjoint (sinAngleOperatorC U V) :=
    isSelfAdjoint_sinAngleOperatorC U V
  have harcsin : ContinuousOn Real.arcsin
      (spectrum ℝ (sinAngleOperatorC U V)) :=
    Real.continuous_arcsin.continuousOn
  have hsin : ContinuousOn Real.sin
      (Real.arcsin '' spectrum ℝ (sinAngleOperatorC U V)) :=
    Real.continuous_sin.continuousOn
  rw [paperAngleOperatorC,
    ← cfc_comp Real.sin Real.arcsin (sinAngleOperatorC U V)
      hsa hsin harcsin]
  calc
    cfc (Real.sin ∘ Real.arcsin) (sinAngleOperatorC U V)
        = cfc (fun x : ℝ => x) (sinAngleOperatorC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_sinAngleOperatorC_subset_Icc U V hx
      exact Real.sin_arcsin (by linarith [hxi.1]) (by linarith [hxi.2])
    _ = sinAngleOperatorC U V := cfc_id' ℝ _

/-- The paper's notation `sin Theta` interpreted literally by applying sine to
the Hermitian angle. -/
noncomputable def paperSinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.sin (paperAngleOperatorC U V)

/-- The paper's complex sine-angle operator agrees with the canonical one. -/
@[simp]
theorem paperSinAngleOperatorC_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSinAngleOperatorC U V = sinAngleOperatorC U V :=
  cfc_sin_paperAngleOperatorC U V

/-- The paper's literal cosine of the angle. -/
noncomputable def paperCosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.cos (paperAngleOperatorC U V)

/-- The literal angle has spectrum in the canonical interval. -/
theorem spectrum_paperAngleOperatorC_subset_Icc (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperAngleOperatorC U V) ⊆ Set.Icc 0 (Real.pi / 2) := by
  intro y hy
  rw [paperAngleOperatorC,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := sinAngleOperatorC U V) (isSelfAdjoint_sinAngleOperatorC U V)
      Real.continuous_arcsin.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_sinAngleOperatorC_subset_Icc U V hx
  exact ⟨Real.arcsin_nonneg.mpr hxi.1,
    Real.arcsin_le_pi_div_two x⟩

/-- Functional-calculus Pythagoras for the literal angle. -/
theorem paperSin_sq_add_paperCos_sq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSinAngleOperatorC U V * paperSinAngleOperatorC U V +
      paperCosAngleOperatorC U V * paperCosAngleOperatorC U V =
        ContinuousLinearMap.id ℂ E := by
  rw [paperSinAngleOperatorC, paperCosAngleOperatorC,
    ← cfc_mul Real.sin Real.sin (paperAngleOperatorC U V)
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn,
    ← cfc_mul Real.cos Real.cos (paperAngleOperatorC U V)
      Real.continuous_cos.continuousOn Real.continuous_cos.continuousOn,
    ← cfc_add (a := paperAngleOperatorC U V)
      (fun x : ℝ => Real.sin x * Real.sin x)
      (fun x : ℝ => Real.cos x * Real.cos x)
      ((Real.continuous_sin.mul Real.continuous_sin).continuousOn)
      ((Real.continuous_cos.mul Real.continuous_cos).continuousOn)]
  calc
    cfc (fun x : ℝ => Real.sin x * Real.sin x +
        Real.cos x * Real.cos x) (paperAngleOperatorC U V)
        = cfc (fun _ : ℝ => 1) (paperAngleOperatorC U V) := by
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    _ = ContinuousLinearMap.id ℂ E := by
      have ha : IsSelfAdjoint (paperAngleOperatorC U V) :=
        isSelfAdjoint_paperAngleOperatorC U V
      exact cfc_const_one ℝ _

section Real

open TauCeti.DavisKahan.Experimental.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification
open TauCeti.DavisKahanExt.Real

variable {ER : Type*} [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
  [CompleteSpace ER]

/-! The real algebra structure and the real continuous functional calculus on the
complexified operator algebra are `scoped instance`s of
`RealComplexificationFunctionalCalculus`, opened below.  They used to be reinstalled
here as a second `local instance`, which made them a *different declaration* from the
one the imported lemmas are stated against; see lane `{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.DavisKahan.Experimental.ExactSinTheta.RealComplexificationFunctionalCalculus

/-- The literal real operator angle, represented canonically on the
complexification. -/
noncomputable def paperAngleOperatorRC (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification ER →L[ℂ] RealComplexification ER :=
  paperAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Applying sine to the real angle recovers the complexification of the real
projection-difference sine operator. -/
theorem cfc_sin_paperAngleOperatorRC (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (paperAngleOperatorRC U V) = sinAngleOperatorRC U V :=
  cfc_sin_paperAngleOperatorC _ _

/-- The real angle has the same canonical spectral interval. -/
theorem spectrum_paperAngleOperatorRC_subset_Icc (U V : Submodule ℝ ER)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperAngleOperatorRC U V) ⊆ Set.Icc 0 (Real.pi / 2) :=
  spectrum_paperAngleOperatorC_subset_Icc _ _

end Real

end

end DavisKahanExt
end TauCeti