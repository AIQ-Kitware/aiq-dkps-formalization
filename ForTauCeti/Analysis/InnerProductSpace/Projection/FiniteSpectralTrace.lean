/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining

/-!
# Spectral traces of directed principal sines

Functional calculus with a symbol vanishing at zero commutes with compression
by a reducing orthogonal projection. Applied to `|P_U-P_V|`, its directed
spectral trace is the sum over the accepted principal sines.
These are classical finite-dimensional identities, including zero angles.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A zero-preserving symbol commutes with multiplication by a reducing
orthogonal projection in finite dimension. No global continuity of the
symbol is needed because the spectra are finite. -/
theorem cfc_mul_projection_of_commute
    (f : ℂ → ℂ) (hf : f 0 = 0) (T P : E →L[ℂ] E)
    (hT : IsSelfAdjoint T) (hP : IsStarProjection P) (hTP : Commute T P) :
    cfc f (T * P) = cfc f T * P := by
  have hself : IsSelfAdjoint (T * P) := by
    change star (T * P) = T * P
    rw [star_mul, hT.star_eq, hP.isSelfAdjoint.star_eq]
    exact hTP.eq.symm
  have hcompress : P * (T * P) = T * P := by
    rw [← mul_assoc, ← hTP.eq, mul_assoc, hP.isIdempotentElem.eq]
  have hkill : (1 - P) * (T * P) = 0 * (1 - P) := by
    rw [sub_mul, one_mul, hcompress, sub_self, zero_mul]
  have hcontinuous := ((T * P).finite_spectrum ℂ).continuousOn f
  have h1 : P * cfc f (T * P) = cfc f T * P :=
    P.comp_cfc_eq_cfc_comp hcompress
      (by rw [hself.star_eq, hT.star_eq]; exact hcompress) f
      hcontinuous ((T.finite_spectrum ℂ).continuousOn f)
      hself.isStarNormal hT.isStarNormal
  have h0 : (1 - P) * cfc f (T * P) = 0 := by
    have h := (1 - P).comp_cfc_eq_cfc_comp hkill
      (by rw [hself.star_eq, star_zero]; exact hkill) f
      hcontinuous
      (((0 : E →L[ℂ] E).finite_spectrum ℂ).continuousOn f)
      hself.isStarNormal (IsSelfAdjoint.zero (R := E →L[ℂ] E)).isStarNormal
    change (1 - P) * cfc f (T * P) = cfc f (0 : E →L[ℂ] E) * (1 - P) at h
    simpa only [cfc_apply_zero, hf, map_zero, zero_mul] using h
  have hsum : P + (1 - P) = (1 : E →L[ℂ] E) := add_sub_cancel _ _
  calc
    cfc f (T * P) = (P + (1 - P)) * cfc f (T * P) := by rw [hsum, one_mul]
    _ = cfc f T * P := by rw [add_mul, h1, h0, add_zero]

/-- The trace of a function of a positive map is the sum of that function
of its singular values, including the zero values. -/
theorem re_trace_cfc_eq_sum_singularValues_of_positive
    (f : ℝ → ℝ) (T : E →L[ℂ] E) (hT : T.IsPositive) :
    (LinearMap.trace ℂ E (cfc (fun z : ℂ => (f z.re : ℂ)) T).toLinearMap).re =
      ∑ i : Fin (Module.finrank ℂ E), f (T.toLinearMap.singularValues i) := by
  let : IsStarNormal T := hT.isSelfAdjoint.isStarNormal
  let e := hT.toLinearMap.isSymmetric.eigenvectorBasis rfl
  let mu := hT.toLinearMap.isSymmetric.eigenvalues rfl
  have he (i) : T (e i) = (mu i : ℂ) • e i :=
    hT.toLinearMap.isSymmetric.apply_eigenvectorBasis rfl i
  rw [ContinuousLinearMap.re_trace_cfc_eq_sum (fun z : ℂ => f z.re) T e
    (fun i => (mu i : ℂ)) he,
    sum_singularValues_eq_sum_norm_eigenvalues e T.toLinearMap
      (fun i => (mu i : ℂ)) he f]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hT.toLinearMap.nonneg_eigenvalues rfl i)]

/-- A reflection-swapped eigenbasis counts each nonzero spectral pair
once in the source-directed trace. The fixed space contributes zero for
a zero-preserving symbol. -/
theorem re_trace_cfc_mul_projection_of_paired_eigenbasis
    (U : Submodule ℂ E) (S : E →L[ℂ] E) [IsStarNormal S]
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (mu : Fin n → ℝ)
    (hS0 : ∀ i, S (e (.inl (0, i))) = (mu i : ℂ) • e (.inl (0, i)))
    (hS1 : ∀ i, S (e (.inl (1, i))) = (mu i : ℂ) • e (.inl (1, i)))
    (hSf : ∀ j, S (e (.inr j)) = 0)
    (hJ0 : ∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (LinearMap.trace ℂ E
      (cfc (fun z : ℂ => (f z.re : ℂ)) S * U.starProjection).toLinearMap).re =
        ∑ i, f (mu i) := by
  have hPinner (x : E) (hxx : ⟪x, x⟫_ℂ = 1)
      (hJx : ⟪x, U.reflection x⟫_ℂ = 0) :
      ⟪x, U.starProjection x⟫_ℂ = ((1 / 2 : ℝ) : ℂ) := by
    have h := congrArg (fun y => ⟪x, y⟫_ℂ) (Submodule.reflection_apply (K := U) x)
    rw [hJx, inner_sub_right, two_smul, inner_add_right, hxx] at h
    push_cast
    linear_combination -(1 / 2 : ℂ) * h
  have hJ1 (i) : U.reflection (e (.inl (1, i))) = e (.inl (0, i)) := by
    rw [← hJ0 i, U.reflection_reflection]
  have hdiag (x : E) (r : ℝ) (hSx : S x = (r : ℂ) • x)
      (hx : ⟪x, U.starProjection x⟫_ℂ = ((1 / 2 : ℝ) : ℂ)) :
      (⟪x, (U.starProjection * cfc (fun z : ℂ => (f z.re : ℂ)) S) x⟫_ℂ).re = f r / 2 := by
    change (⟪x, U.starProjection (cfc (fun z : ℂ => (f z.re : ℂ)) S x)⟫_ℂ).re = _
    rw [ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hSx,
      Complex.ofReal_re, map_smul, inner_smul_right, hx, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have h0 (i) := hdiag _ _ (hS0 i) (hPinner _ (e.inner_eq_one _) (by
    rw [hJ0]
    exact e.inner_eq_zero (by simp)))
  have h1 (i) := hdiag _ _ (hS1 i) (hPinner _ (e.inner_eq_one _) (by
    rw [hJ1]
    exact e.inner_eq_zero (by simp)))
  have hfixed (j) :
      (⟪e (.inr j),
        (U.starProjection * cfc (fun z : ℂ => (f z.re : ℂ)) S) (e (.inr j))⟫_ℂ).re = 0 := by
    change (⟪e (.inr j),
      U.starProjection (cfc (fun z : ℂ => (f z.re : ℂ)) S (e (.inr j)))⟫_ℂ).re = 0
    rw [ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _
      (show S (e (.inr j)) = (0 : ℂ) • e (.inr j) by rw [hSf, zero_smul])]
    simp [hf]
  have hcyclic :
      LinearMap.trace ℂ E (cfc (fun z : ℂ => (f z.re : ℂ)) S * U.starProjection).toLinearMap =
        LinearMap.trace ℂ E (U.starProjection * cfc (fun z : ℂ => (f z.re : ℂ)) S).toLinearMap :=
    LinearMap.trace_mul_comm ℂ _ _
  rw [hcyclic, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [ContinuousLinearMap.coe_coe, h0, h1, hfixed, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end TauCeti

namespace Submodule

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The source-directed spectral trace of the symmetric sine operator is
the sum of the same symbol over the principal sines. Unequal subspace ranks
and zero principal sines are permitted. -/
theorem re_trace_cfc_sinAngleOperator_mul_starProjection
    (U V : Submodule ℂ E) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (LinearMap.trace ℂ E
      (cfc (fun z : ℂ => (f z.re : ℂ)) (U.sinAngleOperator V) * U.starProjection).toLinearMap).re =
        ∑ i : Fin (Module.finrank ℂ U), f (U.principalSines V i) := by
  let S := U.sinAngleOperator V
  let P := U.starProjection
  let A := U.sinThetaMap V
  have hSP : S * P = A.modulus := U.sinAngleOperator_mul_starProjection V
  have hpos : (S * P).IsPositive := by rw [hSP]; exact A.isPositive_modulus
  have hσ : (S * P).toLinearMap.singularValues = A.toLinearMap.singularValues := by
    apply LinearMap.singularValues_eq_of_norm_apply_eq
    intro x
    change ‖(S * P) x‖ = ‖A x‖
    rw [hSP, ContinuousLinearMap.norm_modulus_apply]
  let X : U →L[ℂ] E := U.subtypeL
  let AX := Vᗮ.starProjection ∘L X
  have hσX : U.principalSines V = AX.toLinearMap.singularValues := by
    have h := Submodule.principalSines_range_eq_singularValues
      (X := X) V U.subtypeₗᵢ.isometry
    have hRange : X.range = U := Submodule.range_subtype U
    simpa only [hRange] using h
  rw [← TauCeti.cfc_mul_projection_of_commute (fun z : ℂ => (f z.re : ℂ))
      (by simp [hf]) S P (U.isPositive_sinAngleOperator V).isSelfAdjoint
      isStarProjection_starProjection (U.commute_starProjection_sinAngleOperator V).symm,
    TauCeti.re_trace_cfc_eq_sum_singularValues_of_positive f (S * P) hpos, hσ,
    A.toLinearMap.sum_fin_singularValues f hf,
    ← Submodule.principalSines_def, hσX,
    ← AX.toLinearMap.sum_fin_singularValues f hf]

end Submodule
