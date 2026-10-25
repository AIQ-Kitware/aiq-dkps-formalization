/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum
public import ForTauCeti.Analysis.InnerProductSpace.PositiveUnitaryAverage
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Tactic.Module

/-!
# All finite complex unitaries with a prescribed scalar real part

The two possible scalar phases determine an orthogonal spectral projection.
Conversely every orthogonal projection supplies such a unitary. This is the
projection parameter in the supercritical transport optimizer families.
The statement permits arbitrary multiplicities and the zero-dimensional space.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
-- The finite spectral reduction and its CFC projection require the larger
-- elaboration allowance.
/-- A unitary with scalar real part `c` is exactly an arbitrary orthogonal
splitting between the conjugate phases `c ± i s`, when `c²+s²=1`. -/
theorem unitary_add_star_eq_scalar_iff_projection_complex
    (U : unitary (E →L[ℂ] E)) (c s : ℝ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    (U : E →L[ℂ] E) + star (U : E →L[ℂ] E) = (2 * (c : ℂ)) • 1 ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧
        (U : E →L[ℂ] E) = ((c : ℂ) - (s : ℂ) * Complex.I) • 1 +
          (2 * (s : ℂ) * Complex.I) • P := by
  let : IsStarNormal (U : E →L[ℂ] E) :=
    ⟨(Unitary.star_mul_self_of_mem U.property).trans
      (Unitary.mul_star_self_of_mem U.property).symm⟩
  constructor
  · intro hreal
    have hspec : spectrum ℂ (U : E →L[ℂ] E) ⊆
        {(c : ℂ) - (s : ℂ) * Complex.I, (c : ℂ) + (s : ℂ) * Complex.I} := by
      intro mu hmu
      rw [ContinuousLinearMap.spectrum_eq] at hmu
      obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmu).exists_hasEigenvector
      have hu : (U : E →L[ℂ] E) x = mu • x := hx.apply_eq_smul
      have hnorm : ‖mu‖ = 1 := by
        have hn := ContinuousLinearMap.norm_map_of_mem_unitary U.property x
        rw [hu, norm_smul] at hn
        exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx.2) (by simpa using hn)
      have hmod : star mu * mu = 1 := by
        rw [RCLike.star_def, RCLike.conj_mul, hnorm]
        norm_num
      have hstar : star (U : E →L[ℂ] E) x = star mu • x := by
        apply (Unitary.linearIsometryEquiv U).injective
        change (U : E →L[ℂ] E) (star (U : E →L[ℂ] E) x) =
          (U : E →L[ℂ] E) (star mu • x)
        calc
          _ = x := congrArg (fun T : E →L[ℂ] E => T x)
            (Unitary.mul_star_self_of_mem U.property)
          _ = (star mu * mu) • x := by rw [hmod, one_smul]
          _ = _ := by rw [map_smul, hu, smul_smul]
      have hsum := congrArg (fun T : E →L[ℂ] E => T x) hreal
      change (U : E →L[ℂ] E) x + star (U : E →L[ℂ] E) x = (2 * (c : ℂ)) • x at hsum
      rw [hu, hstar, ← add_smul] at hsum
      have hcoef := smul_left_injective ℂ hx.2 hsum
      have hre : mu.re = c := by
        have h := congrArg Complex.re hcoef
        norm_num [RCLike.star_def] at h
        linarith
      have him : mu.im ^ 2 = s ^ 2 := by
        have h := Complex.sq_norm_sub_sq_re mu
        rw [hnorm, hre] at h
        nlinarith
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with hs | hs
      · right
        apply Complex.ext <;> simp [hre, hs]
      · left
        apply Complex.ext <;> simp [hre, hs]
    obtain ⟨P, hP, heq⟩ := exists_isStarProjection_eq_affine_of_spectrum_subset_pair
      (U : E →L[ℂ] E) ((c : ℂ) - (s : ℂ) * Complex.I)
      ((c : ℂ) + (s : ℂ) * Complex.I) hspec
    have hcoef : ((c : ℂ) + (s : ℂ) * Complex.I) -
        ((c : ℂ) - (s : ℂ) * Complex.I) = 2 * (s : ℂ) * Complex.I := by ring
    exact ⟨P, hP, by simpa only [hcoef] using heq⟩
  · rintro ⟨P, hP, heq⟩
    have ha : star ((c : ℂ) - (s : ℂ) * Complex.I) =
        (c : ℂ) + (s : ℂ) * Complex.I := by simp
    have hb : star (2 * (s : ℂ) * Complex.I) = -(2 * (s : ℂ) * Complex.I) := by simp
    rw [heq, star_add, star_smul, star_smul, star_one, hP.isSelfAdjoint.star_eq, ha, hb]
    module

/-- Distinct conjugate phases make the orthogonal spectral projection
unique, including when either phase has zero multiplicity. -/
theorem unitary_add_star_eq_scalar_iff_unique_projection_complex
    (U : unitary (E →L[ℂ] E)) (c s : ℝ) (hcircle : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    (U : E →L[ℂ] E) + star (U : E →L[ℂ] E) = (2 * (c : ℂ)) • 1 ↔
      ∃! P : E →L[ℂ] E, IsStarProjection P ∧
        (U : E →L[ℂ] E) = ((c : ℂ) - (s : ℂ) * Complex.I) • 1 +
          (2 * (s : ℂ) * Complex.I) • P := by
  constructor
  · intro hreal
    obtain ⟨P, hP, heq⟩ :=
      (unitary_add_star_eq_scalar_iff_projection_complex U c s hcircle).mp hreal
    refine ⟨P, ⟨hP, heq⟩, ?_⟩
    intro Q hQ
    have hnon : 2 * (s : ℂ) * Complex.I ≠ 0 := mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Complex.ofReal_ne_zero.mpr hs)) Complex.I_ne_zero
    apply smul_right_injective _ hnon
    change (2 * (s : ℂ) * Complex.I) • Q = (2 * (s : ℂ) * Complex.I) • P
    exact add_left_cancel (hQ.2.symm.trans heq)
  · rintro ⟨P, hP, _⟩
    exact (unitary_add_star_eq_scalar_iff_projection_complex U c s hcircle).mpr ⟨P, hP⟩

omit [FiniteDimensional ℂ E] in
/-- A scalar real-part identity restricts to any finite invariant subspace
of an ambient unitary. The ambient Hilbert space may be infinite dimensional. -/
theorem exists_restriction_add_star_eq_scalar_complex
    (U : E ≃ₗᵢ[ℂ] E) (N : Submodule ℂ E) [FiniteDimensional ℂ N]
    (hinv : ∀ x ∈ N, U x ∈ N) (c : ℝ)
    (hreal : ∀ x : N, U (x : E) + star (U : E →L[ℂ] E) (x : E) =
      (2 * (c : ℂ)) • (x : E)) :
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = U x) ∧
      (V : N →L[ℂ] N) + star (V : N →L[ℂ] N) = (2 * (c : ℂ)) • 1 := by
  obtain ⟨V, hV, hVs, _⟩ := U.exists_restriction_of_finite_invariant N hinv
  have hsum : (V : N →L[ℂ] N) + star (V : N →L[ℂ] N) = (2 * (c : ℂ)) • 1 := by
    ext x
    change (V x : E) + (star (V : N →L[ℂ] N) x : E) = (2 * (c : ℂ)) • (x : E)
    rw [show star (V : N →L[ℂ] N) = (V.symm : N →L[ℂ] N) from V.adjoint_eq_symm]
    change (V x : E) + (V.symm x : E) = (2 * (c : ℂ)) • (x : E)
    rw [hV, hVs]
    change (U : E →L[ℂ] E) x + (U.symm : E →L[ℂ] E) x = _
    rw [← U.adjoint_eq_symm]
    exact hreal x
  exact ⟨V, hV, hsum⟩

/-- A finite invariant subspace with prescribed scalar real part has a
unique two-phase orthogonal projection. The restricted unitary acts by the
original ambient unitary, including on a zero-dimensional subspace. -/
theorem exists_restriction_unique_phase_projection_complex
    (U : E ≃ₗᵢ[ℂ] E) (N : Submodule ℂ E)
    (hinv : ∀ x ∈ N, U x ∈ N) (c s : ℝ)
    (hcircle : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hreal : ∀ x : N, U (x : E) + star (U : E →L[ℂ] E) (x : E) =
      (2 * (c : ℂ)) • (x : E)) :
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = U x) ∧
      ∃! P : N →L[ℂ] N, IsStarProjection P ∧
        (V : N →L[ℂ] N) = ((c : ℂ) - (s : ℂ) * Complex.I) • 1 +
          (2 * (s : ℂ) * Complex.I) • P := by
  obtain ⟨V, hV, hsum⟩ := exists_restriction_add_star_eq_scalar_complex U N hinv c hreal
  exact ⟨V, hV, (unitary_add_star_eq_scalar_iff_unique_projection_complex
    (Unitary.linearIsometryEquiv.symm V) c s hcircle hs).mp hsum⟩

/-- Equivalently, the choices are self-adjoint unitary phase factors.
At a vanishing sine the representation collapses to a single scalar
operator; no uniqueness of the unused involution parameter is asserted. -/
theorem unitary_add_star_eq_scalar_iff_involution_complex
    (U : unitary (E →L[ℂ] E)) (c s : ℝ) (hcircle : c ^ 2 + s ^ 2 = 1) :
    (U : E →L[ℂ] E) + star (U : E →L[ℂ] E) = (2 * (c : ℂ)) • 1 ↔
      ∃ H : unitary (E →L[ℂ] E), IsSelfAdjoint (H : E →L[ℂ] E) ∧
        (U : E →L[ℂ] E) = (c : ℂ) • 1 + ((s : ℂ) * Complex.I) • (H : E →L[ℂ] E) := by
  constructor
  · intro hreal
    obtain ⟨P, hP, heq⟩ :=
      (unitary_add_star_eq_scalar_iff_projection_complex U c s hcircle).mp hreal
    let H : unitary (E →L[ℂ] E) := ⟨2 * P - 1, hP.two_mul_sub_one_mem_unitary⟩
    have hself : IsSelfAdjoint (H : E →L[ℂ] E) := by
      change IsSelfAdjoint (2 * P - 1)
      rw [two_mul]
      exact (hP.isSelfAdjoint.add hP.isSelfAdjoint).sub (IsSelfAdjoint.one _)
    refine ⟨H, hself, ?_⟩
    change (U : E →L[ℂ] E) = (c : ℂ) • 1 + ((s : ℂ) * Complex.I) • (2 * P - 1)
    rw [heq]
    simp only [two_mul]
    module
  · rintro ⟨H, hH, heq⟩
    have hstar : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by simp
    rw [heq, star_add, star_smul, star_smul, star_one, hH.star_eq, hstar]
    simp only [RCLike.star_def, Complex.conj_ofReal]
    module

/-- The paired unitary-average equation on a positive scalar cosine
block has exactly the self-adjoint-unitary phase choices. In particular,
the two multiplicity factors must agree. -/
theorem unitary_star_average_eq_scalar_iff_involution_complex
    (X Y : unitary (E →L[ℂ] E)) (c s : ℝ) (hc : 0 < c)
    (hcircle : c ^ 2 + s ^ 2 = 1) :
    (X : E →L[ℂ] E) + star (Y : E →L[ℂ] E) = (2 * (c : ℂ)) • 1 ↔
      ∃ H : unitary (E →L[ℂ] E), IsSelfAdjoint (H : E →L[ℂ] E) ∧
        (X : E →L[ℂ] E) = (c : ℂ) • 1 + ((s : ℂ) * Complex.I) • (H : E →L[ℂ] E) ∧
        (Y : E →L[ℂ] E) = (X : E →L[ℂ] E) := by
  constructor
  · intro havg
    let D : E →L[ℂ] E := (c : ℂ) • 1
    have hD : D.IsPositive := ContinuousLinearMap.isPositive_one.smul_of_nonneg
      (RCLike.ofReal_nonneg.mpr hc.le)
    have hinj : Function.Injective D := by
      intro x y hxy
      change (c : ℂ) • x = (c : ℂ) • y at hxy
      exact smul_right_injective E (Complex.ofReal_ne_zero.mpr hc.ne') hxy
    have hstar := ContinuousLinearMap.eq_star_of_unitary_sum_eq_two_smul_of_injective
      X (star Y) D hD (by simpa only [D, smul_smul, Unitary.coe_star] using havg) hinj
    change star (Y : E →L[ℂ] E) = star (X : E →L[ℂ] E) at hstar
    have hYX : (Y : E →L[ℂ] E) = (X : E →L[ℂ] E) := by
      simpa only [star_star] using congrArg star hstar
    obtain ⟨H, hH, hX⟩ := (unitary_add_star_eq_scalar_iff_involution_complex X c s hcircle).mp
      (by simpa only [hYX] using havg)
    exact ⟨H, hH, hX, hYX⟩
  · rintro ⟨H, hH, hX, hYX⟩
    rw [hYX]
    exact (unitary_add_star_eq_scalar_iff_involution_complex X c s hcircle).mpr ⟨H, hH, hX⟩

omit [FiniteDimensional ℂ E] in
/-- At a zero scalar cosine, the average equation leaves an arbitrary
unitary and forces the other factor to be its negative adjoint. -/
theorem unitary_star_sum_eq_zero_iff_complex (X Y : unitary (E →L[ℂ] E)) :
    (X : E →L[ℂ] E) + star (Y : E →L[ℂ] E) = 0 ↔
      (Y : E →L[ℂ] E) = -star (X : E →L[ℂ] E) := by
  constructor
  · intro h
    have hstar := eq_neg_of_add_eq_zero_right h
    simpa only [star_star, star_neg] using congrArg star hstar
  · intro h
    rw [h, star_neg, star_star, add_neg_cancel]

end TauCeti
