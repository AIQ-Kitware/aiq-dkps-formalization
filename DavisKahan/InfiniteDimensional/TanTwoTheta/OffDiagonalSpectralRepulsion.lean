/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Reflection

public import DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAcuteFormGap
public import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Full spectral repulsion for a fully off-diagonal perturbation

Davis--Kahan 1970 Section 8 asserts that a perturbation which is entirely
off-diagonal with respect to the source splitting cannot move any spectrum into
the open gap.  In finite dimension this is a statement about eigenvalues, and
that is how the bounded development previously recorded it.  In an arbitrary
Hilbert space the spectrum need not be a point spectrum at all, so the
eigenvalue form is strictly weaker than the source claim.

The proof here is dimension-free.  Write `J` for the reflection through the
source subspace `U`, and let `lam` be a point of the open gap `(a,b)`.  The
ordered form bounds make the *reflected* centered operator `J (A - lam)`
uniformly coercive by `eps = min (lam-a) (b-lam)`, because reflection flips the
sign on `Uᗮ` exactly where the form inequality points the other way.  Full
off-diagonality gives `J H = - H J`; with `J` and `H` self-adjoint that makes
`J H` skew-adjoint, so it contributes nothing to the real part.  Hence
`J (A + H - lam)` is coercive, therefore a unit, and `J` is its own inverse, so
`A + H - lam` is a unit and `lam` is a resolvent point.

No compactness, no discreteness, no norm-attaining eigenvector.
-/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Foundation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A fully off-diagonal self-adjoint perturbation contributes nothing to the
real part of the form of the reflected operator: `J H` is skew-adjoint. -/
theorem re_inner_reflection_comp_offDiagonal_eq_zero
    (H : E →L[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) (x : E) :
    RCLike.re ⟪((U.reflection : E →L[ℂ] E) ∘L H) x, x⟫_ℂ = 0 := by
  have hJsa : IsSelfAdjoint ((U.reflection : E →L[ℂ] E)) := by
    rw [isSelfAdjoint_iff]
    exact (U.isSelfAdjoint_reflection).star_eq
  have hJsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hJsa
  have hHsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hanti :
      (U.reflection : E →L[ℂ] E) (H x) = -(H ((U.reflection : E →L[ℂ] E) x)) := by
    exact DFunLike.congr_fun
      (U.reflection_mul_eq_neg_mul_of_maps_orthogonal H hHU hHUperp) x
  have hw1 : ⟪(U.reflection : E →L[ℂ] E) (H x), x⟫_ℂ
      = ⟪H x, (U.reflection : E →L[ℂ] E) x⟫_ℂ := hJsym _ _
  have hw2 : ⟪(U.reflection : E →L[ℂ] E) (H x), x⟫_ℂ
      = -⟪(U.reflection : E →L[ℂ] E) x, H x⟫_ℂ := by
    rw [hanti, inner_neg_left]
    congr 1
    exact hHsym _ _
  have hsymRe : RCLike.re ⟪H x, (U.reflection : E →L[ℂ] E) x⟫_ℂ
      = RCLike.re ⟪(U.reflection : E →L[ℂ] E) x, H x⟫_ℂ :=
    inner_re_symm (H x) ((U.reflection : E →L[ℂ] E) x)
  have h1 := congrArg RCLike.re hw1
  have h2 := congrArg RCLike.re hw2
  rw [map_neg] at h2
  simp only [ContinuousLinearMap.comp_apply]
  linarith [h1, h2, hsymRe]

/-- **Spectral repulsion, full spectrum, arbitrary Hilbert space.**

If `A` is self-adjoint with `U` invariant, the form of `A` is bounded below by
`b` on `U` and above by `a` on `Uᗮ`, and the self-adjoint perturbation `H` maps
each of `U`, `Uᗮ` into the other, then no point of the open interval `(a,b)`
belongs to the spectrum of `A + H`.

This is the source Section 8 repulsion statement.  It is genuinely stronger
than the eigenvalue form: continuous spectrum is excluded too. -/
theorem realSpectrum_add_offDiagonal_subset_exterior_of_form_gap
    (A H : E →L[ℂ] E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    realSpectrum (A + H) ⊆ Set.Iic a ∪ Set.Ici b := by
  intro lam hlam
  by_contra hnot
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] at hnot
  obtain ⟨hla, hlb⟩ := hnot
  set ε : ℝ := min (lam - a) (b - lam) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεa : a ≤ lam - ε := by
    have : ε ≤ lam - a := min_le_left _ _
    linarith
  have hεb : lam + ε ≤ b := by
    have : ε ≤ b - lam := min_le_right _ _
    linarith
  -- Shrink the ordered form gap to be centred at `lam`.
  have hUhigh' : ∀ x ∈ U, (lam + ε) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
    intro x hx
    exact le_trans (mul_le_mul_of_nonneg_right hεb (sq_nonneg ‖x‖)) (hUhigh x hx)
  have hUperpLow' : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ (lam - ε) * ‖x‖ ^ 2 := by
    intro x hx
    exact le_trans (hUperpLow x hx)
      (mul_le_mul_of_nonneg_right hεa (sq_nonneg ‖x‖))
  -- The reflected centred operator is coercive by `ε`.
  have hkey : ∀ x : E, ε * ‖x‖ ^ 2 ≤
      RCLike.re ⟪((U.reflection : E →L[ℂ] E) ∘L
        (A - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) x, x⟫_ℂ := by
    intro x
    have h := U.reflection_centered_form_lower A
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) hAU
      (a := lam - ε) (b := lam + ε)
      ((ContinuousLinearMap.lowerFormBoundOn_iff A U (lam + ε)).mpr hUhigh')
      ((ContinuousLinearMap.upperFormBoundOn_iff A Uᗮ (lam - ε)).mpr hUperpLow') x
    have e1 : (lam - ε + (lam + ε)) / 2 = lam := by ring
    have e2 : (lam + ε - (lam - ε)) / 2 = ε := by ring
    rw [e1, e2] at h
    rw [← ContinuousLinearMap.mul_def]
    rw [_root_.ContinuousLinearMap.one_def] at h
    exact h
  have hskew := re_inner_reflection_comp_offDiagonal_eq_zero H U hH hHU hHUperp
  have hcoer : ∀ x : E, ε * ‖x‖ ^ 2 ≤
      RCLike.re ⟪((U.reflection : E →L[ℂ] E) ∘L
        ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) x, x⟫_ℂ := by
    intro x
    have hsplit :
        ((U.reflection : E →L[ℂ] E) ∘L
            ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) x =
          ((U.reflection : E →L[ℂ] E) ∘L
            (A - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) x +
            ((U.reflection : E →L[ℂ] E) ∘L H) x := by
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ← map_add]
      congr 1
      abel
    rw [hsplit, inner_add_left, map_add, hskew x, add_zero]
    exact hkey x
  have hunit : IsUnit ((U.reflection : E →L[ℂ] E) ∘L
      ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) :=
    _root_.ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
      (c := ⟨ε, by positivity⟩) hε
      (fun z => (mul_comm _ _).le.trans ((hcoer z).trans (RCLike.re_le_norm _)))
  have hJJ : (U.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E) = 1 :=
    U.reflection_mul_self
  have hJunit : IsUnit (U.reflection : E →L[ℂ] E) :=
    ⟨⟨(U.reflection : E →L[ℂ] E), (U.reflection : E →L[ℂ] E), hJJ, hJJ⟩, rfl⟩
  have hTunit : IsUnit ((A + H) -
      ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) := by
    have h := hJunit.mul hunit
    have hrw : (U.reflection : E →L[ℂ] E) * ((U.reflection : E →L[ℂ] E) ∘L
        ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) =
        (A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E := by
      rw [show ((U.reflection : E →L[ℂ] E) ∘L
          ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)) =
          (U.reflection : E →L[ℂ] E) *
            ((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) from rfl,
        ← mul_assoc, hJJ, one_mul]
    rwa [hrw] at h
  have hspec : ((lam : ℝ) : ℂ) ∈ spectrum ℂ (A + H) := hlam
  rw [spectrum.mem_iff] at hspec
  apply hspec
  rw [Algebra.algebraMap_eq_smul_one]
  have hneg : ((lam : ℝ) : ℂ) • (1 : E →L[ℂ] E) - (A + H) =
      -((A + H) - ((lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) := by
    show ((lam : ℝ) : ℂ) • (1 : E →L[ℂ] E) - (A + H) =
      -((A + H) - ((lam : ℝ) : ℂ) • (1 : E →L[ℂ] E))
    module
  rw [hneg]
  exact hTunit.neg

end

end DavisKahan
end TauCeti
