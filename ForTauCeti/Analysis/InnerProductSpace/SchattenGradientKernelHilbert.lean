/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenGradientHilbert
public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

/-!
# The zero-gradient sector without an eigenbasis

For `1<p<2`, the imaginary part of a unitary factors through its Schatten
phase gradient by a bounded continuous radial multiplier. Its gradient
kernel therefore carries self-adjoint unitary action, even in infinite
dimension. The positive radial exponent `2-p` avoids an inverse at the
identity and is essential to this bounded multiplier argument.
-/

public section

noncomputable section

namespace TauCeti

private theorem phase_gradient_radial_factor (p : ℝ) (hp : 1 < p) (z : ℂ) :
    z - star z = (((2 / p * ‖z - 1‖ ^ (2 - p) : ℝ) : ℂ) * Complex.I) *
      (schattenPhaseDerivative p z : ℂ) := by
  by_cases hz : z = 1
  · simp [hz, schattenPhaseDerivative_eq]
  have hn : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hpow : ‖z - 1‖ ^ (2 - p) * ‖z - 1‖ ^ (p - 2) = 1 := by
    rw [← Real.rpow_add hn]
    simp
  have hcoeff : (2 / p * ‖z - 1‖ ^ (2 - p)) *
      (p * ‖z - 1‖ ^ (p - 2) * z.im) = 2 * z.im := by
    calc
      _ = (2 / p * p) * (‖z - 1‖ ^ (2 - p) * ‖z - 1‖ ^ (p - 2)) * z.im := by ring
      _ = _ := by rw [hpow, div_mul_cancel₀ _ (by linarith : p ≠ 0), mul_one]
  rw [schattenPhaseDerivative_eq]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> nlinarith [hcoeff]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The unitary imaginary part factors continuously through its phase
gradient. The radial multiplier is bounded on the unit-circle spectrum
and is zero, rather than singular, at identity. -/
theorem unitary_sub_star_eq_radial_mul_schattenUnitaryGradient
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (U : E ≃ₗᵢ[ℂ] E) :
    (U : E →L[ℂ] E) - star (U : E →L[ℂ] E) =
      cfc (fun z : ℂ => ((2 / p * ‖z - 1‖ ^ (2 - p) : ℝ) : ℂ) * Complex.I)
        (U : E →L[ℂ] E) * schattenUnitaryGradient p (U : E →L[ℂ] E) := by
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  let f (z : ℂ) := ((2 / p * ‖z - 1‖ ^ (2 - p) : ℝ) : ℂ) * Complex.I
  let g (z : ℂ) := (schattenPhaseDerivative p z : ℂ)
  have hrad : Continuous (fun z : ℂ => ‖z - 1‖ ^ (2 - p)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ 2 - p)).comp
      (continuous_norm.comp (continuous_id.sub continuous_const))
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp (continuous_const.mul hrad)).mul_const _
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp (continuous_schattenPhaseDerivative p hp1)
  have hleft : cfc (fun z : ℂ => z - star z) (U : E →L[ℂ] E) =
      (U : E →L[ℂ] E) - star (U : E →L[ℂ] E) := by
    rw [cfc_sub (fun z : ℂ => z) (fun z => star z) (U : E →L[ℂ] E)
      continuous_id.continuousOn continuous_star.continuousOn,
      cfc_id' ℂ (U : E →L[ℂ] E),
      cfc_star_id (R := ℂ) (U : E →L[ℂ] E)]
  calc
    _ = cfc (fun z : ℂ => z - star z) (U : E →L[ℂ] E) := hleft.symm
    _ = cfc (fun z => f z * g z) (U : E →L[ℂ] E) :=
      cfc_congr (fun z _ => phase_gradient_radial_factor p hp1 z)
    _ = _ := by
      rw [cfc_mul f g _ hf.continuousOn hg.continuousOn, schattenUnitaryGradient_def]

/-- Every vector in the phase-gradient kernel sees the same forward
and inverse unitary actions. This includes zero displacement and does
not require a finite-dimensional kernel or ambient space. -/
theorem unitary_apply_eq_symm_of_schattenUnitaryGradient_apply_eq_zero
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (U : E ≃ₗᵢ[ℂ] E)
    (x : E) (hx : schattenUnitaryGradient p (U : E →L[ℂ] E) x = 0) :
    U x = U.symm x := by
  have h := congrArg (fun A : E →L[ℂ] E => A x)
    (unitary_sub_star_eq_radial_mul_schattenUnitaryGradient p hp1 hp2 U)
  change U x - star (U : E →L[ℂ] E) x = _ at h
  change U x - star (U : E →L[ℂ] E) x =
    (cfc _ (U : E →L[ℂ] E)) (schattenUnitaryGradient p (U : E →L[ℂ] E) x) at h
  rw [hx, map_zero] at h
  have hs : star (U : E →L[ℂ] E) = (U.symm : E →L[ℂ] E) := U.adjoint_eq_symm
  rw [hs] at h
  exact sub_eq_zero.mp h

/-- The actual restriction to the full phase-gradient kernel is a
self-adjoint unitary. This includes an infinite fixed kernel and does
not discard possible `-1` directions or assume minimality. -/
theorem exists_selfAdjoint_unitary_restriction_schatten_gradient_kernel
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (U : E ≃ₗᵢ[ℂ] E) :
    let Z := (schattenUnitaryGradient p (U : E →L[ℂ] E)).ker
    ∃ V : Z ≃ₗᵢ[ℂ] Z,
      (∀ x : Z, (V x : E) = U x) ∧
      (∀ x : Z, (V.symm x : E) = U.symm x) ∧
      IsSelfAdjoint (V : Z →L[ℂ] Z) := by
  let G := schattenUnitaryGradient p (U : E →L[ℂ] E)
  let Z := G.ker
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  have hGU : Commute G (U : E →L[ℂ] E) := commute_schattenUnitaryGradient p _
  have hGself : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient p _
  have hGUs : Commute G (star (U : E →L[ℂ] E)) := by
    simpa only [hGself.star_eq] using commute_star_star.mpr hGU
  have hred : Z.IsReducing U.toLinearMap := by
    change Z.IsReducing (U : E →L[ℂ] E).toLinearMap
    apply ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr
    constructor
    · apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      intro x hx
      change G (U x) = 0
      calc
        _ = U (G x) := congrArg (fun A : E →L[ℂ] E => A x) hGU.eq
        _ = 0 := by rw [show G x = 0 from hx, map_zero]
    · apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      intro x hx
      change G (star (U : E →L[ℂ] E) x) = 0
      calc
        _ = star (U : E →L[ℂ] E) (G x) :=
          congrArg (fun A : E →L[ℂ] E => A x) hGUs.eq
        _ = 0 := by rw [show G x = 0 from hx, map_zero]
  obtain ⟨V, hV, hVs⟩ := U.exists_restriction_of_reducing Z hred
  refine ⟨V, hV, hVs, ?_⟩
  change star (V : Z →L[ℂ] Z) = (V : Z →L[ℂ] Z)
  rw [show star (V : Z →L[ℂ] Z) = (V.symm : Z →L[ℂ] Z) from V.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact (hVs x).trans
    ((unitary_apply_eq_symm_of_schattenUnitaryGradient_apply_eq_zero p hp1 hp2 U x
      x.property).symm.trans (hV x).symm)

end TauCeti
