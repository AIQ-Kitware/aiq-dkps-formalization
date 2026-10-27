/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientHilbert
public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

/-!
# The entire zero-gradient sector of a smoothed unitary

The imaginary part factors continuously through the Charbonnier phase
gradient. Its full kernel therefore carries self-adjoint unitary action,
including both identity and negative-identity directions.
-/

public section

noncomputable section

namespace TauCeti

private theorem phase_gradient_radial_factor (tau : ℝ) (hτ : 0 < tau) (z : ℂ) :
    z - star z = (((2 * Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      (smoothedPhaseDerivative tau z : ℂ) := by
  let r := Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2)
  have hr : 0 < r := charbonnier_radius_pos tau hτ z
  have hcoeff : (2 * r) * (z.im / r) = 2 * z.im := by
    nlinarith [div_mul_cancel₀ z.im hr.ne']
  rw [smoothedPhaseDerivative_eq]
  change z - star z = (((2 * r : ℝ) : ℂ) * Complex.I) * ((z.im / r : ℝ) : ℂ)
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> nlinarith [hcoeff]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The unitary imaginary part factors continuously through its phase
gradient. Positive smoothing keeps the continuous radial multiplier bounded
on the unit-circle spectrum, including at identity. -/
theorem unitary_sub_star_eq_radial_mul_smoothedUnitaryGradient
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E) :
    (U : E →L[ℂ] E) - star (U : E →L[ℂ] E) =
      cfc (fun z : ℂ => ((2 * Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) : ℝ) : ℂ) * Complex.I)
        (U : E →L[ℂ] E) * smoothedUnitaryGradient tau (U : E →L[ℂ] E) := by
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  let f (z : ℂ) := ((2 * Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) : ℝ) : ℂ) * Complex.I
  let g (z : ℂ) := (smoothedPhaseDerivative tau z : ℂ)
  have hrad : Continuous (fun z : ℂ => Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2)) := by
    fun_prop
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp (continuous_const.mul hrad)).mul_const _
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp (continuous_smoothedPhaseDerivative tau hτ)
  have hleft : cfc (fun z : ℂ => z - star z) (U : E →L[ℂ] E) =
      (U : E →L[ℂ] E) - star (U : E →L[ℂ] E) := by
    rw [cfc_sub (fun z : ℂ => z) (fun z => star z) (U : E →L[ℂ] E)
      continuous_id.continuousOn continuous_star.continuousOn,
      cfc_id' ℂ (U : E →L[ℂ] E),
      cfc_star_id (R := ℂ) (U : E →L[ℂ] E)]
  calc
    _ = cfc (fun z : ℂ => z - star z) (U : E →L[ℂ] E) := hleft.symm
    _ = cfc (fun z => f z * g z) (U : E →L[ℂ] E) :=
      cfc_congr (fun z _ => phase_gradient_radial_factor tau hτ z)
    _ = _ := by
      rw [cfc_mul f g _ hf.continuousOn hg.continuousOn]
      rfl

/-- Every vector in the phase-gradient kernel sees the same forward
and inverse unitary actions. This includes zero displacement and does
not require a finite-dimensional kernel or ambient space. -/
theorem unitary_apply_eq_symm_of_smoothedUnitaryGradient_apply_eq_zero
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E)
    (x : E) (hx : smoothedUnitaryGradient tau (U : E →L[ℂ] E) x = 0) :
    U x = U.symm x := by
  have h := congrArg (fun A : E →L[ℂ] E => A x)
    (unitary_sub_star_eq_radial_mul_smoothedUnitaryGradient tau hτ U)
  change U x - star (U : E →L[ℂ] E) x = _ at h
  change U x - star (U : E →L[ℂ] E) x =
    (cfc _ (U : E →L[ℂ] E)) (smoothedUnitaryGradient tau (U : E →L[ℂ] E) x) at h
  rw [hx, map_zero] at h
  have hs : star (U : E →L[ℂ] E) = (U.symm : E →L[ℂ] E) := U.adjoint_eq_symm
  rw [hs] at h
  exact sub_eq_zero.mp h

/-- The actual restriction to the full phase-gradient kernel is a
self-adjoint unitary. This includes an infinite fixed kernel and does
not discard possible `-1` directions or assume minimality. -/
theorem exists_selfAdjoint_unitary_restriction_smoothed_gradient_kernel
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E) :
    let Z := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).ker
    ∃ V : Z ≃ₗᵢ[ℂ] Z,
      (∀ x : Z, (V x : E) = U x) ∧
      (∀ x : Z, (V.symm x : E) = U.symm x) ∧
      IsSelfAdjoint (V : Z →L[ℂ] Z) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let Z := G.ker
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  have hGU : Commute G (U : E →L[ℂ] E) := commute_smoothedUnitaryGradient tau _
  have hGself : IsSelfAdjoint G := isSelfAdjoint_smoothedUnitaryGradient tau _
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
    ((unitary_apply_eq_symm_of_smoothedUnitaryGradient_apply_eq_zero tau hτ U x
      x.property).symm.trans (hV x).symm)

end TauCeti
