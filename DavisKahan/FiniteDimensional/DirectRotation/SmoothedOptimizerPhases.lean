/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerNoMixing
import ForTauCeti.Analysis.InnerProductSpace.UnitaryScalarRealPart

/-!
# Spectral projection parameters of every smoothed optimizer

Every global optimizer restricts to a unitary on each actual principal-cosine
eigenspace. On a positive supercritical eigenspace this restriction has two
distinct conjugate phases and determines a unique orthogonal projection.

This is a necessary normal form for every optimizer. It does not assert that
every projection on the full cosine eigenspace is admissible: its compatibility
with the source reflection and the rotation grading remains to be imposed.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every optimizer has a unique two-phase spectral projection on each
positive supercritical cosine eigenspace, at arbitrary multiplicity.
The restriction is the action of the original ambient optimizer's relative
phase, not an unrelated model supplied as a hypothesis. -/
theorem minimizing_weighted_transport_eigenspace_phase_projection_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (c : ℝ) (hc : 0 < c) (hcritical : a * c < b) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := R.trans T.symm
    let N := Module.End.eigenspace
      (Proposition35.section3CosAngleOperator K L).toLinearMap (c : ℂ)
    let beta := a * c / b
    let s := Real.sqrt (1 - beta ^ 2)
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = Z x) ∧
      ∃! P : N →L[ℂ] N, IsStarProjection P ∧
        (V : N →L[ℂ] N) = ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 +
          (2 * (s : ℂ) * Complex.I) • P := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z := R.trans T.symm
  let C := Proposition35.section3CosAngleOperator K L
  let N := Module.End.eigenspace C.toLinearMap (c : ℂ)
  let beta := a * c / b
  let s := Real.sqrt (1 - beta ^ 2)
  have hbeta0 : 0 < beta := div_pos (mul_pos (hb.trans hab) hc) hb
  have hbeta1 : beta < 1 := (div_lt_one hb).mpr hcritical
  have hsquare : 0 < 1 - beta ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hbeta1) (add_pos hbeta0 zero_lt_one)]
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hsquare).ne'
  have hcircle : beta ^ 2 + s ^ 2 = 1 := by
    rw [show s ^ 2 = 1 - beta ^ 2 from Real.sq_sqrt hsquare.le]
    ring
  obtain ⟨_, _, _, _, hcomm, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hinv : ∀ x ∈ N, Z x ∈ N := by
    intro x hx
    change x ∈ Module.End.eigenspace C.toLinearMap (c : ℂ) at hx
    change Z x ∈ Module.End.eigenspace C.toLinearMap (c : ℂ)
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change C x = (c : ℂ) • x at hx
    change C (Z x) = (c : ℂ) • Z x
    have h := congrArg (fun A : E →L[ℂ] E => A x) hcomm.eq
    change Z (C x) = C (Z x) at h
    rw [hx, map_smul] at h
    exact h.symm
  apply exists_restriction_unique_phase_projection_complex Z N hinv beta s hcircle hs
  intro x
  have hx : C (x : E) = (c : ℂ) • (x : E) :=
    Module.End.mem_eigenspace_iff.mp x.property
  have h := minimizing_weighted_transport_relative_real_part_complex a b hb hab
    K L hKL T hT hatt c hc x hx
  change Z (x : E) + star (Z : E →L[ℂ] E) (x : E) =
    (2 * ((min 1 beta : ℝ) : ℂ)) • (x : E) at h
  rwa [min_eq_right hbeta1.le] at h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
