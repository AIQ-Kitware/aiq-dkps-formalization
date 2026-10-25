/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerPhases
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Matching phase parameters on the two rotation eigenspaces

For every ambient optimizer, source reflection identifies the restrictions
of its relative phase on conjugate canonical-rotation eigenspaces. A positive
supercritical angle therefore has one orthogonal projection parameter on
one rotation eigenspace, and its reflected copy on the other. The dimension
of this parameter space is the angle multiplicity, rather than twice that
multiplicity. This is a necessary classification; attainment of arbitrary
independent parameter choices is a separate converse.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every minimizing weighted transporter has one unique orthogonal
projection parameter on a supercritical canonical-rotation eigenspace.
Source reflection determines the parameter on the conjugate eigenspace.
The eigenspaces and their pairing are those of the original ambient pair;
no simplicity or prescribed-block assumption is made. -/
theorem minimizing_weighted_transport_paired_phase_projection_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (mu : ℂ) (hmu : ‖mu‖ = 1) (hc : 0 < mu.re) (hcritical : a * mu.re < b) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := R.trans T.symm
    let N := Module.End.eigenspace R.toLinearMap mu
    let M := Module.End.eigenspace R.toLinearMap (star mu)
    let beta := a * mu.re / b
    let s := Real.sqrt (1 - beta ^ 2)
    ∃ j : N ≃ₗᵢ[ℂ] M, (∀ x : N, (j x : E) = K.reflection x) ∧
      ∃ V : N ≃ₗᵢ[ℂ] N, ∃ W : M ≃ₗᵢ[ℂ] M,
        (∀ x : N, (V x : E) = Z x) ∧ (∀ x : M, (W x : E) = Z x) ∧
        ∃! P : N →L[ℂ] N, IsStarProjection P ∧
          (V : N →L[ℂ] N) = ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 +
            (2 * (s : ℂ) * Complex.I) • P ∧
          (W : M →L[ℂ] M) = ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 +
            (2 * (s : ℂ) * Complex.I) •
              ((j : N →L[ℂ] M) ∘L P ∘L (j.symm : M →L[ℂ] N)) := by
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
  let R := Unitary.linearIsometryEquiv U
  let Z := R.trans T.symm
  let C := Proposition35.section3CosAngleOperator K L
  let N := Module.End.eigenspace R.toLinearMap mu
  let M := Module.End.eigenspace R.toLinearMap (star mu)
  let beta := a * mu.re / b
  let s := Real.sqrt (1 - beta ^ 2)
  have hC (x : E) (hx : R x = mu • x) : C x = (mu.re : ℂ) • x :=
    unitary_real_part_apply_of_apply_eq_smul U C
      (nonacuteDirectRotation_add_star_eq_two_cosine K L (finiteCrossedDefectEquiv K L hKL))
      mu hmu x hx
  have hrev (x : E) : (U : E →L[ℂ] E) (K.reflection x) =
      K.reflection (star (U : E →L[ℂ] E) x) :=
    nonacuteDirectRotation_reflection_eq_reflection_star K L
      (finiteCrossedDefectEquiv K L hKL) x
  let j : N ≃ₗᵢ[ℂ] M := unitaryEigenspaceStarEquivOfInvolution U K.reflection
    K.reflection_involutive hrev mu hmu
  have hj (x : N) : (j x : E) = K.reflection x := by
    exact unitaryEigenspaceStarEquivOfInvolution_apply U K.reflection
      K.reflection_involutive hrev mu hmu x
  have hR : K.map R.toLinearMap = L :=
    (K.map_eq_iff_intertwines_reflection L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL))
  have hZJ (x : E) : Z (K.reflection x) = K.reflection (Z x) :=
    K.relative_transport_commutes_reflection L R T hR hT x
  have hinv : ∀ x ∈ N, Z x ∈ N := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change R x = mu • x at hx
    change R (Z x) = mu • Z x
    have h := minimizing_weighted_transport_relative_commutes_rotation_on_positive_cosine_complex
      a b hb hab K L hKL T hT hatt mu.re hc x (hC x hx)
    change Z (R x) = R (Z x) at h
    rw [hx, map_smul] at h
    exact h.symm
  have hbeta0 : 0 < beta := div_pos (mul_pos (hb.trans hab) hc) hb
  have hbeta1 : beta < 1 := (div_lt_one hb).mpr hcritical
  have hsquare : 0 < 1 - beta ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hbeta1) (add_pos hbeta0 zero_lt_one)]
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hsquare).ne'
  have hcircle : beta ^ 2 + s ^ 2 = 1 := by
    rw [show s ^ 2 = 1 - beta ^ 2 from Real.sq_sqrt hsquare.le]
    ring
  obtain ⟨V, hV, P, ⟨hP, hVP⟩, huniq⟩ :=
    exists_restriction_unique_phase_projection_complex Z N hinv beta s hcircle hs (by
      intro x
      have hx : R (x : E) = mu • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
      have h := minimizing_weighted_transport_relative_real_part_complex a b hb hab
        K L hKL T hT hatt mu.re hc x (hC x hx)
      change Z (x : E) + star (Z : E →L[ℂ] E) (x : E) =
        (2 * ((min 1 beta : ℝ) : ℂ)) • (x : E) at h
      rwa [min_eq_right hbeta1.le] at h)
  let W : M ≃ₗᵢ[ℂ] M := j.symm.trans (V.trans j)
  have hW (x : M) : (W x : E) = Z x := by
    change (j (V (j.symm x)) : E) = Z x
    rw [hj, hV, ← hZJ]
    have h := hj (j.symm x)
    rw [j.apply_symm_apply] at h
    rw [← h]
  refine ⟨j, hj, V, W, hV, hW, P, ⟨hP, hVP, ?_⟩, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change j (V (j.symm x)) = _
    change j ((V : N →L[ℂ] N) (j.symm x)) = _
    rw [hVP]
    simp only [add_apply, smul_apply,
      one_apply_eq_self, map_add, map_smul, j.apply_symm_apply,
      ContinuousLinearMap.comp_apply]
    rfl
  · intro Q hQ
    exact huniq Q ⟨hQ.1, hQ.2.1⟩

/-- The paired projection description applies to every global minimizer
of the literal Charbonnier displacement cost. -/
theorem smoothed_minimizer_paired_phase_projection_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap)
    (mu : ℂ) (hmu : ‖mu‖ = 1) (hc : 0 < mu.re)
    (hcritical : smoothingRadius tau * mu.re < (smoothingRadius tau)⁻¹) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := R.trans T.symm
    let N := Module.End.eigenspace R.toLinearMap mu
    let M := Module.End.eigenspace R.toLinearMap (star mu)
    let beta := smoothingRadius tau * mu.re / (smoothingRadius tau)⁻¹
    let s := Real.sqrt (1 - beta ^ 2)
    ∃ j : N ≃ₗᵢ[ℂ] M, (∀ x : N, (j x : E) = K.reflection x) ∧
      ∃ V : N ≃ₗᵢ[ℂ] N, ∃ W : M ≃ₗᵢ[ℂ] M,
        (∀ x : N, (V x : E) = Z x) ∧ (∀ x : M, (W x : E) = Z x) ∧
        ∃! P : N →L[ℂ] N, IsStarProjection P ∧
          (V : N →L[ℂ] N) = ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 +
            (2 * (s : ℂ) * Complex.I) • P ∧
          (W : M →L[ℂ] M) = ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 +
            (2 * (s : ℂ) * Complex.I) •
              ((j : N →L[ℂ] M) ∘L P ∘L (j.symm : M →L[ℂ] N)) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  exact minimizing_weighted_transport_paired_phase_projection_complex a a⁻¹
    (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha)
    K L hKL T hT (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin)
    mu hmu hc hcritical

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
