/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealTwoPrincipalAngles
public import DavisKahan.FiniteDimensional.DirectRotation.RealFourSchattenNorm

/-!
# The unrestricted real one-angle Schatten minimum

The general spectral-penalty formula applies to every finite Schatten
exponent `p ≥ 1`, including the nuclear endpoint and the canonical regime.
It gives an actual unitary attainer and the exact value of every global
minimum on the original two-dimensional space. Its image-target form
computes the actual rank-one restrictions in the all-rank real reduction.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The one-angle real Schatten minimum, with actual attainment and all
ambient orthogonal competitors, for every finite exponent at least one. -/
theorem exists_minimizing_real_two_schatten_unitary_principalAngles
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 2)
    (hK : Module.finrank ℝ K = 1) (hL : Module.finrank ℝ L = 1) :
    ∃ U : unitary (E →L[ℝ] E),
      (U : E →L[ℝ] E) * K.starProjection * star (U : E →L[ℝ] E) = L.starProjection ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - (U : E →L[ℝ] E).toLinearMap) ^ p.toReal =
        min (2 * phaseChord (K.principalAngles L 0)^p.toReal) ((2 : ℝ)^p.toReal) ∧
      IsMinOn
        (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℝ] E) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  obtain ⟨A, hA, htrans, hcost, hmin⟩ :=
    exists_minimizing_real_two_transport_principalAngles K L hE hK hL
      (fun s => s^p.toReal)
      (fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hp0.le)
      (Real.zero_rpow hp0.ne')
  rw [sqrt_displacement_chord_eq_two_sin_half _
    ⟨K.principalAngles_nonneg L 0, (K.principalAngles_le_pi_div_two L 0).trans
      (by linarith [Real.pi_pos])⟩] at hcost
  let B := A.toContinuousLinearMap
  have hAother : A ∘ₗ A.adjoint = LinearMap.id := by
    change A * A.adjoint = 1
    exact mul_eq_one_comm.mp hA
  have hB : B ∈ unitary (E →L[ℝ] E) := by
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · ext x
      change A.adjoint (A x) = x
      exact congrArg (fun C : E →ₗ[ℝ] E => C x) hA
    · ext x
      change A (A.adjoint x) = x
      exact congrArg (fun C : E →ₗ[ℝ] E => C x) hAother
  refine ⟨⟨B, hB⟩, ?_, ?_, ?_⟩
  · ext x
    exact congrArg (fun C : E →ₗ[ℝ] E => C x) htrans
  · rw [realSpectralDisplacementCost_eq_schatten_rpow p hp] at hcost
    exact hcost
  · intro W hW
    have hW₁ := congrArg ContinuousLinearMap.toLinearMap (Unitary.star_mul_self_of_mem hW.1)
    change W.toLinearMap.adjoint ∘ₗ W.toLinearMap = LinearMap.id at hW₁
    have hW₂ := congrArg ContinuousLinearMap.toLinearMap hW.2
    change W.toLinearMap ∘ₗ K.starProjection.toLinearMap ∘ₗ W.toLinearMap.adjoint =
      L.starProjection.toLinearMap at hW₂
    have hbound := hmin ⟨hW₁, hW₂⟩
    change realSpectralDisplacementCost (fun s => s^p.toReal) A ≤
      realSpectralDisplacementCost (fun s => s^p.toReal) W.toLinearMap at hbound
    rw [realSpectralDisplacementCost_eq_schatten_rpow p hp,
      realSpectralDisplacementCost_eq_schatten_rpow p hp] at hbound
    exact hbound

/-- Every real one-angle global minimum has the attained exact value. -/
theorem real_two_schatten_cost_eq_of_isMinOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 2)
    (hK : Module.finrank ℝ K = 1) (hL : Module.finrank ℝ L = 1)
    (T : unitary (E →L[ℝ] E))
    (htrans : (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E) = L.starProjection)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (T : E →L[ℝ] E)) :
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - (T : E →L[ℝ] E).toLinearMap) ^ p.toReal =
      min (2 * phaseChord (K.principalAngles L 0)^p.toReal) ((2 : ℝ)^p.toReal) := by
  obtain ⟨V, hV, hcost, hVmin⟩ :=
    exists_minimizing_real_two_schatten_unitary_principalAngles p hp K L hE hK hL
  apply le_antisymm
  · rw [← hcost]
    exact hmin ⟨V.property, hV⟩
  · rw [← hcost]
    exact hVmin ⟨T.property, htrans⟩

/-- Image-target form for the actual one-angle restrictions of a real
ambient global minimum. No preferred coordinates are supplied. -/
theorem real_two_schatten_cost_eq_of_isMinOn_image
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K : Submodule ℝ E) (hE : Module.finrank ℝ E = 2)
    (hK : Module.finrank ℝ K = 1) (V : E ≃ₗᵢ[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (V : E →L[ℝ] E) * K.starProjection * star (V : E →L[ℝ] E)} (V : E →L[ℝ] E)) :
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - V.toLinearMap) ^ p.toReal =
      min (2 * phaseChord (K.principalAngles (K.map V.toLinearMap) 0)^p.toReal)
        ((2 : ℝ)^p.toReal) := by
  let L := K.map V.toLinearMap
  have hL : Module.finrank ℝ L = 1 := (V.toLinearEquiv.finrank_map_eq K).trans hK
  have htrans : (V : E →L[ℝ] E) * K.starProjection * star (V : E →L[ℝ] E) =
      L.starProjection := by
    ext x
    change V (K.starProjection (star (V : E →L[ℝ] E) x)) = L.starProjection x
    rw [show star (V : E →L[ℝ] E) = (V.symm : E →L[ℝ] E) from V.adjoint_eq_symm]
    exact (Submodule.starProjection_map_apply V K x).symm
  exact real_two_schatten_cost_eq_of_isMinOn p hp K L hE hK hL
    (Unitary.linearIsometryEquiv.symm V)
    (by simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using htrans)
    (by simpa only [Unitary.coe_symm_linearIsometryEquiv_apply, ← htrans] using hmin)

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
