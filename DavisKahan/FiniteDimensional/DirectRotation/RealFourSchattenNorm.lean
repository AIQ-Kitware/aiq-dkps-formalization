/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.RealFourSchatten
import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus

/-!
# The real four-dimensional minimum for the accepted Schatten seminorm

The literal singular-value power theorem yields an actual unitary
minimizer for the accepted Schatten seminorm. Conversely every global
unitary minimum has this exact angle-dependent value. The latter form
applies directly to the actual restrictions of a real ambient minimum.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The literal real displacement power sum is the accepted Schatten power. -/
theorem realSpectralDisplacementCost_eq_schatten_rpow
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (A : E →ₗ[ℝ] E) :
    realSpectralDisplacementCost (fun s => s^p.toReal) A =
      UnitarilyInvariantSeminorm.schatten ℝ E E p (LinearMap.id - A) ^ p.toReal := by
  exact (schatten_rpow_eq_sum_singularValues (LinearMap.id - A) p hp).symm

/-- The exact four-dimensional formula is attained by an actual unitary
for the accepted real Schatten seminorm, with full ambient comparison. -/
theorem exists_minimizing_real_four_schatten_unitary_principalAngles
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2) :
    let h := (K.principalAngles L 0 + K.principalAngles L 1)/2
    let d := (K.principalAngles L 0 - K.principalAngles L 1)/2
    ∃ U : unitary (E →L[ℝ] E),
      (U : E →L[ℝ] E) * K.starProjection * star (U : E →L[ℝ] E) = L.starProjection ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - (U : E →L[ℝ] E).toLinearMap) ^ p.toReal =
        min (2*phasePower p.toReal h (max d (optimalPhase p.toReal h)))
          ((2 : ℝ)^p.toReal + 2*phaseChord (K.principalAngles L 1)^p.toReal) ∧
      IsMinOn
        (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℝ] E) := by
  obtain ⟨A, hA, htrans, hcost, hmin⟩ :=
    exists_minimizing_real_four_schatten_transport_principalAngles p.toReal hp1 hp2 K L hE hK hL
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

/-- Every global minimum in an actual real four-dimensional rank-two
transport problem has the exact clipped two-branch value. -/
theorem real_four_schatten_cost_eq_of_isMinOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2)
    (T : unitary (E →L[ℝ] E))
    (htrans : (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E) = L.starProjection)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (T : E →L[ℝ] E)) :
    let h := (K.principalAngles L 0 + K.principalAngles L 1)/2
    let d := (K.principalAngles L 0 - K.principalAngles L 1)/2
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - (T : E →L[ℝ] E).toLinearMap) ^ p.toReal =
      min (2*phasePower p.toReal h (max d (optimalPhase p.toReal h)))
        ((2 : ℝ)^p.toReal + 2*phaseChord (K.principalAngles L 1)^p.toReal) := by
  obtain ⟨V, hV, hcost, hVmin⟩ :=
    exists_minimizing_real_four_schatten_unitary_principalAngles p hp hp1 hp2 K L hE hK hL
  apply le_antisymm
  · rw [← hcost]
    exact hmin ⟨V.property, hV⟩
  · rw [← hcost]
    exact hVmin ⟨T.property, htrans⟩

/-- Exact four-dimensional restriction cost with its actual target defined
as the image of the source. This applies directly to every balanced
four-dimensional member of a globally minimizing real block family. -/
theorem real_four_schatten_cost_eq_of_isMinOn_image
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (V : E ≃ₗᵢ[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (V : E →L[ℝ] E) * K.starProjection * star (V : E →L[ℝ] E)} (V : E →L[ℝ] E)) :
    let L := K.map V.toLinearMap
    let h := (K.principalAngles L 0 + K.principalAngles L 1)/2
    let d := (K.principalAngles L 0 - K.principalAngles L 1)/2
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - V.toLinearMap) ^ p.toReal =
      min (2*phasePower p.toReal h (max d (optimalPhase p.toReal h)))
        ((2 : ℝ)^p.toReal + 2*phaseChord (K.principalAngles L 1)^p.toReal) := by
  let L := K.map V.toLinearMap
  have hL : Module.finrank ℝ L = 2 := (V.toLinearEquiv.finrank_map_eq K).trans hK
  have htrans : (V : E →L[ℝ] E) * K.starProjection * star (V : E →L[ℝ] E) =
      L.starProjection := by
    ext x
    change V (K.starProjection (star (V : E →L[ℝ] E) x)) = L.starProjection x
    rw [show star (V : E →L[ℝ] E) = (V.symm : E →L[ℝ] E) from V.adjoint_eq_symm]
    exact (Submodule.starProjection_map_apply V K x).symm
  have hnorm := real_four_schatten_cost_eq_of_isMinOn p hp hp1 hp2 K L hE hK hL
    (Unitary.linearIsometryEquiv.symm V)
    (by simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using htrans)
    (by simpa only [Unitary.coe_symm_linearIsometryEquiv_apply, ← htrans] using hmin)
  exact hnorm

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
