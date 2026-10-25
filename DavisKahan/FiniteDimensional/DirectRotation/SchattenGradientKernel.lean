/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientBlocks
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenReflectionBound
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace

/-!
# The angle-cost lower bound on the actual gradient kernel

The zero-gradient unitary restriction is a reflection. Intersecting the
source and target with the gradient kernel gives an actual transport pair
on that carrier, so the reflection lower bound applies to its accepted
principal angles. The proof retains the ambient action of the restriction;
it does not replace the kernel by an unrelated reflection model.

This closes the exceptional block estimate in the proposed global Schatten
lower bound. Reassembling the angle sums over all reducing spectral blocks
is a separate step. The statement allows an empty kernel and needs no local
minimality assumption: the zero-gradient representation holds for any unitary.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- On the actual gradient kernel, the transporter is a self-adjoint
unitary between the restricted subspaces and dominates their exact scalar
principal-angle sum. -/
theorem gradient_kernel_principalAngle_lower_bound
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L) :
    let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
    let K₀ := K.comap Z.subtype
    let L₀ := L.comap Z.subtype
    ∃ V : Z ≃ₗᵢ[ℂ] Z,
      (∀ x : Z, (V x : E) = (U : E →L[ℂ] E) x) ∧
      IsSelfAdjoint (V : Z →L[ℂ] Z) ∧ K₀.map V.toLinearMap = L₀ ∧
      (∑ i : Fin (Module.finrank ℂ K₀), phaseMinimum p.toReal (K₀.principalAngles L₀ i)) ≤
        UnitarilyInvariantSeminorm.schatten ℂ Z Z p
          (LinearMap.id - V.toLinearMap) ^ p.toReal := by
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  obtain ⟨V, S, hS, hV, hrepr⟩ := gradient_kernel_reflection_representation p.toReal hp0 U
  have hself : IsSelfAdjoint (V : Z →L[ℂ] Z) := by
    rw [hrepr]
    have hone : IsSelfAdjoint (1 : Z →L[ℂ] Z) := IsSelfAdjoint.one (Z →L[ℂ] Z)
    have htwo : IsSelfAdjoint (2 : ℂ) := IsSelfAdjoint.ofNat 2
    have hscaled : IsSelfAdjoint ((2 : ℂ) • (S : Z →L[ℂ] Z)) :=
      htwo.smul hS.isSelfAdjoint
    exact IsSelfAdjoint.sub (R := Z →L[ℂ] Z) hone hscaled
  have hVmap : K₀.map V.toLinearMap = L₀ :=
    Submodule.map_comap_subtype_of_isometry_restriction K L Z
      (Unitary.linearIsometryEquiv U) V hmap hV

  exact ⟨V, hV, hself, hVmap,
    sum_phaseMinimum_le_selfAdjoint_transport p hp K₀ L₀ V hself hVmap⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
