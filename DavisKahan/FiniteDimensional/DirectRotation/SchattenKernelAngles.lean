/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenReflectingPlanes
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FixedRightCompression
public import ForTauCeti.Analysis.InnerProductSpace.InvariantKernel

/-!
# The actual gradient-kernel sine operator is a projection

The complete fixed/right block family makes the restricted intrinsic sine
operator a projection. Its eigenvalues are therefore zero or one. This
excludes the gradient kernel from every interior geometric angle space,
without an acuteness assumption on the ambient subspace pair.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- At every finite complex local minimum with `p>1`, the actual
restricted sine operator on the gradient kernel is a projection. -/
theorem gradient_kernel_sinAngleOperator_isStarProjection_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
    IsStarProjection ((K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype)) := by
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨R, hR, hself, hmapR, _⟩ := gradient_kernel_principalAngle_lower_bound p hp K L U hmap
  obtain ⟨R₀, hR₀, F, hF, _, hspan⟩ :=
    gradient_kernel_fixed_or_right_blocks_of_isLocalMinOn_transports_complex
      p hp hp1 K L.starProjection U ht hmin
  have hRR : R₀ = R := by
    apply LinearIsometryEquiv.ext
    intro z
    apply Subtype.ext
    exact (hR₀ z).trans (hR z).symm
  rw [hRR] at hF
  let V := Unitary.linearIsometryEquiv.symm R
  have hVmap : K₀.map (Unitary.linearIsometryEquiv V).toLinearMap = L₀ := by
    simpa only [V, MulEquiv.apply_symm_apply] using hmapR
  apply Submodule.isStarProjection_sinAngleOperator_of_fixed_or_exchange_blocks
    K₀ L₀ R hself ((map_eq_iff_conjugate_starProjection_complex K₀ L₀ V).mp hVmap) F hspan
  intro N hNF
  obtain ⟨_, _, hPN, _, hcase⟩ := hF N hNF
  exact ⟨hPN, hcase.imp id (fun h => h.2)⟩

/-- Every interior sine eigenvector is orthogonal to the actual gradient
kernel. The exponent may be any finite `p>1`, and no ambient angle is
excluded. Values other than zero or one include empty eigenspaces. -/
theorem mem_gradient_kernel_orthogonal_of_sin_eigenvector_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (mu : ℝ) (hmu0 : mu ≠ 0) (hmu1 : mu ≠ 1) (x : E)
    (hx : K.sinAngleOperator L x = (mu : ℂ) • x) :
    x ∈ (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.kerᗮ := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let N := G.toLinearMap.ker
  let S := K.sinAngleOperator L
  let S₀ := (K.comap N.subtype).sinAngleOperator (L.comap N.subtype)
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  have hK : ∀ z ∈ N, K.starProjection z ∈ N :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  have hL : ∀ z ∈ N, L.starProjection z ∈ N :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPL.eq)
  have hres (z : N) : (S₀ z : E) = S (z : E) :=
    Submodule.sinAngleOperator_comap_subtype_apply_of_invariant K L N hK hL z
  have hproj := gradient_kernel_sinAngleOperator_isStarProjection_of_isLocalMinOn_complex
    p hp hp1 K L U hmap hmin
  have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint.isSymmetric
  apply hS.mem_orthogonal_of_eigenvector_of_idempotent_on_subspace N mu hmu0 hmu1 x hx
  intro z hz
  let z' : N := ⟨z, hz⟩
  calc
    S (S z) = S (S₀ z' : E) := congrArg S (hres z').symm
    _ = (S₀ (S₀ z') : E) := (hres (S₀ z')).symm
    _ = (S₀ z' : E) := congrArg (fun y : N => (y : E))
      (congrArg (fun A : N →L[ℂ] N => A z') hproj.isIdempotentElem.eq)
    _ = S z := hres z'

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
