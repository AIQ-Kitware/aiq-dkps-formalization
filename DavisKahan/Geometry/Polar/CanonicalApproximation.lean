/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.CanonicalRestriction
public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation

/-!
# Projection-adapted finite approximations of canonical rotations

The displacement modulus commutes with the source projection even though
the rotation itself generally does not. Its finite spectral cutoffs
therefore reduce both projections. Truncating on these cutoffs preserves
the actual canonical action and decreases every operator-ideal cost.
Neither acuteness nor separability is required.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The canonical displacement modulus commutes with the source
projection, including on zero and right-angle sectors. -/
theorem commute_starProjection_nonacuteDirectRotation_displacement_modulus
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Commute K.starProjection (nonacuteDirectRotation K L J - 1).modulus := by
  let R := nonacuteDirectRotation K L J
  let C := Proposition35.section3CosAngleOperator K L
  have hunit : star R * R = 1 :=
    Unitary.star_mul_self_of_mem (nonacuteDirectRotation_mem_unitary K L J)
  have hsum : R + star R = C + C := nonacuteDirectRotation_add_star_eq_two_cosine K L J
  have hgram : star (R - 1) * (R - 1) = (1 - C) + (1 - C) := by
    rw [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one, hunit]
    calc
      _ = (1 + 1) - (R + star R) := by abel
      _ = (1 + 1) - (C + C) := by rw [hsum]
      _ = _ := by abel
  apply ContinuousLinearMap.commute_modulus_of_commute
  change Commute K.starProjection (star (R - 1) * (R - 1))
  rw [hgram]
  have hPC : Commute K.starProjection C :=
    (Proposition35.section3CosAngleOperator_comm_projection K L).symm
  exact ((Commute.one_right _).sub_right hPC).add_right
    ((Commute.one_right _).sub_right hPC)

/-- Every compact canonical transport admits arbitrarily close finite
truncations on common reducing subspaces of the original projection
pair. The action on the retained block is the actual ambient rotation;
every accepted displacement ideal gauge decreases. -/
theorem exists_finite_canonical_approximation
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[𝕜] E))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : E ≃ₗᵢ[𝕜] E, ∃ M : Submodule 𝕜 E, ∃ _ : FiniteDimensional 𝕜 M,
      ‖(V : E →L[𝕜] E) - nonacuteDirectRotation K L J‖ ≤ ε ∧
      M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧
      (∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M) ∧
      (∀ x ∈ M, V x = nonacuteDirectRotation K L J x) ∧
      (∀ x ∈ Mᗮ, V x = x) ∧
      ∀ Φ : OperatorIdealFamily.{u, v, v} 𝕜,
        Φ.gauge (1 - (V : E →L[𝕜] E)) ≤
          Φ.gauge (1 - nonacuteDirectRotation K L J) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[𝕜] E))
  obtain ⟨B, hfactor, _⟩ := exists_nonacuteDirectRotation_displacement_factor K L J
  have hcompact : IsCompactOperator (((R : E →L[𝕜] E) - 1) : E →L[𝕜] E) := by
    rw [← neg_sub 1 (R : E →L[𝕜] E)]
    apply IsCompactOperator.neg
    change IsCompactOperator ((1 : E →L[𝕜] E) - nonacuteDirectRotation K L J)
    rw [hfactor]
    exact hD.comp_clm B
  obtain ⟨V, _, _, hnorm, _, hcost, _, _, M, hM, hRM, hVM, hfix, hred⟩ :=
    exists_finite_unitary_approximation R hcompact ε hε
  let : FiniteDimensional 𝕜 M := hM
  have hK : M.IsReducing K.starProjection.toLinearMap :=
    hred K.starProjection (isStarProjection_starProjection.isSelfAdjoint)
      (commute_starProjection_nonacuteDirectRotation_displacement_modulus K L J)
  obtain ⟨RM, hRM', _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  have hL : M.IsReducing L.starProjection.toLinearMap := by
    apply (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
    intro x hx
    change L.starProjection x ∈ M
    have h := K.starProjection_map_mem_of_isometry_restriction M R RM hRM'
      hK.mem_invtSubmodule x hx
    simpa only [hmap] using h
  exact ⟨V, M, hM, hnorm, hK, hL, hRM, hVM, hfix, hcost⟩

end TauCeti.DavisKahan
