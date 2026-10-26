/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import ForTauCeti.Analysis.InnerProductSpace.Positive.SquareRoot.Eigenspace

/-!
# Orthogonal projections and principal sines on invariant subspaces

If the orthogonal projection onto `K` preserves `Z`, its restriction to `Z`
is the orthogonal projection onto `K.comap Z.subtype`. The characterization
of an orthogonal projection by membership and an orthogonal residual proves
this without a choice of coordinates.

For a pair of such reducing projections, a nonnegative sine eigenvalue on
the restricted pair is also a sine eigenvalue on the ambient pair. Compute
the square using the restricted projection difference, then use positivity
of the ambient sine operator. This supplies the kernel contribution when
assembling spectral principal-angle sums.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A closed ambient subspace has an orthogonal projection after
intersection with any complete subspace carrier. -/
theorem hasOrthogonalProjection_comap_subtype_of_complete
    (K Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [CompleteSpace Z] :
    (K.comap Z.subtype).HasOrthogonalProjection := by
  apply hasOrthogonalProjection_iff_isClosed.mpr
  exact K.isClosed_of_hasOrthogonalProjection.preimage continuous_subtype_val

/-- Restricting an ambient subspace transport to an invariant carrier
transports the two actual intersections on that carrier. -/
theorem map_comap_subtype_of_isometry_restriction
    (K L Z : Submodule 𝕜 E) (U : E ≃ₗᵢ[𝕜] E) (R : Z ≃ₗᵢ[𝕜] Z)
    (hmap : K.map U.toLinearMap = L) (hR : ∀ z : Z, (R z : E) = U z) :
    (K.comap Z.subtype).map R.toLinearMap = L.comap Z.subtype := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change (R x : E) ∈ L
    rw [hR, ← hmap]
    exact Submodule.mem_map_of_mem hx
  · intro y hy
    have hyL : (y : E) ∈ L := hy
    have hu : U (R.symm y : E) = (y : E) := by
      rw [← hR, R.apply_symm_apply]
    have hpre : (R.symm y : E) ∈ K := by
      rw [← hmap] at hyL
      obtain ⟨x, hx, hxy⟩ := hyL
      have heq : (R.symm y : E) = x := U.injective (hu.trans hxy.symm)
      rwa [heq]
    exact ⟨R.symm y, hpre, R.apply_symm_apply y⟩

/-- If an isometry restricts surjectively to an invariant carrier, source
projection invariance implies invariance under the transported projection.
The inverse on the carrier is supplied by the actual restricted isometry,
so this also applies in infinite dimension without an invariance-to-reduction
assumption for an arbitrary infinite-dimensional invariant subspace. -/
theorem starProjection_map_mem_of_isometry_restriction
    (K Z : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (R : Z ≃ₗᵢ[𝕜] Z)
    (hR : ∀ z : Z, (R z : E) = U z)
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z) :
    ∀ x ∈ Z, (K.map U.toLinearMap).starProjection x ∈ Z := by
  intro x hx
  have hpre : U.symm x = (R.symm ⟨x, hx⟩ : E) := by
    apply U.injective
    rw [U.apply_symm_apply, ← hR, R.apply_symm_apply]
  rw [starProjection_map_apply, hpre]
  let y : Z := ⟨K.starProjection (R.symm ⟨x, hx⟩ : E),
    hK _ (R.symm ⟨x, hx⟩).property⟩
  change U (y : E) ∈ Z
  rw [← hR]
  exact (R y).property

/-- An invariant ambient orthogonal projection restricts to the projection
onto the intersection, expressed on the subspace carrier. -/
theorem starProjection_comap_subtype_apply_of_invariant
    (K Z : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    (hinv : ∀ x ∈ Z, K.starProjection x ∈ Z) (x : Z) :
    (((K.comap Z.subtype).starProjection x : Z) : E) = K.starProjection x := by
  let v : Z := ⟨K.starProjection x, hinv x x.property⟩
  have hproj : (K.comap Z.subtype).starProjection x = v := by
    apply eq_starProjection_of_mem_of_inner_eq_zero
    · exact K.starProjection_apply_mem x
    · intro y hy
      change inner 𝕜 ((x : E) - K.starProjection x) (y : E) = 0
      exact K.starProjection_inner_eq_zero x y hy
  exact congrArg (fun y : Z => (y : E)) hproj

/-- The restricted directed sine map is the directed sine map of the
actual intersections on the invariant carrier. The ambient space and
the carrier may both be infinite-dimensional. -/
theorem sinThetaMap_comap_subtype_apply_of_invariant
    (K L Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) (x : Z) :
    (((K.comap Z.subtype).sinThetaMap (L.comap Z.subtype) x : Z) : E) =
      K.sinThetaMap L (x : E) := by
  have horth (y : Z) :
      (((L.comap Z.subtype)ᗮ.starProjection y : Z) : E) = Lᗮ.starProjection (y : E) := by
    rw [starProjection_orthogonal, starProjection_orthogonal]
    change (y : E) - ((L.comap Z.subtype).starProjection y : E) =
      (y : E) - L.starProjection y
    rw [L.starProjection_comap_subtype_apply_of_invariant Z hL]
  rw [sinThetaMap_apply, sinThetaMap_apply, horth,
    K.starProjection_comap_subtype_apply_of_invariant Z hK]

/-- The projection difference of the actual restricted pair is the
compression of the ambient difference on a common invariant carrier. -/
theorem projection_sub_comap_subtype_eq_compression_of_invariant
    (K L Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) :
    (K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection =
      Z.orthogonalProjectionOnto ∘L (K.starProjection - L.starProjection) ∘L Z.subtypeL := by
  have hpoint (x : Z) :
      (((K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection) x : E) =
        (K.starProjection - L.starProjection) (x : E) := by
    change ((K.comap Z.subtype).starProjection x : E) -
      ((L.comap Z.subtype).starProjection x : E) = _
    rw [K.starProjection_comap_subtype_apply_of_invariant Z hK,
      L.starProjection_comap_subtype_apply_of_invariant Z hL]
    rfl
  apply ContinuousLinearMap.ext
  intro x
  change _ = Z.orthogonalProjectionOnto ((K.starProjection - L.starProjection) (x : E))
  rw [← hpoint, Z.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The gap of the actual restricted pair is bounded by the operator
norm of the ambient projection difference on that carrier. The carrier
and ambient space may both be infinite-dimensional. -/
theorem projectionGap_comap_subtype_le_norm_projection_sub_comp
    (K L Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) :
    (K.comap Z.subtype).projectionGap (L.comap Z.subtype) ≤
      ‖(K.starProjection - L.starProjection) ∘L Z.subtypeL‖ := by
  rw [projectionGap_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hnorm :
      ‖((K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection) x‖ =
        ‖(K.starProjection - L.starProjection) (x : E)‖ := by
    change ‖(((K.comap Z.subtype).starProjection x : Z) : E) -
      (((L.comap Z.subtype).starProjection x : Z) : E)‖ = ‖_‖
    rw [K.starProjection_comap_subtype_apply_of_invariant Z hK,
      L.starProjection_comap_subtype_apply_of_invariant Z hL]
    rfl
  rw [hnorm]
  exact ((K.starProjection - L.starProjection) ∘L Z.subtypeL).le_opNorm x

/-- Restriction to a common invariant carrier cannot increase the
projection gap, in either finite or infinite dimension. -/
theorem projectionGap_comap_subtype_le_of_invariant
    (K L Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection]
    [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) :
    (K.comap Z.subtype).projectionGap (L.comap Z.subtype) ≤ K.projectionGap L := by
  calc
    _ ≤ ‖(K.starProjection - L.starProjection) ∘L Z.subtypeL‖ :=
      K.projectionGap_comap_subtype_le_norm_projection_sub_comp L Z hK hL
    _ ≤ ‖K.starProjection - L.starProjection‖ * ‖Z.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖K.starProjection - L.starProjection‖ * 1 :=
      mul_le_mul_of_nonneg_left Z.norm_subtypeL_le (norm_nonneg _)
    _ = K.projectionGap L := by rw [mul_one, projectionGap_def]

/-- Restriction to a subspace invariant under the target projection cannot
increase the directed gap. The source projection need not preserve it. -/
theorem directedProjectionGap_comap_subtype_le_of_invariant
    (K L Z : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection] [(L.comap Z.subtype).HasOrthogonalProjection]
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) :
    (K.comap Z.subtype).directedProjectionGap (L.comap Z.subtype) ≤
      K.directedProjectionGap L := by
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  apply (K₀.directedProjectionGap_le_iff L₀ (K.directedProjectionGap_nonneg L)).mpr
  intro x hx
  have hproj := starProjection_comap_subtype_apply_of_invariant L Z hL x
  have hnorm : ‖L₀ᗮ.starProjection x‖ = ‖Lᗮ.starProjection (x : E)‖ := by
    rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
    change ‖(x : E) - (L₀.starProjection x : E)‖ = ‖(x : E) - L.starProjection x‖
    rw [hproj]
  rw [hnorm]
  exact (K.directedProjectionGap_le_iff L (K.directedProjectionGap_nonneg L)).mp
    le_rfl x hx

/-- Acuteness survives restriction to a subspace invariant under the
target orthogonal projection. -/
theorem principalAngles_comap_lt_pi_div_two_of_invariant [FiniteDimensional 𝕜 E]
    (K L Z : Submodule 𝕜 E)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z)
    (hacute : ∀ i : ℕ, K.principalAngles L i < Real.pi / 2) :
    ∀ i : ℕ, (K.comap Z.subtype).principalAngles (L.comap Z.subtype) i < Real.pi / 2 := by
  apply ((K.comap Z.subtype).forall_principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one
    (L.comap Z.subtype)).mpr
  exact (directedProjectionGap_comap_subtype_le_of_invariant K L Z hL).trans_lt
    ((K.forall_principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one L).mp hacute)

/-- A nonnegative principal-sine eigenvalue of an invariant subspace pair
is also a sine eigenvalue for the ambient pair. -/
theorem sinAngleOperator_apply_of_comap_eigenvector [CompleteSpace E]
    (K L Z : Submodule 𝕜 E) [CompleteSpace Z]
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [(K.comap Z.subtype).HasOrthogonalProjection] [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z)
    (x : Z) (s : ℝ) (hs : 0 ≤ s)
    (hx : (K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype) x = (s : 𝕜) • x) :
    K.sinAngleOperator L (x : E) = (s : 𝕜) • (x : E) := by
  let S := K.sinAngleOperator L
  let D := K.starProjection - L.starProjection
  let S₀ := (K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype)
  let D₀ := (K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection
  have hD (y : Z) : (D₀ y : E) = D (y : E) := by
    change ((K.comap Z.subtype).starProjection y : E) -
      ((L.comap Z.subtype).starProjection y : E) = _
    rw [starProjection_comap_subtype_apply_of_invariant K Z hK,
      starProjection_comap_subtype_apply_of_invariant L Z hL]
    rfl
  have hDsq : (D₀ (D₀ x) : E) = D (D (x : E)) := by rw [hD, hD]
  have hS₀sq : S₀ * S₀ = D₀ * D₀ := by
    simpa only [sq] using (K.comap Z.subtype).sinAngleOperator_sq (L.comap Z.subtype)
  have hscalar : D (D (x : E)) = ((s : 𝕜) * (s : 𝕜)) • (x : E) := by
    rw [← hDsq]
    have h := congrArg (fun T : Z →L[𝕜] Z => (T x : E)) hS₀sq
    change (S₀ (S₀ x) : E) = (D₀ (D₀ x) : E) at h
    rw [← h]
    change ((S₀ (S₀ x) : Z) : E) = _
    change S₀ x = (s : 𝕜) • x at hx
    rw [hx, map_smul, hx, smul_smul]
    rfl
  have hS : S.toLinearMap.IsPositive := (K.isPositive_sinAngleOperator L).toLinearMap
  apply hS.apply_eq_smul_of_apply_apply_eq_smul hs
  have h := congrArg (fun T : E →L[𝕜] E => T (x : E)) (K.sinAngleOperator_sq L)
  change S (S (x : E)) = D (D (x : E)) at h
  exact h.trans hscalar


/-- On any orthogonally complemented common reducing subspace, the
ambient sine operator is exactly the sine of the actual restricted pair.
Neither the carrier nor the ambient space needs finite dimension. -/
theorem sinAngleOperator_comap_subtype_apply_of_invariant
    [CompleteSpace E] (K L Z : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [(K.comap Z.subtype).HasOrthogonalProjection] [(L.comap Z.subtype).HasOrthogonalProjection]
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z) (x : Z) :
    (((K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype) x : Z) : E) =
      K.sinAngleOperator L (x : E) := by
  let D := K.starProjection - L.starProjection
  let D₀ := (K.comap Z.subtype).starProjection - (L.comap Z.subtype).starProjection
  let S := K.sinAngleOperator L
  let S₀ := Z.orthogonalProjectionOnto ∘L S ∘L Z.subtypeL
  have hZD : Commute Z.starProjection D :=
    (isReducing_coe_iff_commute_starProjection.mp
      ((K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr hK)).sub_right
    (isReducing_coe_iff_commute_starProjection.mp
      ((L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr hL))
  have hDself : IsSelfAdjoint D :=
    (isSelfAdjoint_starProjection K).sub (isSelfAdjoint_starProjection L)
  have hZS : Commute Z.starProjection S := by
    change Commute Z.starProjection (K.sinAngleOperator L)
    rw [sinAngleOperator_def]
    apply ContinuousLinearMap.commute_modulus_of_commute
    change Commute Z.starProjection (star D * D)
    rw [hDself.star_eq]
    exact hZD.mul_right hZD
  have hSred : Z.IsReducing S.toLinearMap := isReducing_coe_iff_commute_starProjection.mpr hZS
  have hS₀ (y : Z) : (S₀ y : E) = S (y : E) := by
    change Z.starProjection (S (y : E)) = S (y : E)
    exact Z.starProjection_eq_self_iff.mpr (hSred.mem_invtSubmodule y.property)
  have hD₀ (y : Z) : (D₀ y : E) = D (y : E) := by
    change ((K.comap Z.subtype).starProjection y : E) -
      ((L.comap Z.subtype).starProjection y : E) = _
    rw [K.starProjection_comap_subtype_apply_of_invariant Z hK,
      L.starProjection_comap_subtype_apply_of_invariant Z hL]
    rfl
  have hmod : S₀ = D₀.modulus := by
    apply ContinuousLinearMap.eq_modulus_iff.mpr
    refine ⟨(K.isPositive_sinAngleOperator L).orthogonalProjectionOnto_comp Z, ?_⟩
    have hD₀self : IsSelfAdjoint D₀ :=
      (isSelfAdjoint_starProjection _).sub (isSelfAdjoint_starProjection _)
    rw [hD₀self.adjoint_eq]
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    change (S₀ (S₀ y) : E) = (D₀ (D₀ y) : E)
    rw [hS₀, hS₀, hD₀, hD₀]
    exact congrArg (fun A : E →L[𝕜] E => A (y : E)) (K.sinAngleOperator_sq L)
  rw [sinAngleOperator_def]
  change (D₀.modulus x : E) = S (x : E)
  rw [← hmod]
  exact hS₀ x

end Submodule
