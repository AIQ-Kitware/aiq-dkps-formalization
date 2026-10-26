/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NonacuteCompression
public import DavisKahan.Geometry.Polar.DirectRotationAcute
public import DavisKahan.Geometry.Angle.CosineKernel
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

/-!
# Canonical rotations on actual invariant subspaces

An actual unitary restriction of a completed direct rotation has the
positive diagonal compressions of a canonical rotation. On an acute
restricted pair, uniqueness of the polar factor identifies the restriction
with its canonical rotation. Neither ambient nor restricted space must
be finite-dimensional; both scalar fields and arbitrary ambient defect
completions are included.

The proof pulls each positive ambient diagonal compression back along
the subspace inclusion. This preserves self-adjointness as well as the
quadratic-form sign, which is necessary over the real field. The theorem
supplies the canonical-tail identification in Schatten optimization.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Both diagonal compressions of every completed canonical rotation
are positive operators, over either scalar field in arbitrary dimension. -/
theorem nonacuteDirectRotation_diagonal_compressions_isPositive
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    (K.starProjection * nonacuteDirectRotation K L J * K.starProjection).IsPositive ∧
      (Kᗮ.starProjection * nonacuteDirectRotation K L J * Kᗮ.starProjection).IsPositive := by
  let C := Proposition35.section3CosAngleOperator K L
  have hC : C.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hCP : Commute C K.starProjection :=
    Proposition35.section3CosAngleOperator_comm_projection K L
  have hCPc : Commute C Kᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal' K]
    exact (Commute.one_right C).sub_right hCP
  have hpositive (N : Submodule 𝕜 E) [N.HasOrthogonalProjection]
      (hCN : Commute C N.starProjection) : (C * N.starProjection).IsPositive := by
    have heq : N.starProjection * C * N.starProjection = C * N.starProjection := by
      rw [← hCN.eq, mul_assoc, N.isIdempotentElem_starProjection.eq]
    rw [← heq]
    exact hC.conj_starProjection N
  obtain ⟨hK, hKc⟩ := nonacuteDirectRotation_compressions_eq_cosine K L J
  rw [hK, hKc]
  exact ⟨hpositive K hCP, hpositive Kᗮ hCPc⟩

/-- On an acute pair every completed construction agrees with the
canonical polar factor. The defect completion introduces no freedom. -/
theorem nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hacute : K ⊓ Lᗮ = ⊥) (hacute' : Kᗮ ⊓ L = ⊥) :
    nonacuteDirectRotation K L J = spectraCanonicalPolarFactor K L := by
  obtain ⟨hpos, hposc⟩ := nonacuteDirectRotation_diagonal_compressions_isPositive K L J
  exact eq_spectraCanonicalPolarFactor_of_diagonalBlocks_isPositive K L hacute hacute'
    _ (nonacuteDirectRotation_mem_unitary K L J)
    (nonacuteDirectRotation_intertwines K L J) hpos hposc

omit [CompleteSpace E] in
private theorem compression_restrict_eq
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (P T : E →L[𝕜] E) (P₀ T₀ : M →L[𝕜] M)
    (hP : ∀ x : M, (P₀ x : E) = P x) (hT : ∀ x : M, (T₀ x : E) = T x) :
    P₀ * T₀ * P₀ = M.orthogonalProjectionOnto ∘L (P * T * P) ∘L M.subtypeL := by
  have hpoint (x : M) : ((P₀ * T₀ * P₀) x : E) = (P * T * P) (x : E) := by
    change (P₀ (T₀ (P₀ x)) : E) = P (T (P x))
    calc
      _ = P (T₀ (P₀ x) : E) := hP _
      _ = P (T (P₀ x : E)) := congrArg P (hT _)
      _ = _ := congrArg (fun y => P (T y)) (hP x)
  apply ContinuousLinearMap.ext
  intro x
  change (P₀ * T₀ * P₀) x = M.orthogonalProjectionOnto ((P * T * P) (x : E))
  rw [← hpoint, M.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- **Canonical restriction on an acute pair.** Every actual unitary
restriction of a completed ambient rotation equals the canonical polar
factor of the actual restricted pair when its crossed defects vanish.
The restricted space may be infinite-dimensional and need not contain
all of the ambient defects. -/
theorem nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute
    (K L M : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    [CompleteSpace M]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (V : M ≃ₗᵢ[𝕜] M)
    (hV : ∀ x : M, (V x : E) = nonacuteDirectRotation K L J x)
    (hK : ∀ x ∈ M, K.starProjection x ∈ M)
    (hacute : (K.comap M.subtype) ⊓ (L.comap M.subtype)ᗮ = ⊥)
    (hacute' : (K.comap M.subtype)ᗮ ⊓ (L.comap M.subtype) = ⊥) :
    (V : M →L[𝕜] M) =
      spectraCanonicalPolarFactor (K.comap M.subtype) (L.comap M.subtype) := by
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[𝕜] E))
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L J
  have hmap : K₀.map V.toLinearMap = L₀ :=
    K.map_comap_subtype_of_isometry_restriction L M R V hRmap hV
  have hinter : (V : M →L[𝕜] M) * K₀.starProjection =
      L₀.starProjection * (V : M →L[𝕜] M) := by
    apply ContinuousLinearMap.ext
    intro x
    change V (K₀.starProjection x) = L₀.starProjection (V x)
    have h := Submodule.starProjection_map_apply V K₀ (V x)
    simpa only [hmap, V.symm_apply_apply] using h.symm
  have hP (x : M) : (K₀.starProjection x : E) = K.starProjection x :=
    K.starProjection_comap_subtype_apply_of_invariant M hK x
  have hPc (x : M) : (K₀ᗮ.starProjection x : E) = Kᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
    change (x : E) - (K₀.starProjection x : E) = (x : E) - K.starProjection x
    rw [hP]
  obtain ⟨hpos, hposc⟩ := nonacuteDirectRotation_diagonal_compressions_isPositive K L J
  apply eq_spectraCanonicalPolarFactor_of_diagonalBlocks_isPositive K₀ L₀
    hacute hacute' (V : M →L[𝕜] M) (Unitary.linearIsometryEquiv.symm V).property hinter
  · rw [compression_restrict_eq M K.starProjection _ K₀.starProjection
      (V : M →L[𝕜] M) hP hV]
    exact hpos.orthogonalProjectionOnto_comp M
  · rw [compression_restrict_eq M Kᗮ.starProjection _ K₀ᗮ.starProjection
      (V : M →L[𝕜] M) hPc hV]
    exact hposc.orthogonalProjectionOnto_comp M

/-- A reducing acute sector of a completed ambient rotation carries
its actual canonical unitary, with both forward and inverse actions
inherited from the ambient rotation. Infinite sectors are included. -/
theorem exists_canonical_restriction_of_acute_reducing_pair
    (K L M : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    [CompleteSpace M]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hM : M.IsReducing (nonacuteDirectRotation K L J).toLinearMap)
    (hK : ∀ x ∈ M, K.starProjection x ∈ M)
    (hacute : (K.comap M.subtype) ⊓ (L.comap M.subtype)ᗮ = ⊥)
    (hacute' : (K.comap M.subtype)ᗮ ⊓ (L.comap M.subtype) = ⊥) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = nonacuteDirectRotation K L J x) ∧
      (∀ x : M, (V.symm x : E) = star (nonacuteDirectRotation K L J) x) ∧
      (V : M →L[𝕜] M) =
        spectraCanonicalPolarFactor (K.comap M.subtype) (L.comap M.subtype) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[𝕜] E))
  obtain ⟨V, hV, hVs⟩ := R.exists_restriction_of_reducing M hM
  refine ⟨V, hV, ?_, nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute
    K L M J V hV hK hacute hacute'⟩
  intro x
  have hs : star (R : E →L[𝕜] E) = (R.symm : E →L[𝕜] E) := R.adjoint_eq_symm
  change (V.symm x : E) = star (R : E →L[𝕜] E) x
  rw [hs]
  exact hVs x

end TauCeti.DavisKahan
