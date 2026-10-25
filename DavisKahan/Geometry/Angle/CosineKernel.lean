/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.Geometry.Angle.Proposition35Nonacute
import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Geometry of the right-angle cosine kernel

The kernel of the principal cosine is the actual crossed-defect sum.
Source and target reflections are opposite there. A cosine-preserving
transporter consequently anticommutes with source reflection on this
kernel, also in infinite dimension. These are geometric reductions for
assembling exceptional optimizer blocks; no ideal attainment is asserted.
-/

noncomputable section

namespace TauCeti.DavisKahan.Proposition35

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The principal cosine commutes with the source orthogonal projection. -/
theorem section3CosAngleOperator_comm_projection
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    Commute (section3CosAngleOperator K L) K.starProjection := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue]
  exact (ContinuousLinearMap.commute_modulus_of_commute
    (commute_projection_spectraCanonicalIntertwiner_star_mul_self K L)).symm

/-- Source reflection preserves the actual right-angle kernel. -/
theorem reflection_mem_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (x : H) (hx : section3CosAngleOperator K L x = 0) :
    section3CosAngleOperator K L (K.reflection x) = 0 := by
  have hP := DFunLike.congr_fun (section3CosAngleOperator_comm_projection K L).eq x
  change section3CosAngleOperator K L (K.starProjection x) =
    K.starProjection (section3CosAngleOperator K L x) at hP
  rw [Submodule.reflection_apply, map_sub, map_nsmul, hP, hx, map_zero]
  simp

/-- The right-angle space is exactly the sum of the two crossed defects. -/
theorem ker_section3CosAngleOperator_eq_crossedDefectSum
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (section3CosAngleOperator K L).ker = crossedDefectSum K L := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue, ContinuousLinearMap.ker_modulus]
  exact ker_canonicalIntertwiner_eq_crossedDefectSum K L

/-- The two reflections are opposite on the whole right-angle space,
without a choice of pairing between the defect spaces. -/
theorem reflection_eq_neg_on_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (x : H) (hx : section3CosAngleOperator K L x = 0) :
    L.reflection x = -K.reflection x := by
  have hxmem : x ∈ (section3CosAngleOperator K L).ker := hx
  rw [ker_section3CosAngleOperator_eq_crossedDefectSum] at hxmem
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨huK, huL⟩ := mem_halmosSourceDefect.mp hu
  obtain ⟨hvK, hvL⟩ := mem_halmosTargetDefect.mp hv
  rw [map_add, map_add,
    Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg huL,
    Submodule.reflection_mem_subspace_eq_self hvL,
    Submodule.reflection_mem_subspace_eq_self huK,
    Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvK]
  abel

/-- A transporter preserving the principal cosine anticommutes with
source reflection on its right-angle kernel. This is the actual ambient
transporter, without a supplied block decomposition. -/
theorem transport_anticommutes_reflection_on_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H ≃ₗᵢ[𝕜] H) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : H →L[𝕜] H) (section3CosAngleOperator K L))
    (x : H) (hx : section3CosAngleOperator K L x = 0) :
    T (K.reflection x) = -K.reflection (T x) := by
  have hker : section3CosAngleOperator K L (T x) = 0 := by
    have h := DFunLike.congr_fun hTC.eq x
    change T (section3CosAngleOperator K L x) = section3CosAngleOperator K L (T x) at h
    rw [hx, map_zero] at h
    exact h.symm
  rw [(K.map_eq_iff_intertwines_reflection L T).mp hT x]
  exact reflection_eq_neg_on_cosine_kernel K L (T x) hker

/-- A feasible unitary self-adjoint on the right-angle kernel determines
exactly one unitary identification of the crossed defects. Its action on
the other defect is the inverse identification. No finite dimension or
cosine-commutation hypothesis is needed for this implication. -/
theorem exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H ≃ₗᵢ[𝕜] H) (hT : K.map T.toLinearMap = L)
    (hself : ∀ x : H, section3CosAngleOperator K L x = 0 →
      T x = star (T : H →L[𝕜] H) x) :
    ∃! D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L,
      (∀ x : halmosSourceDefect K L, T x = (D x : H)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : H)) := by
  have hsrc : halmosSourceDefect K L ≤ (section3CosAngleOperator K L).ker := by
    rw [ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact le_sup_left
  have htgt : halmosTargetDefect K L ≤ (section3CosAngleOperator K L).ker := by
    rw [ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact le_sup_right
  have hself' (x : H) (hx : section3CosAngleOperator K L x = 0) : T x = T.symm x := by
    have h := hself x hx
    rw [show star (T : H →L[𝕜] H) = (T.symm : H →L[𝕜] H) from T.adjoint_eq_symm] at h
    exact h
  have hTT (x : H) (hx : section3CosAngleOperator K L x = 0) : T (T x) = x := by
    rw [hself' x hx, T.apply_symm_apply]
  have hTp : Kᗮ.map T.toLinearMap = Lᗮ := by
    rw [Submodule.map_orthogonal_equiv, hT]
  have hforward (x : halmosSourceDefect K L) : T (x : H) ∈ halmosTargetDefect K L := by
    obtain ⟨hxK, hxL⟩ := mem_halmosSourceDefect.mp x.property
    apply mem_halmosTargetDefect.mpr
    refine ⟨?_, ?_⟩
    · rw [hself' x (hsrc x.property)]
      have hx : (x : H) ∈ Kᗮ.map T.toLinearMap := by rwa [hTp]
      obtain ⟨y, hy, heq⟩ := hx
      change T y = (x : H) at heq
      rw [← heq, T.symm_apply_apply]
      exact hy
    · have hx : T (x : H) ∈ K.map T.toLinearMap := ⟨x, hxK, rfl⟩
      exact hT ▸ hx
  have hbackward (y : halmosTargetDefect K L) : T (y : H) ∈ halmosSourceDefect K L := by
    obtain ⟨hyK, hyL⟩ := mem_halmosTargetDefect.mp y.property
    apply mem_halmosSourceDefect.mpr
    refine ⟨?_, ?_⟩
    · rw [hself' y (htgt y.property)]
      have hy : (y : H) ∈ K.map T.toLinearMap := by rwa [hT]
      obtain ⟨x, hx, heq⟩ := hy
      change T x = (y : H) at heq
      rw [← heq, T.symm_apply_apply]
      exact hx
    · have hy : T (y : H) ∈ Kᗮ.map T.toLinearMap := ⟨y, hyK, rfl⟩
      exact hTp ▸ hy
  let v : halmosSourceDefect K L →ₗᵢ[𝕜] halmosTargetDefect K L :=
    { T.toLinearMap.restrict (fun x hx => hforward ⟨x, hx⟩) with
      norm_map' := fun x => T.norm_map x }
  have hvsurj : Function.Surjective v := by
    intro y
    refine ⟨⟨T y, hbackward y⟩, ?_⟩
    apply Subtype.ext
    exact hTT y (htgt y.property)
  let D := LinearIsometryEquiv.ofSurjective v hvsurj
  have hD (x : halmosSourceDefect K L) : (D x : H) = T x := rfl
  have hDinv (y : halmosTargetDefect K L) : T y = (D.symm y : H) := by
    apply T.injective
    calc
      T (T y) = (y : H) := hTT y (htgt y.property)
      _ = (D (D.symm y) : H) := by rw [D.apply_symm_apply]
      _ = T (D.symm y) := hD _
  refine ⟨D, ⟨fun x => (hD x).symm, hDinv⟩, ?_⟩
  intro D' hD'
  ext x
  exact (hD'.1 x).symm.trans (hD x).symm

/-- Prescribing a defect isometry and its inverse forces the ambient
transporter to be self-adjoint on the entire cosine kernel. The two
defect summands need not have finite dimension. -/
theorem selfAdjoint_on_cosine_kernel_of_defect_equiv
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H ≃ₗᵢ[𝕜] H)
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hsrc : ∀ x : halmosSourceDefect K L, T x = (D x : H))
    (htgt : ∀ y : halmosTargetDefect K L, T y = (D.symm y : H)) :
    ∀ x : H, section3CosAngleOperator K L x = 0 →
      T x = star (T : H →L[𝕜] H) x := by
  have hTTsrc (u : halmosSourceDefect K L) : T (T u) = u := by
    rw [hsrc, htgt, D.symm_apply_apply]
  have hTTtgt (v : halmosTargetDefect K L) : T (T v) = v := by
    rw [htgt, hsrc, D.apply_symm_apply]
  intro x hx
  have hxmem : x ∈ (section3CosAngleOperator K L).ker := hx
  rw [ker_section3CosAngleOperator_eq_crossedDefectSum] at hxmem
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxmem
  rw [show star (T : H →L[𝕜] H) = (T.symm : H →L[𝕜] H) from T.adjoint_eq_symm]
  apply T.injective
  change T (T (u + v)) = T (T.symm (u + v))
  rw [T.apply_symm_apply, map_add, map_add, hTTsrc ⟨u, hu⟩, hTTtgt ⟨v, hv⟩]

/-- Self-adjoint action on the actual right-angle kernel is equivalent to
one defect isometry paired with its inverse. Feasibility suffices for the
necessary direction; neither dimension nor cosine commutation is assumed. -/
theorem selfAdjoint_on_cosine_kernel_iff_exists_defect_equiv
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H ≃ₗᵢ[𝕜] H) (hT : K.map T.toLinearMap = L) :
    (∀ x : H, section3CosAngleOperator K L x = 0 →
      T x = star (T : H →L[𝕜] H) x) ↔
      ∃ D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L,
        (∀ x : halmosSourceDefect K L, T x = (D x : H)) ∧
        (∀ y : halmosTargetDefect K L, T y = (D.symm y : H)) := by
  constructor
  · intro hself
    obtain ⟨D, hD, _⟩ := exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel K L T hT hself
    exact ⟨D, hD⟩
  · rintro ⟨D, hsrc, htgt⟩
    exact selfAdjoint_on_cosine_kernel_of_defect_equiv K L T D hsrc htgt

end TauCeti.DavisKahan.Proposition35
