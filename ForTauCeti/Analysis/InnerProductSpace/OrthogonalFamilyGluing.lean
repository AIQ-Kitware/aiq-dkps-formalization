/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.FiniteBlocks
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace

/-!
# Gluing an actual finite orthogonal family of transports

Use Mathlib's internal orthogonal-sum isometry into `PiLp 2`, apply the
given isometries in each coordinate, and return to the ambient space.
The restriction equations identify the actual map on every summand.
For a pair of reducing projections, local subspace transports then give
an ambient transport. Finite Schatten displacement powers add exactly.

This is the constructive assembly step for transport matchings. It does
not assume that a matching has already been realized by geometric blocks.
Empty index types and zero summands are allowed.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Isometries of a complete finite orthogonal family glue to one ambient
isometry. Finite-dimensionality and completeness are not needed for this
finite orthogonal-sum construction. -/
theorem exists_linearIsometryEquiv_of_orthogonal_blocks
    {ι : Type*} [Finite ι] (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤) (V : ∀ i, W i ≃ₗᵢ[𝕜] W i) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ i, ∀ x : W i, U (x : E) = (V i x : E) := by
  classical
  let := Fintype.ofFinite ι
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top horth.independent hspan
  let e := hint.isometryL2OfOrthogonalFamily horth
  have hsingle (i : ι) (x : W i) : e.symm (PiLp.single 2 i x) = (x : E) := by
    rw [DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have he (i : ι) (x : W i) : e (x : E) = PiLp.single 2 i x := by
    apply e.symm.injective
    rw [e.symm_apply_apply, hsingle]
  let U := (e.trans (LinearIsometryEquiv.piLpCongrRight 2 V)).trans e.symm
  refine ⟨U, fun i x => ?_⟩
  change e.symm (LinearIsometryEquiv.piLpCongrRight 2 V (e (x : E))) = _
  rw [he, LinearIsometryEquiv.piLpCongrRight_single]
  exact hsingle i (V i x)

variable [FiniteDimensional 𝕜 E]

/-- Local orthogonal transports on actual reducing subspaces glue to an
ambient transport, with its actual finite Schatten power equal to the
sum of the chosen local powers. The statement supplies no minimizer or
principal-plane decomposition hypothesis beyond the displayed family. -/
theorem exists_transport_of_orthogonal_blocks
    {ι : Type*} [Fintype ι] (K L : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i)
    (V : ∀ i, W i ≃ₗᵢ[𝕜] W i)
    (hV : ∀ i, (K.comap (W i).subtype).map (V i).toLinearMap = L.comap (W i).subtype)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (∀ i, ∀ x : W i, U (x : E) = (V i x : E)) ∧
      UnitarilyInvariantSeminorm.schatten 𝕜 E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        ∑ i, UnitarilyInvariantSeminorm.schatten 𝕜 (W i) (W i) p
          (LinearMap.id - (V i).toLinearMap) ^ p.toReal := by
  classical
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_orthogonal_blocks W horth hspan V
  have hlocal (i : ι) (x : W i) :
      V i ((K.comap (W i).subtype).starProjection x) =
        (L.comap (W i).subtype).starProjection (V i x) := by
    have h := Submodule.starProjection_map_apply (V i) (K.comap (W i).subtype) (V i x)
    simpa only [hV i, (V i).symm_apply_apply] using h.symm
  have hcomm (i : ι) (x : E) (hx : x ∈ W i) :
      U (K.starProjection x) = L.starProjection (U x) := by
    let y : W i := ⟨x, hx⟩
    calc
      _ = U (((K.comap (W i).subtype).starProjection y : W i) : E) := by
        rw [K.starProjection_comap_subtype_apply_of_invariant (W i) (hK i)]
      _ = (V i ((K.comap (W i).subtype).starProjection y) : E) := hU i _
      _ = (((L.comap (W i).subtype).starProjection (V i y) : W i) : E) :=
        congrArg Subtype.val (hlocal i y)
      _ = L.starProjection (V i y : E) :=
        L.starProjection_comap_subtype_apply_of_invariant (W i) (hL i) _
      _ = _ := congrArg L.starProjection (hU i y).symm
  have hcommAll (x : E) : U (K.starProjection x) = L.starProjection (U x) := by
    let D := U.toLinearMap ∘ₗ K.starProjection.toLinearMap -
      L.starProjection.toLinearMap ∘ₗ U.toLinearMap
    have hker : (⨆ i, W i) ≤ D.ker := iSup_le (fun i x hx => by
      change U (K.starProjection x) - L.starProjection (U x) = 0
      exact sub_eq_zero.mpr (hcomm i x hx))
    have hx : x ∈ (⨆ i, W i) := by rw [hspan]; trivial
    exact sub_eq_zero.mp (hker hx)
  refine ⟨U, ?_, hU, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      apply L.starProjection_eq_self_iff.mp
      exact (hcommAll x).symm.trans (congrArg U (K.starProjection_eq_self_iff.mpr hx))
    · intro y hy
      have hpre : U.symm y ∈ K := by
        apply K.starProjection_eq_self_iff.mp
        apply U.injective
        rw [hcommAll, U.apply_symm_apply, L.starProjection_eq_self_iff.mpr hy]
      exact ⟨U.symm y, hpre, U.apply_symm_apply y⟩
  · have hinv : ∀ i, ∀ x ∈ W i, (U : E →L[𝕜] E) x ∈ W i := by
      intro i x hx
      change U x ∈ W i
      rw [hU i ⟨x, hx⟩]
      exact (V i ⟨x, hx⟩).property
    have hpow := schatten_displacement_rpow_of_orthogonal_blocks W horth hspan
      (U : E →L[𝕜] E) hinv p hp
    have hlin : (U : E →L[𝕜] E).toLinearMap = U.toLinearMap := by ext x; rfl
    rw [hlin] at hpow
    rw [hpow]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    apply LinearMap.ext
    intro x
    change x - (W i).orthogonalProjectionOnto (U x) = x - V i x
    rw [hU i x, (W i).orthogonalProjectionOnto_mem_subspace_eq_self]

end TauCeti
