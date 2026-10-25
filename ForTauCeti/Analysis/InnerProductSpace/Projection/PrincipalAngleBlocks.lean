/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.FiniteBlocks

/-!
# Principal angles on a complete orthogonal invariant decomposition

The actual restricted directed sine maps are the restrictions of the
ambient directed sine map. Full finite singular-value additivity then
assembles all zero-preserving angle penalties. The sums use the accepted
principal angles and the actual source ranks, without an acute-pair or
equal-rank assumption.
-/

public section

noncomputable section

namespace Submodule

open TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Source-rank indexing counts every nonzero accepted angle and includes
the actual source's zero-angle multiplicity. Zero-preserving penalties
may equivalently be summed over the full ambient index set. -/
theorem sum_principalAngles_eq_sum_ambient
    (K L : Submodule 𝕜 E) {M : Type*} [AddCommMonoid M] (f : ℝ → M) (hf : f 0 = 0) :
    (∑ j : Fin (Module.finrank 𝕜 K), f (K.principalAngles L j)) =
      ∑ j : Fin (Module.finrank 𝕜 E), f (K.principalAngles L j) := by
  classical
  have hs : (K.principalAngles L).support ⊆ Finset.range (Module.finrank 𝕜 K) := by
    intro j hj
    by_contra hnot
    have hzero := K.principalAngles_of_finrank_le L
      (Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h)))
    exact Finsupp.mem_support_iff.mp hj hzero
  have he : (K.principalAngles L).support ⊆ Finset.range (Module.finrank 𝕜 E) :=
    hs.trans (Finset.range_subset_range.mpr K.finrank_le)
  rw [Fin.sum_univ_eq_sum_range (fun j => f (K.principalAngles L j)),
    Fin.sum_univ_eq_sum_range (fun j => f (K.principalAngles L j))]
  exact (Finsupp.sum_of_support_subset (K.principalAngles L) hs
    (fun _ s => f s) (fun _ _ => hf)).symm.trans
      (Finsupp.sum_of_support_subset (K.principalAngles L) he (fun _ s => f s) (fun _ _ => hf))

/-- A zero-preserving angle penalty is a full singular-value penalty of
the actual directed sine map, with arcsine applied to every singular value. -/
theorem sum_principalAngles_eq_sum_singularValues_arcsin
    (K L : Submodule 𝕜 E) {M : Type*} [AddCommMonoid M] (f : ℝ → M) (hf : f 0 = 0) :
    (∑ j : Fin (Module.finrank 𝕜 K), f (K.principalAngles L j)) =
      ∑ j : Fin (Module.finrank 𝕜 E),
        f (Real.arcsin ((K.sinThetaMap L).toLinearMap.singularValues j)) := by
  rw [sum_principalAngles_eq_sum_ambient K L f hf]
  simp only [principalAngles_apply, principalSines_def]

/-- The restricted directed sine map is the directed sine map of the
actual intersections on the invariant carrier. -/
theorem sinThetaMap_comap_subtype_apply_of_invariant
    (K L Z : Submodule 𝕜 E)
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

/-- Every zero-preserving accepted principal-angle sum is additive on a
complete finite orthogonal family reducing both projections. All source
ranks and all zero, right and repeated principal angles are retained. -/
theorem sum_principalAngles_of_orthogonal_blocks
    {ι : Type*} [Fintype ι] (K L : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i)
    {M : Type*} [AddCommMonoid M] (f : ℝ → M) (hf : f 0 = 0) :
    (∑ j : Fin (Module.finrank 𝕜 K), f (K.principalAngles L j)) =
      ∑ i, ∑ j : Fin (Module.finrank 𝕜 (K.comap (W i).subtype)),
        f ((K.comap (W i).subtype).principalAngles (L.comap (W i).subtype) j) := by
  have hinv : ∀ i, ∀ x ∈ W i, K.sinThetaMap L x ∈ W i := by
    intro i x hx
    rw [sinThetaMap_apply, starProjection_orthogonal]
    change K.starProjection x - L.starProjection (K.starProjection x) ∈ W i
    exact (W i).sub_mem (hK i x hx) (hL i _ (hK i x hx))
  have hrestrict (i : ι) :
      (K.sinThetaMap L).toLinearMap.restrict (hinv i) =
        ((K.comap (W i).subtype).sinThetaMap (L.comap (W i).subtype)).toLinearMap := by
    ext x
    exact (sinThetaMap_comap_subtype_apply_of_invariant K L (W i) (hK i) (hL i) x).symm
  rw [sum_principalAngles_eq_sum_singularValues_arcsin K L f hf,
    sum_singularValues_of_orthogonal_blocks W horth hspan _ hinv (fun s => f (Real.arcsin s))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrestrict]
  exact (sum_principalAngles_eq_sum_singularValues_arcsin _ _ f hf).symm

/-- Source dimensions split over the same invariant orthogonal family.
This is the rank information needed to recover zero-angle multiplicities. -/
theorem finrank_comap_of_orthogonal_blocks
    {ι : Type*} [Fintype ι] (K : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i) :
    Module.finrank 𝕜 K = ∑ i, Module.finrank 𝕜 (K.comap (W i).subtype) := by
  have hrange : K.starProjection.toLinearMap.range = K := K.range_starProjection
  calc Module.finrank 𝕜 K = Module.finrank 𝕜 K.starProjection.toLinearMap.range := by
         rw [hrange]
       _ = _ := finrank_range_of_orthogonal_blocks W horth hspan _ hK
       _ = _ := ?_
  apply Finset.sum_congr rfl
  intro i _
  have hrestrict : K.starProjection.toLinearMap.restrict (hK i) =
      (K.comap (W i).subtype).starProjection.toLinearMap := by
    ext x
    exact (K.starProjection_comap_subtype_apply_of_invariant (W i) (hK i) x).symm
  rw [hrestrict]
  exact congrArg (fun S : Submodule 𝕜 (W i) => Module.finrank 𝕜 S)
    (K.comap (W i).subtype).range_starProjection

/-- For an additive group, arbitrary angle penalties assemble, with no
condition at zero. Source-rank additivity cancels the zero baseline. -/
theorem sum_principalAngles_of_orthogonal_blocks_group
    {ι : Type*} [Fintype ι] (K L : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i)
    {M : Type*} [AddCommGroup M] (f : ℝ → M) :
    (∑ j : Fin (Module.finrank 𝕜 K), f (K.principalAngles L j)) =
      ∑ i, ∑ j : Fin (Module.finrank 𝕜 (K.comap (W i).subtype)),
        f ((K.comap (W i).subtype).principalAngles (L.comap (W i).subtype) j) := by
  have h := sum_principalAngles_of_orthogonal_blocks K L W horth hspan hK hL
    (fun t => f t - f 0) (by simp)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] at h
  rw [← Finset.sum_smul, ← finrank_comap_of_orthogonal_blocks K W horth hspan hK] at h
  exact sub_left_inj.mp h

/-- The finite accepted principal-angle multiset, with exactly one entry
per source dimension. In contrast to its finitely supported angle sequence,
this multiset explicitly retains all zero-angle multiplicities. The body is
exposed so finite matching constructions can enumerate the actual entries. -/
@[expose] def principalAngleMultiset (K L : Submodule 𝕜 E) : Multiset ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank 𝕜 K))).val.map
    (fun j : Fin (Module.finrank 𝕜 K) => K.principalAngles L j)

@[simp] theorem card_principalAngleMultiset (K L : Submodule 𝕜 E) :
    (K.principalAngleMultiset L).card = Module.finrank 𝕜 K := by
  simp [principalAngleMultiset]

/-- Multiplicity of an angle in the source-indexed accepted multiset. -/
theorem count_principalAngleMultiset (K L : Submodule 𝕜 E) (t : ℝ) :
    (K.principalAngleMultiset L).count t =
      ∑ j : Fin (Module.finrank 𝕜 K), if t = K.principalAngles L j then 1 else 0 := by
  classical
  rw [principalAngleMultiset, Multiset.count_map, ← Finset.filter_val]
  change (Finset.univ.filter (fun j : Fin (Module.finrank 𝕜 K) =>
    t = K.principalAngles L j)).card = _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Exact multiset assembly of the original principal angles from the
actual reducing blocks. Every zero, repeated and right angle has its exact
multiplicity, and the projection ranks need not be equal. -/
theorem principalAngleMultiset_of_orthogonal_blocks
    {ι : Type*} [Fintype ι] (K L : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i) :
    K.principalAngleMultiset L =
      ∑ i, (K.comap (W i).subtype).principalAngleMultiset (L.comap (W i).subtype) := by
  classical
  apply Multiset.ext.mpr
  intro t
  rw [Multiset.count_sum', count_principalAngleMultiset]
  simp_rw [count_principalAngleMultiset]
  have h := sum_principalAngles_of_orthogonal_blocks_group K L W horth hspan hK hL
    (fun s => if t = s then (1 : ℤ) else 0)
  exact_mod_cast h

/-- A complete reducing decomposition labels the original accepted
principal-angle indices bijectively by the actual block indices. Equal
angles remain separate labels, including all zero slots. Construct the
bijection on each angle fiber using its exact multiplicity; this avoids
choosing distinct representatives for repeated spectral values. -/
theorem exists_equiv_principalAngleIndices_of_orthogonal_blocks
    {ι : Type*} [Finite ι] (K L : Submodule 𝕜 E) (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i) :
    ∃ e : Fin (Module.finrank 𝕜 K) ≃
        Σ i, Fin (Module.finrank 𝕜 (K.comap (W i).subtype)),
      ∀ j, (K.comap (W (e j).1).subtype).principalAngles
        (L.comap (W (e j).1).subtype) (e j).2 = K.principalAngles L j := by
  classical
  let := Fintype.ofFinite ι
  let f (j : Fin (Module.finrank 𝕜 K)) := K.principalAngles L j
  let g (x : Σ i, Fin (Module.finrank 𝕜 (K.comap (W i).subtype))) :=
    (K.comap (W x.1).subtype).principalAngles (L.comap (W x.1).subtype) x.2
  have hcard (t : ℝ) : Fintype.card {j // f j = t} = Fintype.card {x // g x = t} := by
    simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_sigma]
    have h := sum_principalAngles_of_orthogonal_blocks_group K L W horth hspan hK hL
      (fun s => if s = t then (1 : ℤ) else 0)
    exact_mod_cast h
  let e (t : ℝ) := Fintype.equivOfCardEq (hcard t)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

end Submodule
