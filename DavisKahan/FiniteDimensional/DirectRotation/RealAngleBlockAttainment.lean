/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealAngleCosts
import ForTauCeti.Analysis.InnerProductSpace.OrthogonalFamilyGluing
import ForTauCeti.Analysis.InnerProductSpace.Projection.CosineSineBlocks
import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-!
# Attainment on prescribed geometric real angle blocks

Choose the proved unrestricted minimum on every actual rank-one plane
and rank-two four-dimensional block. On every common source/target
summand choose identity. The accepted orthogonal-sum construction glues
these choices to an ambient transporter and preserves their cost sum.

The block family here is geometric input. Constructing such a family for
an arbitrary matching of the original positive angle labels is the next
step; this result alone makes no all-ambient optimality assertion.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A unitary conjugating the actual orthogonal projections transports
their source and target subspaces. -/
theorem map_eq_of_unitary_conjugate (K L : Submodule ℝ E)
    (U : unitary (E →L[ℝ] E))
    (htrans : (U : E →L[ℝ] E) * K.starProjection * star (U : E →L[ℝ] E) = L.starProjection) :
    K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
  let V := Unitary.linearIsometryEquiv U
  have hV : (V : E →L[ℝ] E) = (U : E →L[ℝ] E) :=
    Unitary.coe_linearIsometryEquiv_apply U
  have hs : star (U : E →L[ℝ] E) = (V.symm : E →L[ℝ] E) := by
    rw [← hV]
    exact V.adjoint_eq_symm
  have hP : (K.map V.toLinearMap).starProjection = L.starProjection := by
    ext x
    rw [Submodule.starProjection_map_apply]
    have h := congrArg (fun A : E →L[ℝ] E => A x) htrans
    change (U : E →L[ℝ] E) (K.starProjection (star (U : E →L[ℝ] E) x)) = L.starProjection x at h
    rw [hs, ← hV] at h
    exact h
  rw [← Submodule.range_starProjection (K.map V.toLinearMap),
    ← Submodule.range_starProjection L, hP]

/-- Every common block has zero explicit angle cost, in any dimension
and at every exponent at least one. -/
theorem realSchattenAngleBlockCost_self (p : ℝ) (hp : 1 ≤ p) (K : Submodule ℝ E) :
    realSchattenAngleBlockCost p K K = 0 := by
  classical
  simp [realSchattenAngleBlockCost, realPairSchattenCost, realSingleSchattenCost,
    Submodule.principalAngles_self, optimalPhase_zero p hp, phasePower, phaseChord,
    Real.zero_rpow (show p ≠ 0 by linarith), Real.rpow_nonneg]

private theorem exists_real_small_block_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E)
    (hclass : K = L ∨
      (Module.finrank ℝ E = 2 ∧ Module.finrank ℝ K = 1 ∧ Module.finrank ℝ L = 1) ∨
      (Module.finrank ℝ E = 4 ∧ Module.finrank ℝ K = 2 ∧ Module.finrank ℝ L = 2)) :
    ∃ V : E ≃ₗᵢ[ℝ] E, K.map V.toLinearMap = L ∧
      (K = L → V = LinearIsometryEquiv.refl ℝ E) ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal = realSchattenAngleBlockCost p.toReal K L := by
  by_cases hcommon : K = L
  · subst L
    refine ⟨LinearIsometryEquiv.refl ℝ E, by simp, fun _ => rfl, ?_⟩
    rw [realSchattenAngleBlockCost_self p.toReal hp1.le K]
    change UnitarilyInvariantSeminorm.schatten ℝ E E p (LinearMap.id - LinearMap.id) ^ p.toReal = 0
    simp [Real.zero_rpow (show p.toReal ≠ 0 by linarith)]
  · rcases hclass with hcommon' | ⟨hE, hK, hL⟩ | ⟨hE, hK, hL⟩
    · exact (hcommon hcommon').elim
    · obtain ⟨U, htrans, hcost, _⟩ :=
        exists_minimizing_real_two_schatten_unitary_principalAngles p hp K L hE hK hL
      let V := Unitary.linearIsometryEquiv U
      have hV : (V : E →L[ℝ] E) = (U : E →L[ℝ] E) :=
        Unitary.coe_linearIsometryEquiv_apply U
      have hlin : V.toLinearMap = (U : E →L[ℝ] E).toLinearMap := by
        rw [← hV]
        ext x
        rfl
      refine ⟨V, map_eq_of_unitary_conjugate K L U htrans,
        fun heq => (hcommon heq).elim, ?_⟩
      rw [hlin]
      rw [realSchattenAngleBlockCost, ite_eq_right (by omega : Module.finrank ℝ E ≠ 4),
        hK, Fin.sum_univ_one]
      exact hcost
    · obtain ⟨U, htrans, hcost, _⟩ :=
        exists_minimizing_real_four_schatten_unitary_principalAngles p hp hp1 hp2 K L hE hK hL
      let V := Unitary.linearIsometryEquiv U
      have hV : (V : E →L[ℝ] E) = (U : E →L[ℝ] E) :=
        Unitary.coe_linearIsometryEquiv_apply U
      have hlin : V.toLinearMap = (U : E →L[ℝ] E).toLinearMap := by
        rw [← hV]
        ext x
        rfl
      refine ⟨V, map_eq_of_unitary_conjugate K L U htrans,
        fun heq => (hcommon heq).elim, ?_⟩
      rw [hlin]
      simpa only [realSchattenAngleBlockCost, hE, ite_true, realPairSchattenCost] using hcost

/-- Every prescribed complete orthogonal family of actual real one-angle,
two-angle and common blocks has an ambient transporter attaining the sum
of its exact unrestricted block costs. Every common member is fixed
pointwise, including common members of arbitrary dimension. -/
theorem exists_real_transport_attaining_angle_blocks
    {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (W : ι → Submodule ℝ E)
    (horth : OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤)
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i)
    (hclass : ∀ i,
      (K.comap (W i).subtype = L.comap (W i).subtype) ∨
      (Module.finrank ℝ (W i) = 2 ∧ Module.finrank ℝ (K.comap (W i).subtype) = 1 ∧
        Module.finrank ℝ (L.comap (W i).subtype) = 1) ∨
      (Module.finrank ℝ (W i) = 4 ∧ Module.finrank ℝ (K.comap (W i).subtype) = 2 ∧
        Module.finrank ℝ (L.comap (W i).subtype) = 2)) :
    ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      (∀ i, K.comap (W i).subtype = L.comap (W i).subtype →
        ∀ x : W i, U (x : E) = (x : E)) ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        ∑ i, realSchattenAngleBlockCost p.toReal
          (K.comap (W i).subtype) (L.comap (W i).subtype) := by
  classical
  choose V hV hfix hcost using fun i => exists_real_small_block_transport p hp hp1 hp2
    (K.comap (W i).subtype) (L.comap (W i).subtype) (hclass i)
  obtain ⟨U, hmap, hU, hsum⟩ :=
    exists_transport_of_orthogonal_blocks K L W horth hspan hK hL V hV p hp
  refine ⟨U, hmap, ?_, ?_⟩
  · intro i hcommon x
    rw [hU, hfix i hcommon]
    rfl
  · rw [hsum]
    exact Finset.sum_congr rfl (fun i _ => hcost i)

/-- Geometric angle blocks need only exhaust the noncommon space. Their
entire common orthogonal remainder is fixed, in arbitrary ambient rank. -/
theorem exists_real_transport_attaining_incomplete_angle_blocks
    {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (W : ι → Submodule ℝ E)
    (horth : OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hK : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (hL : ∀ i, ∀ x ∈ W i, L.starProjection x ∈ W i)
    (hcommon : ∀ x ∈ (⨆ i, W i)ᗮ, K.starProjection x = L.starProjection x)
    (hclass : ∀ i,
      (Module.finrank ℝ (W i) = 2 ∧ Module.finrank ℝ (K.comap (W i).subtype) = 1 ∧
        Module.finrank ℝ (L.comap (W i).subtype) = 1) ∨
      (Module.finrank ℝ (W i) = 4 ∧ Module.finrank ℝ (K.comap (W i).subtype) = 2 ∧
        Module.finrank ℝ (L.comap (W i).subtype) = 2)) :
    ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      (∀ x ∈ (⨆ i, W i)ᗮ, U x = x) ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        ∑ i, realSchattenAngleBlockCost p.toReal
          (K.comap (W i).subtype) (L.comap (W i).subtype) := by
  classical
  let S := ⨆ i, W i
  let Z : Option ι → Submodule ℝ E := fun i => i.elim Sᗮ W
  have hKsum : ∀ x ∈ S, K.starProjection x ∈ S := by
    have hle : S ≤ S.comap K.starProjection.toLinearMap :=
      iSup_le (fun i x hx => (le_iSup W i) (hK i x hx))
    exact fun _ hx => hle hx
  have hLsum : ∀ x ∈ S, L.starProjection x ∈ S := by
    have hle : S ≤ S.comap L.starProjection.toLinearMap :=
      iSup_le (fun i x hx => (le_iSup W i) (hL i x hx))
    exact fun _ hx => hle hx
  have hKperp : ∀ x ∈ Sᗮ, K.starProjection x ∈ Sᗮ :=
    TauCeti.isInvariant_orthogonal_of_isSymmetric K.starProjection_isSymmetric hKsum
  have hLperp : ∀ x ∈ Sᗮ, L.starProjection x ∈ Sᗮ :=
    TauCeti.isInvariant_orthogonal_of_isSymmetric L.starProjection_isSymmetric hLsum
  have hrestrict : K.comap Sᗮ.subtype = L.comap Sᗮ.subtype := by
    ext x
    change (x : E) ∈ K ↔ (x : E) ∈ L
    rw [← K.starProjection_eq_self_iff, ← L.starProjection_eq_self_iff,
      hcommon x x.property]
  have horthZ : OrthogonalFamily ℝ (fun i => Z i) (fun i => (Z i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    · exact (hij rfl).elim
    · apply Submodule.isOrtho_iff_inner_eq.mpr
      intro x hx y hy
      exact Submodule.inner_left_of_mem_orthogonal ((le_iSup W j) hy) hx
    · apply Submodule.isOrtho_iff_inner_eq.mpr
      intro x hx y hy
      exact Submodule.inner_right_of_mem_orthogonal ((le_iSup W i) hx) hy
    · exact horth.pairwise (fun heq => hij (congrArg some heq))
  have hspanZ : (⨆ i, Z i) = ⊤ := by
    rw [iSup_option]
    exact sup_comm Sᗮ S |>.trans S.sup_orthogonal_of_hasOrthogonalProjection
  have hKZ : ∀ i, ∀ x ∈ Z i, K.starProjection x ∈ Z i := by
    rintro (_ | i)
    · exact hKperp
    · exact hK i
  have hLZ : ∀ i, ∀ x ∈ Z i, L.starProjection x ∈ Z i := by
    rintro (_ | i)
    · exact hLperp
    · exact hL i
  have hclassZ : ∀ i,
      K.comap (Z i).subtype = L.comap (Z i).subtype ∨
      (Module.finrank ℝ (Z i) = 2 ∧ Module.finrank ℝ (K.comap (Z i).subtype) = 1 ∧
        Module.finrank ℝ (L.comap (Z i).subtype) = 1) ∨
      (Module.finrank ℝ (Z i) = 4 ∧ Module.finrank ℝ (K.comap (Z i).subtype) = 2 ∧
        Module.finrank ℝ (L.comap (Z i).subtype) = 2) := by
    rintro (_ | i)
    · exact Or.inl hrestrict
    · exact Or.inr (hclass i)
  obtain ⟨U, hmap, hfix, hcost⟩ := exists_real_transport_attaining_angle_blocks
    p hp hp1 hp2 K L Z horthZ hspanZ hKZ hLZ hclassZ
  refine ⟨U, hmap, fun x hx => hfix none hrestrict ⟨x, hx⟩, ?_⟩
  rw [Fintype.sum_option] at hcost
  change _ = realSchattenAngleBlockCost p.toReal
    (K.comap Sᗮ.subtype) (L.comap Sᗮ.subtype) + _ at hcost
  rw [hrestrict, realSchattenAngleBlockCost_self _ hp1.le, zero_add] at hcost
  exact hcost

/-- Every labelled partition of the positive principal angles into ordered
singletons and pairs is realizable by actual reducing subspaces and an
ambient orthogonal transporter. The actual accepted angles of every block
are exactly its selected labels. Zero angles and all unused ambient
directions lie in the common orthogonal remainder and are fixed pointwise. -/
theorem exists_real_transport_attaining_principalAngle_groups
    {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L)
    (n : ι → ℕ) (hn : ∀ i, n i = 1 ∨ n i = 2)
    (e : ∀ i, Fin (n i) ↪ Fin (Module.finrank ℝ L))
    (hpos : ∀ i a, 0 < K.principalAngles L (e i a))
    (horder : ∀ i, Antitone (fun a => K.principalAngles L (e i a)))
    (hdisjoint : ∀ i j, i ≠ j → ∀ a b, e i a ≠ e j b)
    (hcover : ∀ j : Fin (Module.finrank ℝ L), 0 < K.principalAngles L j →
      ∃ i a, e i a = j) :
    ∃ W : ι → Submodule ℝ E,
      OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ) ∧
      (∀ i, Module.finrank ℝ (W i) = 2 * n i ∧
        Module.finrank ℝ (K.comap (W i).subtype) = n i ∧
        Module.finrank ℝ (L.comap (W i).subtype) = n i ∧
        ∀ a : Fin (n i), (K.comap (W i).subtype).principalAngles
          (L.comap (W i).subtype) a = K.principalAngles L (e i a)) ∧
      ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
        (∀ x ∈ (⨆ i, W i)ᗮ, U x = x) ∧
        UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - U.toLinearMap) ^ p.toReal =
          ∑ i, realSchattenAngleBlockCost p.toReal
            (K.comap (W i).subtype) (L.comap (W i).subtype) := by
  classical
  obtain ⟨u, w, v, hgram, _, _, hdecomp, hLu, hLv⟩ :=
    K.exists_cosineSine_principalAngle_frame L hKL
  let W i := Submodule.cosineSineFrameBlock u v (e i)
  have hdata (i) := K.cosineSineFrameBlock_data L u w v hgram hdecomp hLu hLv
    (e i) (hpos i) (horder i)
  have horth := K.orthogonalFamily_cosineSineFrameBlock L u v hgram n e hdisjoint
  have hspan := K.iSup_cosineSineFrameBlock_eq_active L u v n e hpos hcover
  have hcommon : ∀ x ∈ (⨆ i, W i)ᗮ, K.starProjection x = L.starProjection x := by
    intro x hx
    rw [hspan] at hx
    exact K.starProjection_eq_on_cosineSine_active_orthogonal L u w v hdecomp x hx
  refine ⟨W, horth, fun i => ⟨(hdata i).1, (hdata i).2.2.2.1,
    (hdata i).2.2.2.2.1, (hdata i).2.2.2.2.2⟩, ?_⟩
  apply exists_real_transport_attaining_incomplete_angle_blocks p hp hp1 hp2 K L W
    horth (fun i => (hdata i).2.1) (fun i => (hdata i).2.2.1) hcommon
  intro i
  rcases hn i with hi | hi
  · exact Or.inl ⟨by simpa only [hi] using (hdata i).1,
      (hdata i).2.2.2.1.trans hi, (hdata i).2.2.2.2.1.trans hi⟩
  · exact Or.inr ⟨by simpa only [hi] using (hdata i).1,
      (hdata i).2.2.2.1.trans hi, (hdata i).2.2.2.2.1.trans hi⟩

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
