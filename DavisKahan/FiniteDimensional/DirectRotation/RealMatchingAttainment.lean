/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.RealAngleBlockAttainment
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealMatchingWeights

/-!
# Realizing labelled real transport matchings

A matching is partitioned into ordered singleton and two-cycle orbits.
The actual principal-angle frame realizes those orbits as reducing planes
and four-dimensional blocks, with identity on the common complement.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open scoped ENNReal

private theorem ordered_partner_eq {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (hs : Function.Involutive s) {i j : ι}
    (hi : i ≤ s i) (hj : j ≤ s j) (h : i = s j) : i = j := by
  have hsi : s i = j := by rw [h, hs j]
  exact le_antisymm (hsi ▸ hi) (h ▸ hj)

private def matchingGroupSize {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (i : {i // i ≤ s i}) : ℕ :=
  if s i.val = i.val then 1 else 2

private def matchingGroupVertex {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (i : {i // i ≤ s i}) (a : Fin (matchingGroupSize s i)) : ι :=
  if a.val = 0 then i.val else s i.val

private theorem matchingGroupVertex_injective {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (i : {i // i ≤ s i}) :
    Function.Injective (matchingGroupVertex s i) := by
  intro a b hab
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  dsimp [matchingGroupSize] at ha hb
  by_cases hfix : s i.val = i.val
  · simp only [hfix, ite_true] at ha hb
    omega
  · simp only [hfix, ite_false] at ha hb
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
    · omega
    · exact (hfix (by simpa only [matchingGroupVertex, ha0, hb0,
        ite_true, ite_false] using hab.symm)).elim
    · exact (hfix (by simpa only [matchingGroupVertex, ha0, hb0,
        ite_true, ite_false] using hab)).elim
    · omega

private theorem matchingGroupVertex_disjoint {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (hs : Function.Involutive s)
    (i j : {i // i ≤ s i}) (hij : i ≠ j)
    (a : Fin (matchingGroupSize s i)) (b : Fin (matchingGroupSize s j)) :
    matchingGroupVertex s i a ≠ matchingGroupVertex s j b := by
  intro hab
  apply hij
  apply Subtype.ext
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · simpa only [matchingGroupVertex, ha, hb, ite_true] using hab
  · exact ordered_partner_eq s hs i.property j.property
      (by simpa only [matchingGroupVertex, ha, hb, ite_true, ite_false] using hab)
  · exact (ordered_partner_eq s hs j.property i.property
      (by simpa only [matchingGroupVertex, ha, hb, ite_true, ite_false] using hab.symm)).symm
  · apply s.injective
    simpa only [matchingGroupVertex, ha, hb, ite_false] using hab

private theorem matchingGroupVertex_cover {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (hs : Function.Involutive s) (j : ι) :
    ∃ i : {i // i ≤ s i}, ∃ a : Fin (matchingGroupSize s i), matchingGroupVertex s i a = j := by
  by_cases hj : j ≤ s j
  · let i : {i // i ≤ s i} := ⟨j, hj⟩
    have hn : 0 < matchingGroupSize s i := by unfold matchingGroupSize; split <;> omega
    exact ⟨i, ⟨0, hn⟩, rfl⟩
  · have hfix : s (s j) ≠ s j := by
      rw [hs j]
      exact ne_of_gt (lt_of_not_ge hj)
    let i : {i // i ≤ s i} := ⟨s j, by rw [hs j]; exact (le_of_not_ge hj)⟩
    have hn : 1 < matchingGroupSize s i := by
      change 1 < if s (s j) = s j then 1 else 2
      rw [ite_eq_right hfix]
      norm_num
    refine ⟨i, ⟨1, hn⟩, ?_⟩
    exact hs j

private theorem matchingGroupVertex_monotone {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (i : {i // i ≤ s i}) :
    Monotone (matchingGroupVertex s i) := by
  intro a b hab
  by_cases ha : a.val = 0
  · by_cases hb : b.val = 0
    · simp only [matchingGroupVertex, ha, hb, ite_true, le_refl]
    · simpa only [matchingGroupVertex, ha, hb, ite_true, ite_false] using i.property
  · have hb : b.val ≠ 0 := by have := hab; omega
    simp only [matchingGroupVertex, ha, hb, ite_false, le_refl]

private theorem matchingGroupVertex_rev {ι : Type*} [LinearOrder ι]
    (s : Equiv.Perm ι) (hs : Function.Involutive s)
    (i : {i // i ≤ s i}) (a : Fin (matchingGroupSize s i)) :
    matchingGroupVertex s i (Fin.rev a) = s (matchingGroupVertex s i a) := by
  have ha := a.isLt
  dsimp [matchingGroupSize] at ha
  by_cases hfix : s i.val = i.val
  · simp only [hfix, ite_true] at ha
    have ha0 : a.val = 0 := by omega
    simp [matchingGroupVertex, Fin.rev, matchingGroupSize, hfix, ha0]
  · simp only [hfix, ite_false] at ha
    by_cases ha0 : a.val = 0
    · simp [matchingGroupVertex, Fin.rev, matchingGroupSize, hfix, ha0]
    · have ha1 : a.val = 1 := by omega
      simp [matchingGroupVertex, Fin.rev, matchingGroupSize, hfix, ha1, hs i.val]

set_option maxHeartbeats 800000 in
/-- Ordered singleton/two-cycle coordinates preserve the complete matching
cost, with every original vertex and repeated angle retained. -/
private theorem matchingCost_eq_ordered_groups {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    realSchattenMatchingCost p theta s =
      ∑ i : {i // i ≤ s i}, realSchattenMatchingCost p
        (theta ∘ matchingGroupVertex s i) Fin.revPerm := by
  classical
  let f : (Σ i : {i // i ≤ s i}, Fin (matchingGroupSize s i)) → ι :=
    fun x => matchingGroupVertex s x.1 x.2
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hi : a.1 = b.1 := by
        by_contra hne
        exact matchingGroupVertex_disjoint s hs a.1 b.1 hne a.2 b.2 hab
      cases a with | mk i a =>
        cases b with | mk j b =>
          dsimp at hi
          subst j
          exact congrArg (Sigma.mk i) (matchingGroupVertex_injective s i hab)
    · intro j
      obtain ⟨i, a, ha⟩ := matchingGroupVertex_cover s hs j
      exact ⟨⟨i, a⟩, ha⟩
  let e := Equiv.ofBijective f hbij
  have hconj : (e.trans s).trans e.symm =
      Equiv.sigmaCongrRight (fun i : {i // i ≤ s i} => (Fin.revPerm :
        Equiv.Perm (Fin (matchingGroupSize s i)))) := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    apply e.injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sigmaCongrRight_apply]
    change s (matchingGroupVertex s i a) = matchingGroupVertex s i (Fin.rev a)
    exact (matchingGroupVertex_rev s hs i a).symm
  have hindex := realSchattenMatchingCost_reindex p theta s e
  rw [hconj] at hindex
  have hsum := realSchattenMatchingCost_sigma p
    (fun (i : {i // i ≤ s i}) (a : Fin (matchingGroupSize s i)) =>
      theta (matchingGroupVertex s i a)) (fun _ => Fin.revPerm)
  exact hindex.symm.trans hsum

private theorem matchingCost_rev_finCongr {m n : ℕ}
    (p : ℝ) (theta : Fin n → ℝ) (h : m = n) :
    realSchattenMatchingCost p (theta ∘ finCongr h) Fin.revPerm =
      realSchattenMatchingCost p theta Fin.revPerm := by
  let e := finCongr h
  have hconj : (e.trans Fin.revPerm).trans e.symm = Fin.revPerm := by
    apply Equiv.ext
    intro a
    apply e.injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Fin.revPerm_apply]
    exact (Fin.cast_rev a h).symm
  have he := realSchattenMatchingCost_reindex p theta Fin.revPerm e
  rw [hconj] at he
  exact he

private theorem matchingCost_ordered_group {ι : Type*} [LinearOrder ι]
    (p : ℝ) (theta : ι → ℝ) (htheta : Antitone theta)
    (s : Equiv.Perm ι) (i : {i // i ≤ s i}) :
    realSchattenMatchingCost p (theta ∘ matchingGroupVertex s i) Fin.revPerm =
      if s i.val = i.val then realSingleSchattenCost p (theta i.val)
      else realPairSchattenCost p (theta i.val) (theta (s i.val)) := by
  classical
  have horder := htheta i.property
  by_cases hfix : s i.val = i.val
  · have hn : matchingGroupSize s i = 1 := by simp [matchingGroupSize, hfix]
    rw [← matchingCost_rev_finCongr p _ hn.symm]
    simp only [realSchattenMatchingCost, Fin.sum_univ_one, Fin.revPerm_apply,
      Fin.rev_zero, Fin.isValue, Function.comp_apply, matchingGroupVertex,
      finCongr_apply_coe, Fin.val_zero, ite_true, hfix,
      show (Fin.last 0 : Fin 1) = 0 by decide]
  · have hn : matchingGroupSize s i = 2 := by simp [matchingGroupSize, hfix]
    rw [← matchingCost_rev_finCongr p _ hn.symm]
    rw [realSchattenMatchingCost_rev_two p _]
    · simp only [Function.comp_apply, matchingGroupVertex, finCongr_apply_coe,
        Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false, hfix]
    · simpa only [Function.comp_apply, matchingGroupVertex, finCongr_apply_coe,
        Fin.val_zero, Fin.val_one, ite_true, one_ne_zero, ite_false] using horder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every matching of the original labelled positive principal angles is
attained by an actual ambient orthogonal transporter, with its full
one-angle/two-class pair cost. All ambient dimensions, repeated angles,
right angles and the empty positive-angle set are included. -/
theorem exists_real_transport_attaining_matching
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L)
    (s : Equiv.Perm {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j})
    (hs : Function.Involutive s) :
    ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        realSchattenMatchingCost p.toReal
          (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
            K.principalAngles L j.val) s := by
  classical
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let R := {i : J // i ≤ s i}
  let n : R → ℕ := matchingGroupSize s
  let e (i : R) : Fin (n i) ↪ Fin (Module.finrank ℝ L) :=
    ⟨fun a => Fin.cast hKL (matchingGroupVertex s i a).val, by
      intro a b hab
      apply matchingGroupVertex_injective s i
      apply Subtype.ext
      exact Fin.cast_injective hKL hab⟩
  have hn (i : R) : n i = 1 ∨ n i = 2 := by
    unfold n matchingGroupSize
    split <;> simp
  have hpos (i : R) (a : Fin (n i)) : 0 < K.principalAngles L (e i a) :=
    (matchingGroupVertex s i a).property
  have horder (i : R) : Antitone (fun a => K.principalAngles L (e i a)) := by
    intro a b hab
    apply K.principalAngles_antitone L
    exact matchingGroupVertex_monotone s i hab
  have hdisjoint (i j : R) (hij : i ≠ j) (a : Fin (n i)) (b : Fin (n j)) :
      e i a ≠ e j b := by
    intro hab
    apply matchingGroupVertex_disjoint s hs i j hij a b
    apply Subtype.ext
    exact Fin.cast_injective hKL hab
  have hcover (j : Fin (Module.finrank ℝ L)) (hj : 0 < K.principalAngles L j) :
      ∃ i a, e i a = j := by
    let k : J := ⟨Fin.cast hKL.symm j, hj⟩
    obtain ⟨i, a, ha⟩ := matchingGroupVertex_cover s hs k
    refine ⟨i, a, ?_⟩
    change Fin.cast hKL (matchingGroupVertex s i a).val = j
    rw [ha]
    simp only [k, Fin.cast_cast, Fin.cast_eq_self]
  obtain ⟨W, _, hdata, U, hmap, _, hcost⟩ :=
    exists_real_transport_attaining_principalAngle_groups p hp hp1 hp2 K L hKL
      n hn e hpos horder hdisjoint hcover
  refine ⟨U, hmap, hcost.trans ?_⟩
  rw [matchingCost_eq_ordered_groups p.toReal _ s hs]
  apply Finset.sum_congr rfl
  intro i _
  let K₀ := K.comap (W i).subtype
  let L₀ := L.comap (W i).subtype
  have hdim : Module.finrank ℝ (W i) = 2 * n i := (hdata i).1
  have hrank : Module.finrank ℝ K₀ = n i := (hdata i).2.1
  have hlabel (a : Fin (n i)) : K₀.principalAngles L₀ a =
      K.principalAngles L (matchingGroupVertex s i a).val := (hdata i).2.2.2 a
  change realSchattenAngleBlockCost p.toReal K₀ L₀ = _
  rw [matchingCost_ordered_group p.toReal
    (fun j : J => K.principalAngles L j.val)
    (fun _ _ h => K.principalAngles_antitone L h) s i]
  by_cases hfix : s i.val = i.val
  · have hni : n i = 1 := by simp only [n, matchingGroupSize, hfix, ite_true]
    have h0 : K₀.principalAngles L₀ 0 = K.principalAngles L i.val.val := by
      simpa only [matchingGroupVertex, Fin.val_cast, Fin.val_zero, ite_true] using
        hlabel (Fin.cast hni.symm (0 : Fin 1))
    rw [realSchattenAngleBlockCost, hdim, hni,
      ite_eq_right (by decide : ¬(2*1 : ℕ) = 4), hrank, hni, Fin.sum_univ_one]
    change realSingleSchattenCost p.toReal (K₀.principalAngles L₀ 0) = _
    rw [h0, ite_eq_left hfix]
  · have hni : n i = 2 := by simp only [n, matchingGroupSize, hfix, ite_false]
    have h0 : K₀.principalAngles L₀ 0 = K.principalAngles L i.val.val := by
      simpa only [matchingGroupVertex, Fin.val_cast, Fin.val_zero, ite_true] using
        hlabel (Fin.cast hni.symm (0 : Fin 2))
    have h1 : K₀.principalAngles L₀ 1 = K.principalAngles L (s i.val).val := by
      simpa only [matchingGroupVertex, Fin.val_cast, Fin.val_one, one_ne_zero,
        ite_false] using hlabel (Fin.cast hni.symm (1 : Fin 2))
    rw [realSchattenAngleBlockCost, hdim, hni,
      ite_eq_left (by decide : (2*2 : ℕ) = 4), h0, h1, ite_eq_right hfix]

/-- The unrestricted finite-dimensional real Schatten transport minimum is
exactly the positive-edge matching minimum on the original positive
principal angles. It is attained by an ambient orthogonal transporter
and bounds every ambient orthogonal competitor. There are no acuteness,
multiplicity, determinant, parity or prescribed-plane restrictions. -/
theorem exists_minimizing_real_schatten_transport_matching
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        realPositiveSchattenMatchingMinimum p.toReal
          (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
            K.principalAngles L j.val) ∧
      ∀ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let theta : J → ℝ := fun j => K.principalAngles L j.val
  obtain ⟨s, hs, hcost⟩ := exists_attains_realSchattenMatchingMinimum p.toReal theta
  obtain ⟨U, hmap, hU⟩ := exists_real_transport_attaining_matching p hp hp1 hp2 K L hKL s hs
  have hvalue : UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - U.toLinearMap) ^ p.toReal =
      realPositiveSchattenMatchingMinimum p.toReal theta := by
    rw [hU, hcost]
    exact realSchattenMatchingMinimum_eq_positive p.toReal hp1 hp2 theta
      (fun j => ⟨K.principalAngles_nonneg L j.val, K.principalAngles_le_pi_div_two L j.val⟩)
  refine ⟨U, hmap, hvalue, fun T hT => ?_⟩
  rw [hvalue]
  exact realPositiveSchattenMatchingMinimum_le_of_map_eq p hp hp1 hp2 K L T hT

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
