/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealMatchingZeros

/-!
# The two-class real pair weight and the positive pair weight

The full unrestricted four-dimensional minimum equals the lesser of its
positive-determinant minimum and two independent one-angle minima. This
is the scalar identity needed to convert full pair weights into the
positive-edge weights used in the matching draft. The proof keeps zero,
equal and right angles and does not assume which determinant class wins.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open scoped ENNReal

/-- Positive-determinant two-angle cost, on decreasing principal angles. -/
@[expose]
def realPositivePairSchattenCost (p theta psi : ℝ) : ℝ :=
  let h := (theta + psi)/2
  let d := (theta - psi)/2
  2 * phasePower p h (max d (optimalPhase p h))

private theorem positive_pair_cost_bounds
    (p theta psi : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hpsi : 0 ≤ psi) (horder : psi ≤ theta) (htheta : theta ≤ Real.pi/2) :
    realPositivePairSchattenCost p theta psi ≤
        2 * phaseChord theta^p + 2 * phaseChord psi^p ∧
      realPositivePairSchattenCost p theta psi ≤ 2 * (2 : ℝ)^p := by
  let h := (theta+psi)/2
  let d := (theta-psi)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hdh : d ≤ h := by dsimp [d, h]; linarith
  have hh : h ≤ Real.pi/2 := by dsimp [h]; linarith
  have hh0 : 0 ≤ h := hd.trans hdh
  have ht : h+d = theta := by dsimp [h, d]; ring
  have hu : h-d = psi := by dsimp [h, d]; ring
  have hopt := (optimalPhase_spec p h hp1.le hh0).1.2
  have hclip : max d (optimalPhase p h) ∈ Set.Icc d h :=
    ⟨le_max_left _ _, max_le hdh hopt⟩
  have hmin := (phasePower_isMinOn_truncated_iff p h d _ hp1 hp2 hd hdh hh hclip).mpr rfl
  have hleft := hmin ⟨le_rfl, hdh⟩
  have hright := hmin ⟨hdh, le_rfl⟩
  change phasePower p h (max d (optimalPhase p h)) ≤ phasePower p h d at hleft
  change phasePower p h (max d (optimalPhase p h)) ≤ phasePower p h h at hright
  have hendpoint : phasePower p h h = phaseChord (2*h)^p := by
    simp [phasePower, show h+h = 2*h by ring, phaseChord,
      Real.zero_rpow (show p ≠ 0 by linarith)]
  have hchord0 : 0 ≤ phaseChord (2*h) := by
    dsimp [phaseChord]
    exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos]))
  have hchord2 : phaseChord (2*h) ≤ 2 := by
    dsimp [phaseChord]
    linarith [Real.sin_le_one (2*h/2)]
  have hpower := Real.rpow_le_rpow hchord0 hchord2 (show 0 ≤ p by linarith)
  change 2 * phasePower p h (max d (optimalPhase p h)) ≤ _ ∧
    2 * phasePower p h (max d (optimalPhase p h)) ≤ _
  have hcanonical : phasePower p h d = phaseChord theta^p + phaseChord psi^p := by
    rw [phasePower, ht, hu]
  rw [hcanonical] at hleft
  rw [hendpoint] at hright
  constructor <;> linarith

/-- The full two-class cost is exactly the minimum of the positive pair
cost and the cost of leaving both vertices unmatched. This includes all
zero, equal and right principal angles. -/
theorem realPairSchattenCost_eq_min_positive_singletons
    (p theta psi : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hpsi : 0 ≤ psi) (horder : psi ≤ theta) (htheta : theta ≤ Real.pi/2) :
    realPairSchattenCost p theta psi =
      min (realPositivePairSchattenCost p theta psi)
        (realSingleSchattenCost p theta + realSingleSchattenCost p psi) := by
  obtain ⟨hcanonical, hreflection⟩ := positive_pair_cost_bounds p theta psi hp1 hp2 hpsi horder htheta
  have hchord0 : 0 ≤ phaseChord psi := by
    exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos]))
  have hchordOrder : phaseChord psi ≤ phaseChord theta := by
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ psi/2 by linarith [Real.pi_pos])
      (show theta/2 ≤ Real.pi/2 by linarith [Real.pi_pos]) (by linarith : psi/2 ≤ theta/2)
    dsimp [phaseChord]
    linarith
  have hpowerOrder := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hchord0 hchordOrder (show 0 ≤ p by linarith)) (by norm_num : (0 : ℝ) ≤ 2)
  change min (realPositivePairSchattenCost p theta psi)
    ((2 : ℝ)^p + 2 * phaseChord psi^p) = _
  by_cases hlarge : 2 * phaseChord theta^p ≤ (2 : ℝ)^p
  · have hsmall : 2 * phaseChord psi^p ≤ (2 : ℝ)^p := hpowerOrder.trans hlarge
    simp only [realSingleSchattenCost, min_eq_left hlarge, min_eq_left hsmall]
    rw [min_eq_left hcanonical, min_eq_left (by linarith :
      realPositivePairSchattenCost p theta psi ≤ (2 : ℝ)^p + 2 * phaseChord psi^p)]
  · by_cases hsmall : 2 * phaseChord psi^p ≤ (2 : ℝ)^p
    · simp only [realSingleSchattenCost, min_eq_right (le_of_not_ge hlarge), min_eq_left hsmall]
    · simp only [realSingleSchattenCost, min_eq_right (le_of_not_ge hlarge),
        min_eq_right (le_of_not_ge hsmall)]
      rw [min_eq_left (by linarith : realPositivePairSchattenCost p theta psi ≤
          (2 : ℝ)^p + (2 : ℝ)^p),
        min_eq_left (by linarith : realPositivePairSchattenCost p theta psi ≤
          (2 : ℝ)^p + 2 * phaseChord psi^p)]

/-- Symmetric positive-determinant edge weight used by the matching draft. -/
@[expose] def realPositiveSchattenPairWeight (p theta psi : ℝ) : ℝ :=
  realPositivePairSchattenCost p (max theta psi) (min theta psi)

theorem realPositiveSchattenPairWeight_comm (p theta psi : ℝ) :
    realPositiveSchattenPairWeight p theta psi = realPositiveSchattenPairWeight p psi theta := by
  simp only [realPositiveSchattenPairWeight, max_comm, min_comm]

/-- Symmetric form of the exact pair-versus-two-singletons identity. -/
theorem realSchattenPairWeight_eq_min_positive_singletons
    (p theta psi : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (htheta : theta ∈ Set.Icc 0 (Real.pi/2)) (hpsi : psi ∈ Set.Icc 0 (Real.pi/2)) :
    realSchattenPairWeight p theta psi = min (realPositiveSchattenPairWeight p theta psi)
      (realSingleSchattenCost p theta + realSingleSchattenCost p psi) := by
  rcases le_total psi theta with horder | horder
  · simp only [realSchattenPairWeight, realPositiveSchattenPairWeight,
      max_eq_left horder, min_eq_right horder]
    exact realPairSchattenCost_eq_min_positive_singletons p theta psi hp1 hp2 hpsi.1 horder htheta.2
  · simp only [realSchattenPairWeight, realPositiveSchattenPairWeight,
      max_eq_right horder, min_eq_left horder]
    rw [add_comm]
    exact realPairSchattenCost_eq_min_positive_singletons p psi theta hp1 hp2 htheta.1 horder hpsi.2

/-- The draft's matching cost, with positive-class edges and unrestricted
one-angle weights at unmatched vertices. -/
@[expose]
def realPositiveSchattenMatchingCost {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) : ℝ := by
  classical
  exact ∑ i, if s i = i then realSingleSchattenCost p (theta i)
    else realPositiveSchattenPairWeight p (theta i) (theta (s i)) / 2

/-- Every full-weight matching has an equal-cost positive-weight matching.
Keep an edge when its positive pair cost is no larger than two singletons;
otherwise remove it. The decision is the same at both endpoints, so the
new partner map is involutive. This accounts for both determinant classes
without losing a negative-class improvement. -/
theorem exists_positive_weight_matching_cost_eq {ι : Type*} [Fintype ι]
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi/2))
    (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    ∃ t : Equiv.Perm ι, Function.Involutive t ∧
      realPositiveSchattenMatchingCost p theta t = realSchattenMatchingCost p theta s := by
  classical
  let keep (i : ι) := realPositiveSchattenPairWeight p (theta i) (theta (s i)) ≤
    realSingleSchattenCost p (theta i) + realSingleSchattenCost p (theta (s i))
  have hkeep (i : ι) : keep (s i) ↔ keep i := by
    dsimp only [keep]
    rw [hs i, realPositiveSchattenPairWeight_comm p (theta (s i)) (theta i),
      add_comm (realSingleSchattenCost p (theta (s i))) (realSingleSchattenCost p (theta i))]
  let partner (i : ι) := if keep i then s i else i
  have hpartner : Function.Involutive partner := by
    intro i
    by_cases hi : keep i
    · have hsi := (hkeep i).mpr hi
      simp only [partner, ite_eq_left hi, ite_eq_left hsi, hs i]
    · simp only [partner, ite_eq_right hi]
  let t := Function.Involutive.toPerm partner hpartner
  have ht : Function.Involutive t := hpartner
  refine ⟨t, ht, ?_⟩
  let a (i : ι) := if s i = i then realSingleSchattenCost p (theta i)
    else realSchattenPairWeight p (theta i) (theta (s i)) / 2
  let b (i : ι) := if t i = i then realSingleSchattenCost p (theta i)
    else realPositiveSchattenPairWeight p (theta i) (theta (t i)) / 2
  have hpair (i : ι) : b i + b (s i) = a i + a (s i) := by
    by_cases hfixed : s i = i
    · simp [a, b, t, partner, hfixed]
    · have hreverse : i ≠ s i := Ne.symm hfixed
      have hid := realSchattenPairWeight_eq_min_positive_singletons
        p (theta i) (theta (s i)) hp1 hp2 (htheta i) (htheta (s i))
      by_cases hi : keep i
      · have hsi := (hkeep i).mpr hi
        simp [a, b, t, partner, hi, hsi, hs i, hfixed, hreverse,
          realSchattenPairWeight_comm p (theta (s i)) (theta i),
          realPositiveSchattenPairWeight_comm p (theta (s i)) (theta i), hid,
          min_eq_left hi]
      · have hsi : ¬keep (s i) := (hkeep i).not.mpr hi
        simp [a, b, t, partner, hi, hsi, hs i, hfixed, hreverse,
          realSchattenPairWeight_comm p (theta (s i)) (theta i), hid,
          min_eq_right (le_of_not_ge hi)]
  have hdouble : (∑ i, b i) + (∑ i, b i) = (∑ i, a i) + (∑ i, a i) := by
    calc
      _ = ∑ i, (b i + b (s i)) := by rw [Finset.sum_add_distrib, Equiv.sum_comp s]
      _ = ∑ i, (a i + a (s i)) := Finset.sum_congr rfl (fun i _ => hpair i)
      _ = _ := by rw [Finset.sum_add_distrib, Equiv.sum_comp s]
  change (∑ i, b i) = ∑ i, a i
  linarith

/-- Minimum of the draft's positive-edge matching costs. The identity
matching makes the finite feasible set nonempty even at rank zero. -/
@[expose]
def realPositiveSchattenMatchingMinimum {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) : ℝ :=
  (realSchattenMatchings ι).inf' (realSchattenMatchings_nonempty ι)
    (realPositiveSchattenMatchingCost p theta)

theorem realPositiveSchattenMatchingMinimum_le {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    realPositiveSchattenMatchingMinimum p theta ≤ realPositiveSchattenMatchingCost p theta s := by
  exact Finset.inf'_le _ ((mem_realSchattenMatchings s).mpr hs)

/-- Combinatorial attainment of the positive-edge matching minimum. -/
theorem exists_attains_realPositiveSchattenMatchingMinimum {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) :
    ∃ s : Equiv.Perm ι, Function.Involutive s ∧
      realPositiveSchattenMatchingCost p theta s = realPositiveSchattenMatchingMinimum p theta := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
    (realSchattenMatchings_nonempty ι) (realPositiveSchattenMatchingCost p theta)
  exact ⟨s, (mem_realSchattenMatchings s).mp hs, heq.symm⟩

/-- The full-weight and positive-edge combinatorial minima coincide.
The two determinant classes are accounted for by deleting an edge when
its positive-class cost exceeds the two unmatched one-angle costs. -/
theorem realSchattenMatchingMinimum_eq_positive {ι : Type*} [Fintype ι]
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi/2)) :
    realSchattenMatchingMinimum p theta = realPositiveSchattenMatchingMinimum p theta := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs, hcost⟩ := exists_attains_realPositiveSchattenMatchingMinimum p theta
    rw [← hcost]
    apply (realSchattenMatchingMinimum_le p theta s hs).trans
    unfold realSchattenMatchingCost realPositiveSchattenMatchingCost
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact div_le_div_of_nonneg_right
        (by rw [realSchattenPairWeight_eq_min_positive_singletons p _ _ hp1 hp2
          (htheta i) (htheta (s i))]; exact min_le_left _ _) (by norm_num)
  · obtain ⟨s, hs, hcost⟩ := exists_attains_realSchattenMatchingMinimum p theta
    obtain ⟨t, ht, heq⟩ := exists_positive_weight_matching_cost_eq p hp1 hp2 theta htheta s hs
    rw [← hcost, ← heq]
    exact realPositiveSchattenMatchingMinimum_le p theta t ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Every unrestricted real global minimum has exactly the cost of an
actual matching on its original strictly positive angle labels, using the
draft's positive-edge weights. Both zero-angle partners and negative-class
pair choices are eliminated without altering the certificate's cost. -/
theorem exists_positive_matching_cost_eq_of_isMinOn_real_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * K.starProjection * star W =
        (T : E →L[ℝ] E) * K.starProjection * star (T : E →L[ℝ] E)} (T : E →L[ℝ] E)) :
    let theta : Fin (Module.finrank ℝ K) → ℝ :=
      fun j => K.principalAngles (K.map T.toLinearMap) j
    ∃ s : Equiv.Perm {j // 0 < theta j}, Function.Involutive s ∧
      realPositiveSchattenMatchingCost p.toReal (fun j : {j // 0 < theta j} => theta j.val) s =
        UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  dsimp only
  let theta : Fin (Module.finrank ℝ K) → ℝ :=
    fun j => K.principalAngles (K.map T.toLinearMap) j
  obtain ⟨s, hs, hfull⟩ := exists_matching_cost_eq_of_isMinOn_real_transport p hp hp1 hp2 K T hmin
  obtain ⟨t, ht, hzero⟩ := exists_positive_matching_cost_eq p.toReal hp1.le theta
    (fun j => K.principalAngles_nonneg (K.map T.toLinearMap) j) s hs
  obtain ⟨u, hu, hpositive⟩ := exists_positive_weight_matching_cost_eq p.toReal hp1 hp2
    (fun j : {j // 0 < theta j} => theta j.val)
    (fun j => ⟨K.principalAngles_nonneg (K.map T.toLinearMap) j.val,
      K.principalAngles_le_pi_div_two (K.map T.toLinearMap) j.val⟩) t ht
  exact ⟨u, hu, hpositive.trans (hzero.trans hfull)⟩

/-- The draft's positive-edge matching minimum is a global lower bound
on every unrestricted real orthogonal transport. Vertices are exactly the
original strictly positive principal-angle indices, with all repetitions
and right angles retained. This proves the lower-bound direction of the
matching formula; ambient attainment is the remaining converse. -/
theorem realPositiveSchattenMatchingMinimum_le_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    let theta : Fin (Module.finrank ℝ K) → ℝ :=
      fun j => K.principalAngles (K.map T.toLinearMap) j
    realPositiveSchattenMatchingMinimum p.toReal
        (fun j : {j // 0 < theta j} => theta j.val) ≤
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  let theta : Fin (Module.finrank ℝ K) → ℝ :=
    fun j => K.principalAngles (K.map T.toLinearMap) j
  let J := {j // 0 < theta j}
  have htheta (j : J) : theta j.val ∈ Set.Icc 0 (Real.pi/2) :=
    ⟨K.principalAngles_nonneg (K.map T.toLinearMap) j.val,
      K.principalAngles_le_pi_div_two (K.map T.toLinearMap) j.val⟩
  calc
    realPositiveSchattenMatchingMinimum p.toReal (fun j : J => theta j.val) =
        realSchattenMatchingMinimum p.toReal (fun j : J => theta j.val) :=
      (realSchattenMatchingMinimum_eq_positive p.toReal hp1 hp2 _ htheta).symm
    _ ≤ _ := realSchattenPositiveMatchingMinimum_le_transport p hp hp1 hp2 K T

/-- Source-target form of the unrestricted real matching lower bound. -/
theorem realPositiveSchattenMatchingMinimum_le_of_map_eq
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) (hmap : K.map T.toLinearMap = L) :
    let theta : Fin (Module.finrank ℝ K) → ℝ := fun j => K.principalAngles L j
    realPositiveSchattenMatchingMinimum p.toReal
        (fun j : {j // 0 < theta j} => theta j.val) ≤
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  subst L
  exact realPositiveSchattenMatchingMinimum_le_transport p hp hp1 hp2 K T

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
