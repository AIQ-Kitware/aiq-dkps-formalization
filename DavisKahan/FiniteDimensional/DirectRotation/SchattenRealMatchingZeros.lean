/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealMatching

/-!
# Removing zero-angle partners from real transport matchings

An edge incident to a zero angle has exactly the cost of leaving its
other endpoint unmatched. Remove all such edges simultaneously. The
resulting permutation is still involutive, fixes every zero vertex, and
has exactly the same cost. The sum proof pairs each vertex's contribution
with its original partner; this retains every repeated zero label.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open scoped ENNReal

theorem realSchattenPairWeight_zero_right (p theta : ℝ) (hp : 1 ≤ p) (htheta : 0 ≤ theta) :
    realSchattenPairWeight p theta 0 = realSingleSchattenCost p theta := by
  simp only [realSchattenPairWeight, max_eq_left htheta, min_eq_right htheta]
  exact realPairSchattenCost_zero p theta hp htheta

theorem realSchattenPairWeight_zero_left (p theta : ℝ) (hp : 1 ≤ p) (htheta : 0 ≤ theta) :
    realSchattenPairWeight p 0 theta = realSingleSchattenCost p theta := by
  rw [realSchattenPairWeight_comm]
  exact realSchattenPairWeight_zero_right p theta hp htheta

variable {ι : Type*}

/-- Fix both endpoints of every edge incident to a zero angle. -/
def realZeroStrippedPartner (theta : ι → ℝ) (s : Equiv.Perm ι) (i : ι) : ι := by
  classical
  exact if theta i = 0 ∨ theta (s i) = 0 then i else s i

/-- Simultaneously removing the zero-angle edges leaves an involution. -/
theorem realZeroStrippedPartner_involutive (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) : Function.Involutive (realZeroStrippedPartner theta s) := by
  classical
  intro i
  by_cases hi : theta i = 0
  · simp [realZeroStrippedPartner, hi]
  · by_cases hsi : theta (s i) = 0
    · simp [realZeroStrippedPartner, hi, hsi]
    · simp [realZeroStrippedPartner, hi, hsi, hs i]

/-- The zero-stripped matching as an actual permutation. -/
def realZeroStrippedMatching (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) : Equiv.Perm ι :=
  Function.Involutive.toPerm _ (realZeroStrippedPartner_involutive theta s hs)

@[simp] theorem realZeroStrippedMatching_apply (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) (i : ι) :
    realZeroStrippedMatching theta s hs i = realZeroStrippedPartner theta s i := rfl

theorem realZeroStrippedMatching_involutive (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) : Function.Involutive (realZeroStrippedMatching theta s hs) :=
  realZeroStrippedPartner_involutive theta s hs

/-- Every zero vertex becomes unmatched. -/
theorem realZeroStrippedMatching_fixes_zero (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) (i : ι) (hi : theta i = 0) :
    realZeroStrippedMatching theta s hs i = i := by
  simp [realZeroStrippedPartner, hi]

/-- Stripping every zero-angle edge preserves the complete matching cost.
There is no restriction on the number or multiplicity of zero angles. -/
theorem realSchattenMatchingCost_zeroStripped [Fintype ι]
    (p : ℝ) (hp : 1 ≤ p) (theta : ι → ℝ) (htheta : ∀ i, 0 ≤ theta i)
    (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    realSchattenMatchingCost p theta (realZeroStrippedMatching theta s hs) =
      realSchattenMatchingCost p theta s := by
  classical
  let a (t : Equiv.Perm ι) (i : ι) :=
    if t i = i then realSingleSchattenCost p (theta i)
    else realSchattenPairWeight p (theta i) (theta (t i)) / 2
  let S := realZeroStrippedMatching theta s hs
  have hpair (i : ι) : a S i + a S (s i) = a s i + a s (s i) := by
    by_cases hfixed : s i = i
    · simp [a, S, realZeroStrippedPartner, hfixed]
    · have hreverse : i ≠ s i := Ne.symm hfixed
      by_cases hi : theta i = 0
      · simp [a, S, realZeroStrippedPartner, hi, hs i, hfixed, hreverse,
          realSchattenPairWeight_zero_right p _ hp (htheta _),
          realSchattenPairWeight_zero_left p _ hp (htheta _),
          realSingleSchattenCost_zero p (by linarith)]
      · by_cases hsi : theta (s i) = 0
        · simp [a, S, realZeroStrippedPartner, hi, hsi, hs i, hfixed, hreverse,
            realSchattenPairWeight_zero_right p _ hp (htheta _),
            realSchattenPairWeight_zero_left p _ hp (htheta _),
            realSingleSchattenCost_zero p (by linarith)]
        · simp [a, S, realZeroStrippedPartner, hi, hsi, hs i, hfixed, hreverse]
  have hdouble : (∑ i, a S i) + (∑ i, a S i) = (∑ i, a s i) + (∑ i, a s i) := by
    calc
      _ = ∑ i, (a S i + a S (s i)) := by rw [Finset.sum_add_distrib, Equiv.sum_comp s]
      _ = ∑ i, (a s i + a s (s i)) := Finset.sum_congr rfl (fun i _ => hpair i)
      _ = _ := by rw [Finset.sum_add_distrib, Equiv.sum_comp s]
  change (∑ i, a S i) = ∑ i, a s i
  linarith

/-- Every matching on nonnegative angles has an equal-cost matching on
the labelled strictly positive angles. The zero labels are removed only
after stripping their incident edges, so positive partners become
unmatched and keep exactly their original full edge cost. -/
theorem exists_positive_matching_cost_eq [Fintype ι]
    (p : ℝ) (hp : 1 ≤ p) (theta : ι → ℝ) (htheta : ∀ i, 0 ≤ theta i)
    (s : Equiv.Perm ι) (hs : Function.Involutive s) :
    ∃ t : Equiv.Perm {i // 0 < theta i}, Function.Involutive t ∧
      realSchattenMatchingCost p (fun i : {i // 0 < theta i} => theta i.val) t =
        realSchattenMatchingCost p theta s := by
  classical
  let S := realZeroStrippedMatching theta s hs
  have hS : Function.Involutive S := realZeroStrippedMatching_involutive theta s hs
  have hfix (i : ι) (hi : theta i = 0) : S i = i :=
    realZeroStrippedMatching_fixes_zero theta s hs i hi
  have hpos (i : ι) : 0 < theta (S i) ↔ 0 < theta i := by
    constructor
    · intro hpositive
      by_contra hnot
      have hz : theta i = 0 := le_antisymm (le_of_not_gt hnot) (htheta i)
      rw [hfix i hz, hz] at hpositive
      exact (lt_irrefl _) hpositive
    · intro hpositive
      by_contra hnot
      have hz : theta (S i) = 0 := le_antisymm (le_of_not_gt hnot) (htheta (S i))
      have heq : S i = i := S.injective (hfix (S i) hz)
      rw [heq] at hz
      exact (ne_of_gt hpositive) hz
  let t := S.subtypePerm (p := fun i => 0 < theta i) hpos
  have ht : Function.Involutive t := by
    intro i
    apply Subtype.ext
    exact hS i.val
  refine ⟨t, ht, ?_⟩
  rw [← realSchattenMatchingCost_zeroStripped p hp theta htheta s hs]
  let a (i : ι) := if S i = i then realSingleSchattenCost p (theta i)
    else realSchattenPairWeight p (theta i) (theta (S i)) / 2
  have hzero (i : {i // ¬0 < theta i}) : a i.val = 0 := by
    have hz : theta i.val = 0 := le_antisymm (le_of_not_gt i.property) (htheta i.val)
    simp [a, hfix i.val hz, hz, realSingleSchattenCost_zero p (by linarith)]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < theta i) a
  rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero] at hsplit
  change realSchattenMatchingCost p (fun i : {i // 0 < theta i} => theta i.val) t = ∑ i, a i
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro i _
  simp only [t, Equiv.Perm.subtypePerm_apply, Subtype.ext_iff, a]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Every ambient real transporter dominates an actual matching on its
labelled strictly positive principal angles. Zero and common ambient
directions have been removed with no loss of cost in the certificate.
The pair weight includes both determinant classes. -/
theorem exists_positive_matching_cost_le_real_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    let theta : Fin (Module.finrank ℝ K) → ℝ :=
      fun j => K.principalAngles (K.map T.toLinearMap) j
    ∃ s : Equiv.Perm {j // 0 < theta j}, Function.Involutive s ∧
      realSchattenMatchingCost p.toReal (fun j : {j // 0 < theta j} => theta j.val) s ≤
        UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  dsimp only
  obtain ⟨s, hs, hbound⟩ := exists_matching_cost_le_real_transport p hp hp1 hp2 K T
  obtain ⟨t, ht, hcost⟩ := exists_positive_matching_cost_eq p.toReal hp1.le
    (fun j : Fin (Module.finrank ℝ K) => K.principalAngles (K.map T.toLinearMap) j)
    (fun j => K.principalAngles_nonneg (K.map T.toLinearMap) j) s hs
  exact ⟨t, ht, hcost.trans_le hbound⟩

/-- Global matching lower bound on strictly positive original principal
angles, with repetitions as separate vertices and no assumption on the
competitor beyond real orthogonality. -/
theorem realSchattenPositiveMatchingMinimum_le_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (T : E ≃ₗᵢ[ℝ] E) :
    let theta : Fin (Module.finrank ℝ K) → ℝ :=
      fun j => K.principalAngles (K.map T.toLinearMap) j
    realSchattenMatchingMinimum p.toReal (fun j : {j // 0 < theta j} => theta j.val) ≤
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  obtain ⟨s, hs, hbound⟩ := exists_positive_matching_cost_le_real_transport p hp hp1 hp2 K T
  exact (realSchattenMatchingMinimum_le _ _ s hs).trans hbound

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
