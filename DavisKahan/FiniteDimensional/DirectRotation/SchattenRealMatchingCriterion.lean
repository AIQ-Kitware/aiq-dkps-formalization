/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.RealMatchingAttainment

/-!
# When independent real principal planes suffice

The exact finite matching minimum equals the sum of its unmatched costs
if and only if no single edge improves its two unmatched endpoints.
Together with unrestricted matching attainment, this gives an all-rank
certificate for the global optimality of independent real plane choices.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

variable {ι : Type*} [Fintype ι]

/-- Replacing precisely two unmatched vertices by one edge changes the
cost by the edge weight minus those two unmatched costs. -/
theorem realSchattenMatchingCost_swap_add [DecidableEq ι] (p : ℝ) (theta : ι → ℝ)
    (i j : ι) (hij : i ≠ j) :
    realSchattenMatchingCost p theta (Equiv.swap i j) +
        realSingleSchattenCost p (theta i) + realSingleSchattenCost p (theta j) =
      (∑ k, realSingleSchattenCost p (theta k)) +
        realSchattenPairWeight p (theta i) (theta j) := by
  classical
  let a k := realSingleSchattenCost p (theta k)
  let w := realSchattenPairWeight p (theta i) (theta j)
  let b k := if Equiv.swap i j k = k then a k
    else realSchattenPairWeight p (theta k) (theta (Equiv.swap i j k)) / 2
  have hpoint (k : ι) :
      b k + (if k = i then a i else 0) + (if k = j then a j else 0) =
        a k + (if k = i then w/2 else 0) + (if k = j then w/2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [b, w, hij, Ne.symm hij, Equiv.swap_apply_def]
      ring
    · by_cases hkj : k = j
      · subst k
        simp [b, w, hij, Ne.symm hij, Equiv.swap_apply_def, realSchattenPairWeight_comm]
        ring
      · simp [b, hki, hkj, Equiv.swap_apply_def]
  have hsum := congrArg (fun f : ι → ℝ => ∑ k, f k) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  have hb : realSchattenMatchingCost p theta (Equiv.swap i j) = ∑ k, b k := by
    unfold realSchattenMatchingCost
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [b, a]
    split_ifs <;> rfl
  rw [hb]
  change (∑ k, b k) + a i + a j = (∑ k, a k) + w
  linarith

/-- Independent one-angle optima are globally optimal exactly when no
pair of distinct labelled angles has a cheaper coupled four-dimensional
optimum. This finite certificate does not require the angles to differ. -/
theorem realSchattenMatchingMinimum_eq_singletons_iff (p : ℝ) (theta : ι → ℝ) :
    realSchattenMatchingMinimum p theta = (∑ i, realSingleSchattenCost p (theta i)) ↔
      ∀ i j, i ≠ j → realSingleSchattenCost p (theta i) +
        realSingleSchattenCost p (theta j) ≤ realSchattenPairWeight p (theta i) (theta j) := by
  classical
  let a i := realSingleSchattenCost p (theta i)
  constructor
  · intro hmin i j hij
    have hbound := realSchattenMatchingMinimum_le p theta (Equiv.swap i j)
      (fun k => Equiv.swap_apply_self i j k)
    rw [hmin] at hbound
    have hswap := realSchattenMatchingCost_swap_add p theta i j hij
    linarith
  · intro hpair
    apply le_antisymm
    · simpa only [realSchattenMatchingCost_refl] using
        realSchattenMatchingMinimum_le p theta (Equiv.refl ι) (fun _ => rfl)
    · obtain ⟨s, _, hcost⟩ := exists_attains_realSchattenMatchingMinimum p theta
      rw [← hcost]
      have hvertex (i : ι) : (a i + a (s i))/2 ≤
          if s i = i then a i else realSchattenPairWeight p (theta i) (theta (s i))/2 := by
        by_cases hfix : s i = i
        · simp [hfix]
        · rw [ite_eq_right hfix]
          exact div_le_div_of_nonneg_right (hpair i (s i) (Ne.symm hfix)) (by norm_num)
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hvertex i)
      rw [← Finset.sum_div, Finset.sum_add_distrib, Equiv.sum_comp s] at hsum
      change (∑ i, a i) ≤ _
      change _ ≤ realSchattenMatchingCost p theta s at hsum
      linarith

/-- The same no-profitable-pair criterion in the positive-edge weights of
the real matching formula. Both determinant classes are still covered:
an edge can instead be split into its two independent real plane minima. -/
theorem realPositiveSchattenMatchingMinimum_eq_singletons_iff
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi/2)) :
    realPositiveSchattenMatchingMinimum p theta = (∑ i, realSingleSchattenCost p (theta i)) ↔
      ∀ i j, i ≠ j → realSingleSchattenCost p (theta i) +
        realSingleSchattenCost p (theta j) ≤ realPositiveSchattenPairWeight p (theta i) (theta j) := by
  rw [← realSchattenMatchingMinimum_eq_positive p hp1 hp2 theta htheta,
    realSchattenMatchingMinimum_eq_singletons_iff]
  constructor
  · intro h i j hij
    have hi := h i j hij
    rw [realSchattenPairWeight_eq_min_positive_singletons p _ _ hp1 hp2
      (htheta i) (htheta j)] at hi
    exact (le_min_iff.mp hi).1
  · intro h i j hij
    rw [realSchattenPairWeight_eq_min_positive_singletons p _ _ hp1 hp2
      (htheta i) (htheta j)]
    exact le_min (h i j hij) le_rfl

open scoped ENNReal

/-- An unrestricted real global optimum has the independent-plane value
if and only if every pair of distinct positive angle labels passes the
explicit four-dimensional comparison. Thus checking all labelled pairs
certifies optimality against every ambient orthogonal competitor. -/
theorem exists_minimizing_real_schatten_transport_singletons_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
    (∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        (∑ j : J, realSingleSchattenCost p.toReal (K.principalAngles L j.val)) ∧
      ∀ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal) ↔
      ∀ i j : J, i ≠ j →
        realSingleSchattenCost p.toReal (K.principalAngles L i.val) +
          realSingleSchattenCost p.toReal (K.principalAngles L j.val) ≤
        realPositiveSchattenPairWeight p.toReal
          (K.principalAngles L i.val) (K.principalAngles L j.val) := by
  classical
  dsimp only
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let theta : J → ℝ := fun j => K.principalAngles L j.val
  have htheta (j : J) : theta j ∈ Set.Icc 0 (Real.pi/2) :=
    ⟨K.principalAngles_nonneg L j.val, K.principalAngles_le_pi_div_two L j.val⟩
  have hcriterion := realPositiveSchattenMatchingMinimum_eq_singletons_iff
    p.toReal hp1 hp2 theta htheta
  obtain ⟨V, hV, hcostV, hminV⟩ :=
    exists_minimizing_real_schatten_transport_matching p hp hp1 hp2 K L hKL
  constructor
  · rintro ⟨U, hU, hcostU, hminU⟩
    apply hcriterion.mp
    have hbound := realSchattenMatchingMinimum_le p.toReal theta (Equiv.refl J) (fun _ => rfl)
    rw [realSchattenMatchingMinimum_eq_positive p.toReal hp1 hp2 theta htheta,
      realSchattenMatchingCost_refl] at hbound
    have hreverse := hminU V hV
    rw [hcostU, hcostV] at hreverse
    exact le_antisymm hbound hreverse
  · intro hpair
    refine ⟨V, hV, ?_, hminV⟩
    exact hcostV.trans (hcriterion.mpr hpair)

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
