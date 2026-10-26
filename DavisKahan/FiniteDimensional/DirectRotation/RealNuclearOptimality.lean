/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearExchange

/-!
# The all-rank real nuclear canonical region

The unrestricted real nuclear matching minimum equals the canonical
principal-angle sum exactly when at most one angle is positive and all
angles are at most `pi/3`. Zero, repeated and right angles are allowed.
The ambient consequence uses the proved unrestricted matching theorem;
no principal-plane restriction is imposed on competitors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The nuclear matching minimum is bounded by every labelled matching. -/
theorem realNuclearMatchingMinimum_le (theta : ι → ℝ) (s : Equiv.Perm ι)
    (hs : Function.Involutive s) :
    realNuclearMatchingMinimum theta ≤ realNuclearMatchingCost theta s :=
  Finset.inf'_le _ ((mem_realSchattenMatchings s).mpr hs)

/-- A labelled involution attains the nuclear matching minimum. -/
theorem exists_attains_realNuclearMatchingMinimum (theta : ι → ℝ) :
    ∃ s : Equiv.Perm ι, Function.Involutive s ∧
      realNuclearMatchingCost theta s = realNuclearMatchingMinimum theta := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
    (realSchattenMatchings_nonempty ι) (realNuclearMatchingCost theta)
  exact ⟨s, (mem_realSchattenMatchings s).mp hs, heq.symm⟩

/-- The exact canonical-versus-reflection cutoff for a nuclear singleton. -/
theorem nuclear_canonical_cost_le_two_iff (theta : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) :
    4 * Real.sin (theta/2) ≤ 2 ↔ theta ≤ Real.pi/3 := by
  have hsin : Real.sin (theta/2) ≤ (1 : ℝ)/2 ↔ theta/2 ≤ Real.pi/6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [htheta.1, Real.pi_pos], by linarith [htheta.2, Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  constructor
  · intro h
    have := hsin.mp (by linarith)
    linarith
  · intro h
    have := hsin.mpr (by linarith)
    linarith

/-- The exact cost change on inserting one nuclear edge. -/
theorem realNuclearMatchingCost_swap_add [DecidableEq ι] (theta : ι → ℝ)
    (i j : ι) (hij : i ≠ j) :
    realNuclearMatchingCost theta (Equiv.swap i j) +
        min (4 * Real.sin (theta i/2)) 2 + min (4 * Real.sin (theta j/2)) 2 =
      (∑ k, min (4 * Real.sin (theta k/2)) 2) +
        realNuclearPairWeight (theta i) (theta j) := by
  classical
  let a k := min (4 * Real.sin (theta k/2)) 2
  let w := realNuclearPairWeight (theta i) (theta j)
  let b k := if Equiv.swap i j k = k then a k
    else realNuclearPairWeight (theta k) (theta (Equiv.swap i j k))/2
  have hpoint (k : ι) :
      b k + (if k = i then a i else 0) + (if k = j then a j else 0) =
        a k + (if k = i then w/2 else 0) + (if k = j then w/2 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [b, w, hij, Ne.symm hij, Equiv.swap_apply_def]
      ring
    · by_cases hkj : k = j
      · subst k
        simp [b, w, hij, Ne.symm hij, Equiv.swap_apply_def, realNuclearPairWeight_comm]
        ring
      · simp [b, hki, hkj, Equiv.swap_apply_def]
  have hsum := congrArg (fun f : ι → ℝ => ∑ k, f k) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  have hb : realNuclearMatchingCost theta (Equiv.swap i j) = ∑ k, b k := by
    unfold realNuclearMatchingCost
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [b, a]
    split_ifs <;> rfl
  rw [hb]
  change (∑ k, b k) + a i + a j = (∑ k, a k) + w
  linarith

/-- In every rank, the unrestricted nuclear value equals the canonical
sum exactly when at most one angle is positive and it is at most `pi/3`.
Repeated values retain their distinct labels. -/
theorem realNuclearMatchingMinimum_eq_canonical_iff
    (theta : ι → ℝ) (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realNuclearMatchingMinimum theta = (∑ i, 4 * Real.sin (theta i/2)) ↔
      (∀ i, theta i ≤ Real.pi/3) ∧
        (∀ i j, 0 < theta i → 0 < theta j → i = j) := by
  classical
  let a i := 4 * Real.sin (theta i/2)
  have hrefl : realNuclearMatchingCost theta (Equiv.refl ι) = ∑ i, min (a i) 2 := by
    simp [realNuclearMatchingCost, a]
  constructor
  · intro heq
    have hsum : (∑ i, min (a i) 2) = ∑ i, a i := by
      apply le_antisymm (Finset.sum_le_sum fun i _ => min_le_left (a i) 2)
      have hbound := realNuclearMatchingMinimum_le theta (Equiv.refl ι) (fun _ => rfl)
      rw [heq, hrefl] at hbound
      exact hbound
    have hsingle (i : ι) : min (a i) 2 = a i :=
      (Finset.sum_eq_sum_iff_of_le (fun k (_ : k ∈ Finset.univ) =>
        min_le_left (a k) 2)).mp hsum i (Finset.mem_univ i)
    refine ⟨fun i => (nuclear_canonical_cost_le_two_iff _ (htheta i)).mp ?_, ?_⟩
    · exact (hsingle i).symm.trans_le (min_le_right _ _)
    · intro i j hi hj
      by_contra hij
      have hbound := realNuclearMatchingMinimum_le theta (Equiv.swap i j)
        (fun k => Equiv.swap_apply_self i j k)
      have hswap := realNuclearMatchingCost_swap_add theta i j hij
      change realNuclearMatchingCost theta (Equiv.swap i j) +
        min (a i) 2 + min (a j) 2 = (∑ k, min (a k) 2) + _ at hswap
      rw [heq] at hbound
      rw [hsingle i, hsingle j, hsum] at hswap
      have hstrict := realNuclearPairWeight_lt_canonical_sum _ _ hi hj
        (htheta i).2 (htheta j).2
      change _ < a i + a j at hstrict
      linarith
  · rintro ⟨hcut, hone⟩
    have hsingle (i : ι) : min (a i) 2 = a i :=
      min_eq_left ((nuclear_canonical_cost_le_two_iff _ (htheta i)).mpr (hcut i))
    obtain ⟨s, _, hcost⟩ := exists_attains_realNuclearMatchingMinimum theta
    rw [← hcost]
    have hpoint (i : ι) :
        (if s i = i then min (a i) 2
          else realNuclearPairWeight (theta i) (theta (s i))/2) =
        (a i + a (s i))/2 := by
      by_cases hfix : s i = i
      · simp [hfix, hsingle]
      · rw [ite_eq_right hfix]
        have hz : theta i = 0 ∨ theta (s i) = 0 := by
          by_contra h
          push Not at h
          exact hfix (hone (s i) i
            (lt_of_le_of_ne (htheta (s i)).1 (Ne.symm h.2))
            (lt_of_le_of_ne (htheta i).1 (Ne.symm h.1)))
        rcases hz with hz | hz <;> simp [realNuclearPairWeight, a, hz]
    change (∑ i, if s i = i then min (a i) 2
      else realNuclearPairWeight (theta i) (theta (s i))/2) = _
    simp_rw [hpoint]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Equiv.sum_comp s]
    change ((∑ i, a i) + ∑ i, a i)/2 = ∑ i, a i
    ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact unrestricted ambient nuclear minimum equals the canonical
spectral sum precisely in the one-positive-angle region below `pi/3`.
Every ambient orthogonal competitor is included in the minimum. -/
theorem realTransportPowerMinimum_one_eq_canonical_iff
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    realTransportPowerMinimum 1 K L =
        (∑ i : Fin (Module.finrank ℝ K), 4 * Real.sin (K.principalAngles L i/2)) ↔
      (∀ i : Fin (Module.finrank ℝ K), K.principalAngles L i ≤ Real.pi/3) ∧
        (∀ i j : Fin (Module.finrank ℝ K),
          0 < K.principalAngles L i → 0 < K.principalAngles L j → i = j) := by
  classical
  let theta : Fin (Module.finrank ℝ K) → ℝ := fun i => K.principalAngles L i
  let J := {i : Fin (Module.finrank ℝ K) // 0 < theta i}
  have htheta (i) : theta i ∈ Icc 0 (Real.pi/2) :=
    ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
  have hzero (i : {i // ¬0 < theta i}) : 4 * Real.sin (theta i.val/2) = 0 := by
    have hi : theta i.val = 0 := le_antisymm (le_of_not_gt i.property) (htheta i.val).1
    simp [hi]
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < theta i)
    (fun i => 4 * Real.sin (theta i/2))
  rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero] at hsum
  rw [realTransportPowerMinimum_one_eq_nuclearMatching K L hKL, ← hsum,
    realNuclearMatchingMinimum_eq_canonical_iff (fun i : J => theta i.val)
      (fun i => htheta i.val)]
  constructor
  · rintro ⟨hcut, hone⟩
    constructor
    · intro i
      by_cases hi : 0 < theta i
      · exact hcut ⟨i, hi⟩
      · have hz : theta i = 0 := le_antisymm (le_of_not_gt hi) (htheta i).1
        change theta i ≤ _
        rw [hz]
        positivity
    · intro i j hi hj
      exact congrArg Subtype.val (hone (⟨i, hi⟩ : J) ⟨j, hj⟩ hi hj)
  · rintro ⟨hcut, hone⟩
    exact ⟨fun i => hcut i.val,
      fun i j _ _ => Subtype.ext (hone i.val j.val i.property j.property)⟩

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
