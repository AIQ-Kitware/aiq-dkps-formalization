/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearSortedScalar

/-!
# The largest-angle recurrence for real nuclear matching

Every matching on an ordered physical angle list can be changed at no greater
cost so that the largest angle is either a reflection singleton or paired
with the second-largest angle. Canonical singletons and all ties are retained.
The argument is a finite exchange, not a claim about every optimizer.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set
open WeightedInvolution

/-- The nuclear matching energy on a function; involutivity is imposed in
its theorems. This is the existing labelled matching cost on actual permutations. -/
@[expose] def nuclearMatchingEnergy {ι : Type*} [Fintype ι]
    (theta : ι → ℝ) (s : ι → ι) : ℝ :=
  cost (fun i => min (nuclearCanonicalCost (theta i)) 2)
    (fun i j => realNuclearPairWeight (theta i) (theta j)) s

/-- A cost-nonincreasing leading-orbit normalization. It covers arbitrary
optional singletons, repeated angles and the full closed angle interval. -/
theorem exists_nuclear_head_normalization {n : ℕ} (theta : Fin (n + 2) → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi / 2)) (horder : Antitone theta)
    (s : Fin (n + 2) → Fin (n + 2)) (hs : Function.Involutive s) :
    ∃ t : Fin (n + 2) → Fin (n + 2), Function.Involutive t ∧
      nuclearMatchingEnergy theta t ≤ nuclearMatchingEnergy theta s ∧
      ((t 0 = 0 ∧ min (nuclearCanonicalCost (theta 0)) 2 = 2) ∨ t 0 = 1) := by
  let c (i : Fin (n + 2)) := min (nuclearCanonicalCost (theta i)) 2
  let w (i j : Fin (n + 2)) := realNuclearPairWeight (theta i) (theta j)
  have hw (i j) : w i j = w j i := realNuclearPairWeight_comm _ _
  have hle (i : Fin (n + 2)) : theta i ≤ theta 0 := horder (Fin.zero_le i)
  have h01 : theta 1 ≤ theta 0 := hle 1
  have hc_le (i) : c i ≤ nuclearCanonicalCost (theta i) := min_le_left _ _
  have hc0 : nuclearCanonicalCost (theta 1) ≤ nuclearCanonicalCost (theta 0) :=
    nuclearCanonicalCost_mono _ _ (htheta 1).1 h01 (htheta 0).2
  change ∃ t, Function.Involutive t ∧ cost c w t ≤ cost c w s ∧
    ((t 0 = 0 ∧ c 0 = 2) ∨ t 0 = 1)
  by_cases hs0 : s 0 = 0
  · by_cases hC0 : 2 ≤ nuclearCanonicalCost (theta 0)
    · exact ⟨s, hs, le_rfl, Or.inl ⟨hs0, min_eq_right hC0⟩⟩
    have hc0eq : c 0 = nuclearCanonicalCost (theta 0) := min_eq_left (not_le.mp hC0).le
    by_cases hs1 : s 1 = 1
    · let t := joinFixed s 0 1
      have ht0 : t 0 = 1 := by simp only [t, joinFixed_apply, hs0, Equiv.swap_apply_left]
      have hc1eq : c 1 = nuclearCanonicalCost (theta 1) :=
        min_eq_left (hc0.trans (not_le.mp hC0).le)
      have hid := cost_joinFixed c w hw s hs 0 1 Fin.zero_ne_one hs0 hs1
      have hbound := realNuclearPairWeight_le_canonical_sum _ _ (htheta 0) (htheta 1)
      refine ⟨t, joinFixed_involutive s hs 0 1 hs0 hs1, ?_, Or.inr ht0⟩
      change cost c w (joinFixed s 0 1) ≤ cost c w s
      change w 0 1 ≤ _ at hbound
      rw [← hc0eq, ← hc1eq] at hbound
      linarith
    · let b := s 1
      have hb1 : b ≠ 1 := hs1
      have hb0 : b ≠ 0 := by
        intro h
        exact (Ne.symm Fin.zero_ne_one) (hs.injective (h.trans hs0.symm))
      have hsb : s b = 1 := hs 1
      have h1b : (1 : Fin (n + 2)) ≤ b := Fin.one_le_of_ne_zero hb0
      let t := (Equiv.swap 0 b).conj s
      have ht0 : t 0 = 1 := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap, Equiv.swap_apply_left, hsb,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm Fin.zero_ne_one) hb1.symm]
      have hid := cost_conjugate_fixed_edge c w hw s hs 0 1 b
        hs0 rfl hb1.symm
      have hbound := (nuclear_pair_canonical_exchange (theta 0) (theta 1) (theta b)
        (htheta b).1 (horder h1b) h01 (htheta 0).2).trans (min_le_right _ _)
      refine ⟨t, (Equiv.involutive_conj_iff _ s).mpr hs, ?_, Or.inr ht0⟩
      change cost c w ((Equiv.swap 0 b).conj s) ≤ cost c w s
      change w 0 1 + _ ≤ nuclearCanonicalCost (theta 0) + w 1 b at hbound
      rw [← hc0eq] at hbound
      linarith [hc_le b]
  by_cases hs01 : s 0 = 1
  · exact ⟨s, hs, le_rfl, Or.inr hs01⟩
  let a := s 0
  have ha0 : a ≠ 0 := hs0
  have ha1 : a ≠ 1 := hs01
  have hsa : s a = 0 := hs 0
  have h1a : (1 : Fin (n + 2)) ≤ a := Fin.one_le_of_ne_zero ha0
  by_cases hs1 : s 1 = 1
  · by_cases hC1 : 2 ≤ nuclearCanonicalCost (theta 1)
    · let t := (Equiv.swap 1 0).conj s
      have ht0 : t 0 = 0 := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap, Equiv.swap_apply_right, hs1,
          Equiv.swap_apply_left]
      have hc0eq : c 0 = 2 := min_eq_right (hC1.trans hc0)
      have hc1eq : c 1 = 2 := min_eq_right hC1
      have hid := cost_conjugate_fixed_edge c w hw s hs 1 a 0
        hs1 hsa ha0
      have hbound := realNuclearPairWeight_mono_left (theta 1) (theta 0) (theta a)
        (htheta 1).1 h01 (htheta 0).2 (htheta a)
      rw [hw a 0, hc0eq, hc1eq] at hid
      refine ⟨t, (Equiv.involutive_conj_iff _ s).mpr hs, ?_, Or.inl ⟨ht0, hc0eq⟩⟩
      change cost c w ((Equiv.swap 1 0).conj s) ≤ cost c w s
      change w 1 a ≤ w 0 a at hbound
      linarith
    · let t := (Equiv.swap 1 a).conj s
      have ht0 : t 0 = 1 := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one ha0.symm,
          show s 0 = a from rfl, Equiv.swap_apply_right]
      have hc1eq : c 1 = nuclearCanonicalCost (theta 1) := min_eq_left (not_le.mp hC1).le
      have hid := cost_conjugate_fixed_edge c w hw s hs 1 0 a
        hs1 rfl ha0.symm
      have hbound := (nuclear_pair_canonical_exchange (theta 0) (theta 1) (theta a)
        (htheta a).1 (horder h1a) h01 (htheta 0).2).trans (min_le_left _ _)
      rw [hw 1 0, hc1eq] at hid
      refine ⟨t, (Equiv.involutive_conj_iff _ s).mpr hs, ?_, Or.inr ht0⟩
      change cost c w ((Equiv.swap 1 a).conj s) ≤ cost c w s
      change w 0 1 + _ ≤ w 0 a + nuclearCanonicalCost (theta 1) at hbound
      linarith [hc_le a]
  · let b := s 1
    have hb1 : b ≠ 1 := hs1
    have hb0 : b ≠ 0 := by
      intro h
      have h' := congrArg s h
      rw [hs 1] at h'
      exact ha1 h'.symm
    have h1b : (1 : Fin (n + 2)) ≤ b := Fin.one_le_of_ne_zero hb0
    let t := (Equiv.swap 1 a).conj s
    have ht0 : t 0 = 1 := by
      simp only [t, Equiv.conj_apply, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one ha0.symm,
        show s 0 = a from rfl, Equiv.swap_apply_right]
    have hid := cost_conjugate_two_edges c w hw s hs 0 1 a b
      Fin.zero_ne_one ha0.symm hb0.symm hb1.symm rfl rfl
    have hbound := nuclear_pair_largest_exchange (theta 0) (theta 1) (theta a) (theta b)
      (htheta a).1 (htheta b).1 (horder h1a) (horder h1b) h01 (htheta 0).2
    refine ⟨t, (Equiv.involutive_conj_iff _ s).mpr hs, ?_, Or.inr ht0⟩
    change cost c w ((Equiv.swap 1 a).conj s) ≤ cost c w s
    change w 0 1 + w a b ≤ w 0 a + w 1 b at hbound
    linarith

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
