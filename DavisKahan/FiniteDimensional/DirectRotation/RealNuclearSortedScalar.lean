/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearExchange
public import ForTauCeti.Combinatorics.Matching.WeightedInvolution

/-!
# Ordered nuclear matching exchanges

Nuclear edges are increasing in each angle. The four-angle exchange also
compares a canonical singleton with a pair by inserting a scalar zero.
These inequalities support the largest-angle recurrence, without assuming
that a matching is perfect or that the angles are distinct.

The trigonometric and finite-exchange ingredients are classical. The exact
ambient transport application is tracked in the maintained provenance note.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set

/-- Canonical singleton cost as an edge with a scalar zero. -/
@[expose]
def nuclearCanonicalCost (t : ℝ) : ℝ := realNuclearPairWeight t 0

/-- Nuclear pair cost is increasing in its first physical angle. -/
theorem realNuclearPairWeight_mono_left (a b t : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2)
    (ht : t ∈ Icc 0 (Real.pi / 2)) :
    realNuclearPairWeight a t ≤ realNuclearPairWeight b t := by
  unfold realNuclearPairWeight
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · linarith [ht.1, Real.pi_pos]
  · linarith [ht.2]
  · linarith

/-- Canonical singleton costs are increasing throughout the physical interval. -/
theorem nuclearCanonicalCost_mono (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    nuclearCanonicalCost a ≤ nuclearCanonicalCost b :=
  realNuclearPairWeight_mono_left a b 0 ha hab hb ⟨le_rfl, by positivity⟩

/-- Pairing the two largest angles and canonically fixing the third is
no dearer than either other pair/canonical-singleton choice. -/
theorem nuclear_pair_canonical_exchange (a b t : ℝ)
    (ht : 0 ≤ t) (htb : t ≤ b) (hba : b ≤ a) (ha : a ≤ Real.pi / 2) :
    realNuclearPairWeight a b + nuclearCanonicalCost t ≤
      min (realNuclearPairWeight a t + nuclearCanonicalCost b)
        (nuclearCanonicalCost a + realNuclearPairWeight b t) := by
  have h := realNuclearPairWeight_adjacent_exchange a b t 0 le_rfl ht htb hba ha
  exact h

/-- The two largest angles can be joined while their unordered partners
are rejoined, without increasing the total edge cost. -/
theorem nuclear_pair_largest_exchange (a b u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hub : u ≤ b) (hvb : v ≤ b)
    (hba : b ≤ a) (ha : a ≤ Real.pi / 2) :
    realNuclearPairWeight a b + realNuclearPairWeight u v ≤
      realNuclearPairWeight a u + realNuclearPairWeight b v := by
  rcases le_total v u with hvu | huv
  · exact (realNuclearPairWeight_adjacent_exchange a b u v hv hvu hub hba ha).trans
      (min_le_left _ _)
  · rw [realNuclearPairWeight_comm u v]
    exact (realNuclearPairWeight_adjacent_exchange a b v u hu huv hvb hba ha).trans
      (min_le_right _ _)

/-- Every physical pair costs at most two reflection singletons. -/
theorem realNuclearPairWeight_le_four (a b : ℝ) : realNuclearPairWeight a b ≤ 4 := by
  unfold realNuclearPairWeight
  linarith [Real.sin_le_one ((a + b) / 2)]

/-- Every pair costs at most its two canonical singleton costs. -/
theorem realNuclearPairWeight_le_canonical_sum (a b : ℝ)
    (ha : a ∈ Icc 0 (Real.pi / 2)) (hb : b ∈ Icc 0 (Real.pi / 2)) :
    realNuclearPairWeight a b ≤ nuclearCanonicalCost a + nuclearCanonicalCost b := by
  have h := realNuclearPairWeight_submodular 0 a 0 b le_rfl ha.1 ha.2 le_rfl hb.1 hb.2
  simpa only [realNuclearPairWeight, nuclearCanonicalCost, add_zero, zero_add,
    zero_div, Real.sin_zero, mul_zero] using h

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
