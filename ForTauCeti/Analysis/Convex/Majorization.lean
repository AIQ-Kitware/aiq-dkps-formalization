/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5
-/
module

public import TauCeti.Analysis.Convex.Majorization

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Additional finite majorization results

Prefix sums, `IsWeaklyMajorizedBy`, `IsSymmetricConvex` and transfer descent are consumed
from `TauCeti.Analysis.Convex.Majorization`. The native symmetric-convex predicate uses all
permutations; its equivalence with the former transposition formulation was compiled before
removing the local predicate and descent proofs.

This module retains the stronger constructive one-step transfer lemma
`FiniteVector.exists_isTTransform_of_not_forall_le`: a single convex combination with a
transposition preserves prefix domination and nonnegativity while strictly reducing the number
of coordinates disagreeing with the target. Native transfer descent does not expose that progress
certificate. Its `FiniteVector.IsTTransform` is specifically one swap average, whereas native
`TauCeti.IsTTransform` permits a Robin Hood transfer followed by an arbitrary permutation.

Finite symmetric gauges use native `Seminorm` and `IsSymmetricGauge`; zero padding uses
`Fin.append`. The additional pointwise and total-sum consequences are stated directly on
native weak majorization. The constructive progress proof uses native `robinHood` only at
distinct coordinates; its old self-transfer definition was different and is not identified.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: `ForTauCeti.Analysis.Normed.FiniteLpGauge` (the `FiniteVector`
  vocabulary and stronger one-step progress theorem),
  `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm` and
  `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization`
  (two further copies of the same descent, now deleted in favour of this one).
* Extraction class: **split and generalized**.  The moved declarations keep their names and
  statements; the descent itself was restated for a symmetric-convex set, which is the common
  generalization of the three copies, and factored through the T-transform vocabulary.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** in the original extraction. The current module consumes accepted
  Tau Ceti majorization directly.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace IsWeaklyMajorizedBy

variable {n : ℕ}

/-- Coordinatewise domination implies weak majorization for antitone nonnegative tuples. -/
theorem of_pointwise {x y : Fin n → ℝ}
    (hxanti : Antitone x) (hyanti : Antitone y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i ≤ y i) : IsWeaklyMajorizedBy x y := by
  refine ⟨hxanti, hyanti, hx0, hy0, fun k => ?_⟩
  exact prefixSum_mono k hxy

/-- The full-sum consequence of weak majorization. -/
theorem sum_le {x y : Fin n → ℝ} (h : IsWeaklyMajorizedBy x y) :
    ∑ i, x i ≤ ∑ i, y i := by
  have hfull := h.prefixSum_le n
  rwa [prefixSum_of_le le_rfl, prefixSum_of_le le_rfl] at hfull

end IsWeaklyMajorizedBy

namespace FiniteVector

variable {n : ℕ}

/-! ### One-swap averages -/

/-- `q` is a **T-transform** of `y`: a convex combination of `y` with one of its
transpositions.  This is the elementary move of Hardy–Littlewood–Pólya majorization theory;
`isTTransform_robinHood` exhibits `robinHood` as one. -/
def IsTTransform (y q : Fin n → ℝ) : Prop :=
  ∃ (j l : Fin n) (c : ℝ), 0 ≤ c ∧ c ≤ 1 ∧ q = (1 - c) • y + c • (y ∘ Equiv.swap j l)

/-- **The elementary transfer is a T-transform.**  Moving `δ ≥ 0` from `j` to `l` without
overshooting (`δ ≤ q j - q l`) is averaging `q` with its `(j l)`-transposition. -/
theorem isTTransform_robinHood {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ q j - q l) : IsTTransform q (robinHood q j l δ) := by
  rcases eq_or_lt_of_le (le_trans hδ0 hδ) with hzero | hpos
  · -- No room to move: `δ = 0` and the transfer is the identity.
    have : δ = 0 := le_antisymm (hδ.trans hzero.symm.le) hδ0
    subst this
    refine ⟨j, l, 0, le_rfl, zero_le_one, ?_⟩
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    ext i
    rcases eq_or_ne i j with rfl | hij
    · simp [robinHood_apply_left q hjl]
    rcases eq_or_ne i l with rfl | hil
    · simp [robinHood_apply_right q hjl]
    · simp [robinHood_apply_of_ne q hij hil]
  · set c : ℝ := δ / (q j - q l) with hc
    have hcmul : c * (q j - q l) = δ := div_mul_cancel₀ δ (ne_of_gt hpos)
    refine ⟨j, l, c, div_nonneg hδ0 hpos.le, (div_le_one hpos).mpr hδ, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [robinHood_apply_left q hjl, Equiv.swap_apply_left]
      linear_combination hcmul
    rcases eq_or_ne i l with rfl | hil
    · rw [robinHood_apply_right q hjl, Equiv.swap_apply_right]
      linear_combination -hcmul
    · rw [robinHood_apply_of_ne q hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
      ring

/-! ### The transfer lemma -/

/-- **The Hardy–Littlewood–Pólya transfer lemma.**  Let `z` be antitone and nonnegative and
let `q` be nonnegative with every prefix sum of `z` dominated by that of `q`.  If `q` does not
already dominate `z` coordinatewise, then a *single* T-transform of `q` still dominates `z` in
prefix sums, is still nonnegative, and agrees with `z` in strictly more coordinates.

This is the whole content of the majorization descent: everything below iterates it.  The
transform moves mass from the least index `j` where `q` is strictly above `z` down to the
least index `l` where `q` falls strictly below `z`, stopping as soon as either coordinate
meets `z`. -/
theorem exists_isTTransform_of_not_forall_le {z q : Fin n → ℝ}
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hq0 : ∀ i, 0 ≤ q i)
    (hpre : ∀ k, prefixSum k z ≤ prefixSum k q) (hnot : ¬ ∀ i, z i ≤ q i) :
    ∃ q', IsTTransform q q' ∧ (∀ i, 0 ≤ q' i) ∧
      (∀ k, prefixSum k z ≤ prefixSum k q') ∧
      (Finset.univ.filter fun i => z i ≠ q' i).card <
        (Finset.univ.filter fun i => z i ≠ q i).card := by
  classical
  push Not at hnot
  -- `l`: the least index where `q` drops below `z`.
  have hSne : (Finset.univ.filter fun i : Fin n => q i < z i).Nonempty :=
    hnot.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  set l := (Finset.univ.filter fun i : Fin n => q i < z i).min' hSne with hldef
  have hlS : q l < z l :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSne)).2
  have hlmin : ∀ i, i < l → z i ≤ q i := by
    intro i hil
    by_contra hzq
    push Not at hzq
    exact absurd
      (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzq⟩))
      (not_le.mpr hil)
  -- Prefix domination at `l + 1` produces `j < l` with `z j < q j`.
  have hexj : ∃ j, j < l ∧ z j < q j := by
    by_contra hcon
    push Not at hcon
    have heq : ∀ i, i < l → z i = q i := fun i hi => le_antisymm (hlmin i hi) (hcon i hi)
    have hp := hpre ((l : ℕ) + 1)
    have hset : (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) + 1)
        = insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
        · exact Or.inl (Fin.ext heq')
        · exact Or.inr hlt
      · rintro (rfl | hi) <;> omega
    have hlnot : l ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) := by simp
    rw [prefixSum_def, prefixSum_def, hset, Finset.sum_insert hlnot,
      Finset.sum_insert hlnot] at hp
    have hsum_eq :
        ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), z i
          = ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), q i :=
      Finset.sum_congr rfl fun i hi => heq i (Fin.lt_def.mpr (Finset.mem_filter.mp hi).2)
    rw [hsum_eq] at hp
    linarith
  obtain ⟨j, hjl, hzj⟩ := hexj
  have hjl_ne : j ≠ l := ne_of_lt hjl
  -- The transform: move `δ` from coordinate `j` down to coordinate `l`.
  set δ : ℝ := min (q j - z j) (z l - q l) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₁ : δ ≤ q j - z j := min_le_left _ _
  have hδ₂ : δ ≤ z l - q l := min_le_right _ _
  have hδ₃ : δ ≤ q j - q l := by linarith [hz hjl.le]
  refine ⟨robinHood q j l δ, isTTransform_robinHood hjl_ne hδpos.le hδ₃, ?_, ?_, ?_⟩
  · -- (i) nonnegativity survives: coordinate `j` stops at `z j ≥ 0`.
    intro i
    rcases eq_or_ne i j with rfl | hij
    · rw [robinHood_apply_left q hjl_ne]
      linarith [hz0 i]
    rcases eq_or_ne i l with rfl | hil
    · rw [robinHood_apply_right q hjl_ne]
      linarith [hq0 l]
    · rw [robinHood_apply_of_ne q hij hil]
      exact hq0 i
  · -- (ii) prefix domination survives.
    intro k
    rw [prefixSum_robinHood]
    rcases lt_or_ge (j : ℕ) k with hjk | hjk
    · rcases lt_or_ge (l : ℕ) k with hlk | hlk
      · -- Both coordinates lie in the prefix: the transform is sum-preserving there.
        rw [ite_eq_left hjk, ite_eq_left hlk]
        linarith [hpre k]
      · -- Only `j` lies in the prefix, so the prefix of `q` loses exactly `δ`.  But the
        -- prefix gap was already at least `q j - z j ≥ δ`, since `q` dominates `z`
        -- coordinatewise below `l`.
        rw [ite_eq_left hjk, ite_eq_right (by omega : ¬ (l : ℕ) < k)]
        have hjmem : j ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
        have hterm : q j - z j ≤
            ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, (q i - z i) := by
          refine Finset.single_le_sum (f := fun i => q i - z i) (fun i hi => ?_) hjmem
          have hivk : (i : ℕ) < k := (Finset.mem_filter.mp hi).2
          linarith [hlmin i (Fin.lt_def.mpr (by omega : (i : ℕ) < (l : ℕ)))]
        rw [Finset.sum_sub_distrib] at hterm
        simp only [prefixSum_def]
        linarith
    · -- Neither coordinate lies in the prefix: the sums are unchanged.
      rw [ite_eq_right (by omega), ite_eq_right (by omega : ¬ (l : ℕ) < k)]
      linarith [hpre k]
  · -- (iii) the transform kills at least one disagreement and creates none.
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ?_)
    · intro i hi
      obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
      have hij : i ≠ j := by rintro rfl; exact absurd heq hzj.ne
      have hil : i ≠ l := by rintro rfl; exact absurd heq hlS.ne'
      exact hine (by rw [robinHood_apply_of_ne q hij hil]; exact heq)
    · rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
      · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
        have : robinHood q j l δ j = z j := by
          rw [robinHood_apply_left q hjl_ne, hδdef, hmin]; ring
        simp [this]
      · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
        have : robinHood q j l δ l = z l := by
          rw [robinHood_apply_right q hjl_ne, hδdef, hmin]; ring
        simp [this]

end FiniteVector

end TauCeti
