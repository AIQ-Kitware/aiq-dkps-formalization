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

The finite gauge presentation, zero-padding presentation and sorting consequences remain for
subsequent canonical representation migrations. The additional pointwise and total-sum
consequences are stated directly on native weak majorization.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: `ForTauCeti.Analysis.Normed.FiniteLpGauge` (the `FiniteVector`
  vocabulary, `FiniteSymmetricGauge`, and its majorization monotonicity),
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

variable {n m : ℕ}

/-! ### Zero padding -/

/-- Right zero-padding from length `n` to length `n + m`. -/
@[expose]
def zeroPadRight (x : Fin n → ℝ) : Fin (n + m) → ℝ :=
  fun i => if hi : (i : ℕ) < n then x ⟨i, hi⟩ else 0

/-- Zero padding leaves the original coordinates alone. -/
@[simp] theorem zeroPadRight_left (x : Fin n → ℝ) (i : Fin n) :
    zeroPadRight (m := m) x (Fin.castAdd m i) = x i := by
  simp [zeroPadRight]

/-- The padded coordinates are zero. -/
@[simp] theorem zeroPadRight_right (x : Fin n → ℝ) (i : Fin m) :
    zeroPadRight (m := m) x (Fin.natAdd n i) = 0 := by
  simp [zeroPadRight]

/-- Zero padding preserves every prefix sum. -/
theorem prefixSum_zeroPadRight (k : ℕ) (x : Fin n → ℝ) :
    prefixSum k (zeroPadRight (m := m) x) = prefixSum k x := by
  simp only [prefixSum_def]
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp [zeroPadRight]

/-- A decreasing nonnegative vector remains decreasing after appending zeros. -/
theorem antitone_zeroPadRight {x : Fin n → ℝ}
    (hxanti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    Antitone (zeroPadRight (m := m) x) := by
  intro i j hij
  have hijv : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
  unfold zeroPadRight
  -- the antitonicity goal is `pad j ≤ pad i`, so the outer split is on `j`
  split_ifs with hj hi
  · apply hxanti
    exact Fin.le_def.mpr hijv
  · -- `i` sits below `j < n`, so this branch is vacuous
    exact absurd hijv (by omega)
  · exact hx0 _
  · exact le_rfl

/-- Zero padding preserves nonnegativity. -/
theorem zeroPadRight_nonneg {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ zeroPadRight (m := m) x i := by
  intro i
  unfold zeroPadRight
  split_ifs
  · exact hx0 _
  · exact le_rfl

/-! ### T-transforms -/

/-- The **elementary transfer** of `δ` from coordinate `j` to coordinate `l`: the
Hardy–Littlewood–Pólya "Robin Hood" operation, which takes `δ` from the richer coordinate and
gives it to the poorer one. -/
def transfer (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) : Fin n → ℝ :=
  Function.update (Function.update q j (q j - δ)) l (q l + δ)

/-- At the donor coordinate the transfer removes `δ`.  Needs `j ≠ l`, since a self-transfer would
have the receiving update overwrite the donating one. -/
theorem transfer_apply_left {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) :
    transfer q j l δ j = q j - δ := by
  rw [transfer, Function.update_of_ne hjl, Function.update_self]

/-- At the receiving coordinate the transfer adds `δ`. -/
theorem transfer_apply_right (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) :
    transfer q j l δ l = q l + δ := by
  rw [transfer, Function.update_self]

/-- A transfer leaves every coordinate other than the two it moves mass between unchanged. -/
theorem transfer_apply_of_ne {q : Fin n → ℝ} {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l)
    (δ : ℝ) : transfer q j l δ i = q i := by
  rw [transfer, Function.update_of_ne hil, Function.update_of_ne hij]

/-- A transfer of nothing is the identity. -/
@[simp] theorem transfer_zero (q : Fin n → ℝ) (j l : Fin n) : transfer q j l 0 = q := by
  simp [transfer]

/-- The prefix sums of a transfer: the moved mass leaves the prefix once it passes `j` and
returns once it passes `l`.  In particular a transfer preserves every prefix sum that
contains both coordinates or neither. -/
theorem prefixSum_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) (k : ℕ) :
    prefixSum k (transfer q j l δ) =
      prefixSum k q - (if (j : ℕ) < k then δ else 0) + (if (l : ℕ) < k then δ else 0) := by
  classical
  have hsplit : transfer q j l δ =
      q + ((fun i => if i = j then -δ else 0) + fun i => if i = l then δ else 0) := by
    funext i
    simp only [Pi.add_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, ite_eq_left rfl, ite_eq_right hjl]
      ring
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, ite_eq_right hij, ite_eq_left rfl]
      ring
    · rw [transfer_apply_of_ne hij hil, ite_eq_right hij, ite_eq_right hil]
      ring
  have hj : prefixSum k (fun i : Fin n => if i = j then -δ else 0) =
      if (j : ℕ) < k then -δ else 0 := by
    simp [prefixSum_def]
  have hl : prefixSum k (fun i : Fin n => if i = l then δ else 0) =
      if (l : ℕ) < k then δ else 0 := by
    simp [prefixSum_def]
  rw [hsplit, prefixSum_add, prefixSum_add, hj, hl]
  split_ifs <;> ring

/-- `q` is a **T-transform** of `y`: a convex combination of `y` with one of its
transpositions.  This is the elementary move of Hardy–Littlewood–Pólya majorization theory;
`isTTransform_transfer` exhibits `transfer` as one. -/
def IsTTransform (y q : Fin n → ℝ) : Prop :=
  ∃ (j l : Fin n) (c : ℝ), 0 ≤ c ∧ c ≤ 1 ∧ q = (1 - c) • y + c • (y ∘ Equiv.swap j l)

/-- **The elementary transfer is a T-transform.**  Moving `δ ≥ 0` from `j` to `l` without
overshooting (`δ ≤ q j - q l`) is averaging `q` with its `(j l)`-transposition. -/
theorem isTTransform_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ q j - q l) : IsTTransform q (transfer q j l δ) := by
  rcases eq_or_lt_of_le (le_trans hδ0 hδ) with hzero | hpos
  · -- No room to move: `δ = 0` and the transfer is the identity.
    have : δ = 0 := le_antisymm (hδ.trans hzero.symm.le) hδ0
    subst this
    refine ⟨j, l, 0, le_rfl, zero_le_one, ?_⟩
    simp
  · set c : ℝ := δ / (q j - q l) with hc
    have hcmul : c * (q j - q l) = δ := div_mul_cancel₀ δ (ne_of_gt hpos)
    refine ⟨j, l, c, div_nonneg hδ0 hpos.le, (div_le_one hpos).mpr hδ, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, Equiv.swap_apply_left]
      linear_combination hcmul
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, Equiv.swap_apply_right]
      linear_combination -hcmul
    · rw [transfer_apply_of_ne hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
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
  refine ⟨transfer q j l δ, isTTransform_transfer hjl_ne hδpos.le hδ₃, ?_, ?_, ?_⟩
  · -- (i) nonnegativity survives: coordinate `j` stops at `z j ≥ 0`.
    intro i
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl_ne]
      linarith [hz0 i]
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right]
      linarith [hq0 l]
    · rw [transfer_apply_of_ne hij hil]
      exact hq0 i
  · -- (ii) prefix domination survives.
    intro k
    rw [prefixSum_transfer hjl_ne]
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
      exact hine (by rw [transfer_apply_of_ne hij hil]; exact heq)
    · rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
      · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
        have : transfer q j l δ j = z j := by
          rw [transfer_apply_left hjl_ne, hδdef, hmin]; ring
        simp [this]
      · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
        have : transfer q j l δ l = z l := by
          rw [transfer_apply_right, hδdef, hmin]; ring
        simp [this]

end FiniteVector

/-! ### Finite symmetric gauges -/

/-- Algebraic interface for a finite symmetric gauge.  These are precisely the
properties used by the T-transform proof of weak-majorization monotonicity. -/
structure FiniteSymmetricGauge (n : ℕ) where
  toFun : (Fin n → ℝ) → ℝ
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
  real_smul' : ∀ c x, toFun (c • x) = |c| * toFun x
  perm' : ∀ x (π : Equiv.Perm (Fin n)), toFun (x ∘ π) = toFun x
  neg_single' : ∀ x j, toFun (Function.update x j (-(x j))) = toFun x

namespace FiniteSymmetricGauge

variable {n : ℕ}

/-- Apply a finite symmetric gauge directly to a vector, writing `Φ x` for `Φ.toFun x`. -/
instance : CoeFun (FiniteSymmetricGauge n) fun _ => (Fin n → ℝ) → ℝ :=
  ⟨FiniteSymmetricGauge.toFun⟩

variable (Φ : FiniteSymmetricGauge n)

/-- Subadditivity of a finite symmetric gauge. -/
theorem add_le (x y : Fin n → ℝ) : Φ (x + y) ≤ Φ x + Φ y :=
  Φ.add_le' x y

/-- Absolute homogeneity of a finite symmetric gauge. -/
theorem real_smul (c : ℝ) (x : Fin n → ℝ) :
    Φ (c • x) = |c| * Φ x :=
  Φ.real_smul' c x

/-- A finite symmetric gauge is invariant under permuting coordinates -- the *symmetric* half of
the name. -/
theorem perm (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Φ (x ∘ π) = Φ x :=
  Φ.perm' x π

/-- A finite symmetric gauge is invariant under flipping the sign of a single coordinate.  With
`perm` this gives invariance under all signed permutations, which is what makes the sublevel sets
symmetric-convex. -/
theorem neg_single (x : Fin n → ℝ) (j : Fin n) :
    Φ (Function.update x j (-(x j))) = Φ x :=
  Φ.neg_single' x j

/-- **Every sublevel set of a finite symmetric gauge is symmetric-convex.**  This is the
bridge that lets the whole majorization theory be proved once, for sets, and read off for
gauges: convexity is subadditivity plus absolute homogeneity, and the two closure properties
are the gauge's permutation and sign-flip invariance. -/
theorem isSymmetricConvex_sublevel (r : ℝ) :
    IsSymmetricConvex {x : Fin n → ℝ | Φ x ≤ r} where
  convex := by
    intro x hx y hy a b ha hb hab
    have hx' : Φ x ≤ r := hx
    have hy' : Φ y ≤ r := hy
    have : Φ (a • x + b • y) ≤ a * Φ x + b * Φ y := by
      refine (Φ.add_le _ _).trans_eq ?_
      rw [Φ.real_smul, Φ.real_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hle : a * Φ x + b * Φ y ≤ a * r + b * r :=
      add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
    have : Φ (a • x + b • y) ≤ r := by
      refine this.trans (hle.trans_eq ?_)
      rw [← add_mul, hab, one_mul]
    exact this
  comp_perm_mem := fun π y hy => by
    have : Φ (y ∘ π) ≤ r := by rw [Φ.perm]; exact hy
    exact this
  update_neg_mem := fun y hy j => by
    have : Φ (Function.update y j (-(y j))) ≤ r := by rw [Φ.neg_single]; exact hy
    exact this

/-- Shrinking one coordinate of `y` (in absolute value) does not increase the
gauge: `update y j t` with `|t| ≤ y j` is a convex combination of `y` and its
`j`-th sign flip. -/
theorem update_le {y : Fin n → ℝ} {j : Fin n} {t : ℝ} (ht : |t| ≤ y j) :
    Φ (Function.update y j t) ≤ Φ y := by
  have hy : y ∈ {x : Fin n → ℝ | Φ x ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).update_mem hy j (ht.trans (le_abs_self _))

/-- **Coordinatewise monotonicity of the gauge** on nonnegative vectors. -/
theorem mono {x y : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) : Φ x ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).isSolid hy
    (fun i => by
      change |x i| ≤ |y i|
      rw [abs_of_nonneg (hx0 i), abs_of_nonneg ((hx0 i).trans (hxy i))]
      exact hxy i)

/-- **The T-transform descent on the gauge** — the engine of Fan dominance.
If `z` is antitone and nonnegative, `y` is nonnegative, and every prefix sum
of `z` is dominated by the corresponding prefix sum of `y`, then `Φ z ≤ Φ y`.

An instance of `IsSymmetricConvex.mem_of_prefixSum_le` at the sublevel set
`{x | Φ x ≤ Φ y}`. -/
theorem le_of_prefixSum_le {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (_hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, y i) :
    Φ z ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact (Φ.isSymmetricConvex_sublevel (Φ y)).mem_of_prefixSum_le hy hz_anti hz0
    (by simpa only [prefixSum_def] using hpre)

/-- Every finite symmetric gauge is monotone under weak majorization. -/
theorem mono_weaklyMajorized {x y : Fin n → ℝ}
    (h : IsWeaklyMajorizedBy x y) : Φ x ≤ Φ y := by
  have hy : y ∈ {v : Fin n → ℝ | Φ v ≤ Φ y} := by exact le_refl (Φ y)
  exact h.mem (Φ.isSymmetricConvex_sublevel (Φ y)) hy

/-! ### Antitone rearrangement

`Tuple.sort` produces a *monotone* rearrangement.  Several results downstream --
realizing a sequence as the approximation numbers of a diagonal operator, and
the block-sum statement that the sequence of a block-diagonal sum is the
decreasing rearrangement of the union -- need the *antitone* one instead.

Composing the sorting permutation with `Fin.rev` supplies it, and a symmetric
gauge cannot tell the difference, since permutation invariance is one of its
axioms.
-/

/-- `Fin.rev` as a permutation: it is an involution. -/
@[expose]
def revPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm Fin.rev Fin.rev_rev

/-- `revPerm` acts as `Fin.rev`. -/
@[simp]
theorem revPerm_apply {n : ℕ} (i : Fin n) : revPerm n i = i.rev := rfl

/-- The permutation putting a tuple into antitone order: sort, then reverse. -/
noncomputable def antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (revPerm n).trans (Tuple.sort f)

/-- **The rearrangement is antitone.**

`Tuple.monotone_sort` makes `f ∘ sort f` monotone, and `Fin.rev` is strictly
antitone, so the composite reverses order. -/
theorem antitone_comp_antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) :
    Antitone (f ∘ antitoneSortPerm f) := by
  intro i j hij
  have hrev : (j : Fin n).rev ≤ (i : Fin n).rev := Fin.rev_le_rev.mpr hij
  exact Tuple.monotone_sort f hrev

/-- A finite symmetric gauge does not see the rearrangement. -/
theorem apply_antitoneSortPerm {n : ℕ}
    (Φ : FiniteSymmetricGauge n) (f : Fin n → ℝ) :
    Φ (f ∘ antitoneSortPerm f) = Φ f :=
  Φ.perm f (antitoneSortPerm f)

end FiniteSymmetricGauge

end TauCeti
