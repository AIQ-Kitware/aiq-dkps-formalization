/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking


Wave-1 migration provenance: original module `ForMathlib.Analysis.Normed.FiniteLpGauge` at the
Davis--Kahan repository; moved to `ForTauCeti` with the namespace
`ForMathlib` renamed `TauCeti` (module-system conversion deferred to a
later mechanical pass).  No mathematical change
beyond routing historical Courant--Fischer names through the transitional
`CourantFischerCompat` shim.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Fin


/-!
# Finite symmetric gauges and weak majorization

This file provides the finite-vector analytic layer used by rectangular
Schatten norms.

The central objects are:

* `FiniteVector.prefixSum`, the prefix sum of a vector indexed by `Fin n`;
* `FiniteVector.WeaklyMajorized`, weak majorization of the canonical decreasing
  nonnegative representatives;
* `FiniteSymmetricGauge`, the algebraic interface needed by the finite
  T-transform proof;
* `FiniteVector.lpGauge`, the real `ℓᵖ` gauge for `1 ≤ p < ∞`;
* monotonicity of every finite symmetric gauge, hence every `ℓᵖ` gauge, under
  weak majorization;
* the finite Minkowski inequality and zero-padding bridges.

The weak-majorization representation deliberately records antitonicity and
nonnegativity.  Singular values already arrive in exactly this canonical form,
so no second sorting implementation is introduced.
-/

namespace TauCeti

open scoped BigOperators

namespace FiniteVector

variable {n m : ℕ}

/-- Sum of the first `k` coordinates of a finite vector.  For `k ≥ n` this is
its full sum. -/
def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i

@[simp] theorem prefixSum_zero (k : ℕ) :
    prefixSum k (0 : Fin n → ℝ) = 0 := by
  simp [prefixSum]

@[simp] theorem prefixSum_add (k : ℕ) (x y : Fin n → ℝ) :
    prefixSum k (x + y) = prefixSum k x + prefixSum k y := by
  simp [prefixSum, Finset.sum_add_distrib]

@[simp] theorem prefixSum_smul (k : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    prefixSum k (c • x) = c * prefixSum k x := by
  simp [prefixSum, Finset.mul_sum]

/-- Prefix sums stabilize after the vector length. -/
theorem prefixSum_eq_full_sum_of_le (x : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    prefixSum k x = ∑ i, x i := by
  unfold prefixSum
  have hfilter : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) =
      Finset.univ :=
    Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk
  rw [hfilter]

/-- Weak majorization for vectors already presented in decreasing,
nonnegative order. -/
structure WeaklyMajorized (x y : Fin n → ℝ) : Prop where
  left_antitone : Antitone x
  right_antitone : Antitone y
  left_nonneg : ∀ i, 0 ≤ x i
  right_nonneg : ∀ i, 0 ≤ y i
  prefix_le : ∀ k, prefixSum k x ≤ prefixSum k y

local infix:50 " ≺w " => WeaklyMajorized

namespace WeaklyMajorized

/-- Weak majorization is reflexive on decreasing nonnegative vectors. -/
theorem refl {x : Fin n → ℝ} (hxanti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    x ≺w x :=
  ⟨hxanti, hxanti, hx0, hx0, fun _ => le_rfl⟩

/-- Weak majorization is transitive. -/
theorem trans {x y z : Fin n → ℝ} (hxy : x ≺w y) (hyz : y ≺w z) :
    x ≺w z :=
  ⟨hxy.left_antitone, hyz.right_antitone,
    hxy.left_nonneg, hyz.right_nonneg,
    fun k => (hxy.prefix_le k).trans (hyz.prefix_le k)⟩

/-- Coordinatewise domination implies weak majorization when both vectors are
already decreasing and nonnegative. -/
theorem of_pointwise {x y : Fin n → ℝ}
    (hxanti : Antitone x) (hyanti : Antitone y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i ≤ y i) : x ≺w y := by
  refine ⟨hxanti, hyanti, hx0, hy0, fun k => ?_⟩
  exact Finset.sum_le_sum fun i _ => hxy i

/-- Weak majorization is compatible with vector addition. -/
theorem add {x₁ x₂ y₁ y₂ : Fin n → ℝ}
    (h₁ : x₁ ≺w y₁) (h₂ : x₂ ≺w y₂) :
    x₁ + x₂ ≺w y₁ + y₂ := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact add_le_add (h₁.left_antitone hij) (h₂.left_antitone hij)
  · intro i j hij
    exact add_le_add (h₁.right_antitone hij) (h₂.right_antitone hij)
  · intro i
    exact add_nonneg (h₁.left_nonneg i) (h₂.left_nonneg i)
  · intro i
    exact add_nonneg (h₁.right_nonneg i) (h₂.right_nonneg i)
  · rw [prefixSum_add, prefixSum_add]
    exact add_le_add (h₁.prefix_le k) (h₂.prefix_le k)

/-- Nonnegative scaling preserves weak majorization. -/
theorem nonneg_smul {x y : Fin n → ℝ} (h : x ≺w y)
    {c : ℝ} (hc : 0 ≤ c) : c • x ≺w c • y := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (h.left_antitone hij) hc
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (h.right_antitone hij) hc
  · intro i
    exact mul_nonneg hc (h.left_nonneg i)
  · intro i
    exact mul_nonneg hc (h.right_nonneg i)
  · rw [prefixSum_smul, prefixSum_smul]
    exact mul_le_mul_of_nonneg_left (h.prefix_le k) hc

/-- The full-sum consequence of weak majorization. -/
theorem sum_le {x y : Fin n → ℝ} (h : x ≺w y) :
    ∑ i, x i ≤ ∑ i, y i := by
  have hfull := h.prefix_le n
  rw [prefixSum_eq_full_sum_of_le x le_rfl,
    prefixSum_eq_full_sum_of_le y le_rfl] at hfull
  exact hfull

end WeaklyMajorized

/-- Right zero-padding from length `n` to length `n + m`. -/
def zeroPadRight (x : Fin n → ℝ) : Fin (n + m) → ℝ :=
  fun i => if hi : (i : ℕ) < n then x ⟨i, hi⟩ else 0

@[simp] theorem zeroPadRight_left (x : Fin n → ℝ) (i : Fin n) :
    zeroPadRight (m := m) x (Fin.castAdd m i) = x i := by
  simp [zeroPadRight]

@[simp] theorem zeroPadRight_right (x : Fin n → ℝ) (i : Fin m) :
    zeroPadRight (m := m) x (Fin.natAdd n i) = 0 := by
  simp [zeroPadRight]

/-- Zero padding preserves every prefix sum. -/
theorem prefixSum_zeroPadRight (k : ℕ) (x : Fin n → ℝ) :
    prefixSum k (zeroPadRight (m := m) x) = prefixSum k x := by
  unfold prefixSum
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

/-- Appending a common zero tail preserves weak majorization. -/
theorem WeaklyMajorized.zeroPadRight {x y : Fin n → ℝ}
    (h : WeaklyMajorized x y) :
    WeaklyMajorized (zeroPadRight (m := m) x)
      (zeroPadRight (m := m) y) := by
  exact ⟨antitone_zeroPadRight h.left_antitone h.left_nonneg,
    antitone_zeroPadRight h.right_antitone h.right_nonneg,
    zeroPadRight_nonneg h.left_nonneg,
    zeroPadRight_nonneg h.right_nonneg, fun k => by
      simpa only [prefixSum_zeroPadRight] using h.prefix_le k⟩

end FiniteVector

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

instance : CoeFun (FiniteSymmetricGauge n) fun _ => (Fin n → ℝ) → ℝ :=
  ⟨FiniteSymmetricGauge.toFun⟩

variable (Φ : FiniteSymmetricGauge n)

theorem add_le (x y : Fin n → ℝ) : Φ (x + y) ≤ Φ x + Φ y :=
  Φ.add_le' x y

theorem real_smul (c : ℝ) (x : Fin n → ℝ) :
    Φ (c • x) = |c| * Φ x :=
  Φ.real_smul' c x

theorem perm (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Φ (x ∘ π) = Φ x :=
  Φ.perm' x π

theorem neg_single (x : Fin n → ℝ) (j : Fin n) :
    Φ (Function.update x j (-(x j))) = Φ x :=
  Φ.neg_single' x j

/-- Shrinking one coordinate of `y` (in absolute value) does not increase the
gauge: `update y j t` with `|t| ≤ y j` is a convex combination of `y` and its
`j`-th sign flip. -/
theorem update_le {y : Fin n → ℝ}
    {j : Fin n} {t : ℝ} (ht : |t| ≤ y j) :
    Φ (Function.update y j t) ≤ Φ y := by
  have hyj : 0 ≤ y j := le_trans (abs_nonneg t) ht
  rcases hyj.eq_or_lt with h0 | hpos
  · -- `y j = 0` forces `t = 0`: the update is trivial.
    have ht0 : t = 0 := by
      have h1 : |t| ≤ 0 := by rw [h0]; exact ht
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg t))
    have hupd : Function.update y j t = y := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, ht0, ← h0]
      · rw [Function.update_of_ne hij]
    rw [hupd]
  · set c₁ : ℝ := (y j + t) / (2 * y j) with hc₁
    set c₂ : ℝ := (y j - t) / (2 * y j) with hc₂
    obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
    have h2yj : 0 < 2 * y j := by linarith
    have hyj0 : (2 : ℝ) * y j ≠ 0 := ne_of_gt h2yj
    have hc₁0 : 0 ≤ c₁ := div_nonneg (by linarith) h2yj.le
    have hc₂0 : 0 ≤ c₂ := div_nonneg (by linarith) h2yj.le
    have hsum : c₁ + c₂ = 1 := by
      rw [hc₁, hc₂]
      field_simp
      ring
    have hdecomp : Function.update y j t
        = c₁ • y + c₂ • Function.update y j (-(y j)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, Function.update_self, hc₁, hc₂]
        field_simp
        ring
      · rw [Function.update_of_ne hij, Function.update_of_ne hij, ← add_mul,
          hsum, one_mul]
    calc Φ (Function.update y j t)
        = Φ (c₁ • y + c₂ • Function.update y j (-(y j))) := by
          rw [hdecomp]
      _ ≤ Φ (c₁ • y) + Φ (c₂ • Function.update y j (-(y j))) :=
          Φ.add_le _ _
      _ = c₁ * Φ y
          + c₂ * Φ (Function.update y j (-(y j))) := by
          rw [Φ.real_smul, Φ.real_smul, abs_of_nonneg hc₁0,
            abs_of_nonneg hc₂0]
      _ = c₁ * Φ y + c₂ * Φ y := by
          rw [Φ.neg_single]
      _ = Φ y := by
          rw [← add_mul, hsum, one_mul]

/-- **Coordinatewise monotonicity of the gauge** on nonnegative vectors. -/
theorem mono {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    Φ x ≤ Φ y := by
  -- Induct on the number of coordinates where `x` and `y` disagree.
  have H : ∀ d (y : Fin n → ℝ),
      (Finset.univ.filter fun i => x i ≠ y i).card ≤ d → (∀ i, x i ≤ y i) →
      Φ x ≤ Φ y := by
    intro d
    induction d with
    | zero =>
      intro y hcard _
      have hemp : (Finset.univ.filter fun i => x i ≠ y i) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hxy_eq : x = y := funext fun i => by
        by_contra hne
        have hi : i ∈ Finset.univ.filter fun i => x i ≠ y i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        rw [hemp] at hi
        simp at hi
      rw [hxy_eq]
    | succ d ih =>
      intro y hcard hxy
      by_cases hx_eq : x = y
      · rw [hx_eq]
      · have hne : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          refine hx_eq (funext fun i => ?_)
          by_contra hne
          have hi : i ∈ Finset.univ.filter fun i => x i ≠ y i :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hemp] at hi
          simp at hi
        obtain ⟨j, hj⟩ := hne
        set y' := Function.update y j (x j) with hy'def
        have hstep : Φ y' ≤ Φ y := by
          refine Φ.update_le ?_
          rw [abs_of_nonneg (hx0 j)]
          exact hxy j
        have hxy' : ∀ i, x i ≤ y' i := fun i => by
          rcases eq_or_ne i j with rfl | hij
          · rw [hy'def, Function.update_self]
          · rw [hy'def, Function.update_of_ne hij]
            exact hxy i
        have hsub : (Finset.univ.filter fun i => x i ≠ y' i)
            ⊆ (Finset.univ.filter fun i => x i ≠ y i).erase j := by
          intro i hi
          obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
          have hij : i ≠ j := by
            rintro rfl
            exact hine (by rw [hy'def, Function.update_self])
          refine Finset.mem_erase.mpr
            ⟨hij, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rw [hy'def, Function.update_of_ne hij] at hine
          exact hine
        have hcard' : (Finset.univ.filter fun i => x i ≠ y' i).card ≤ d := by
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem hj
          omega
        exact le_trans (ih y' hcard' hxy') hstep
  exact H _ y le_rfl hxy

/-! ### The T-transform descent -/

/-- **The T-transform descent on the gauge** — the engine of Fan dominance.
If `z` is antitone and nonnegative, `y` is nonnegative, and every prefix sum
of `z` is dominated by the corresponding prefix sum of `y`, then
`Φ_N(z) ≤ Φ_N(y)`.

No total-sum equality is assumed, no majorization completion and no
Hardy–Littlewood–Pólya theorem is used: each descent step averages `y` with a
transposition of itself, which costs one triangle inequality, one
homogeneity, and one swap invariance of the gauge. -/
theorem le_of_prefixSum_le
    {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) :
    Φ z ≤ Φ y := by
  -- Induct on the number of coordinates where `z` and `y` disagree.
  have H : ∀ d (y : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ y i).card ≤ d → (∀ i, 0 ≤ y i) →
      (∀ m : ℕ,
        ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
          ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) →
      Φ z ≤ Φ y := by
    intro d
    induction d with
    | zero =>
      intro y hcard _ _
      have hemp : (Finset.univ.filter fun i => z i ≠ y i) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hzy : z = y := funext fun i => by
        by_contra hne
        have hi : i ∈ Finset.univ.filter fun i => z i ≠ y i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        rw [hemp] at hi
        simp at hi
      rw [hzy]
    | succ d ih =>
      intro y hcard hy0 hpre
      by_cases hall : ∀ i, z i ≤ y i
      · exact Φ.mono hz0 hall
      push Not at hall
      -- `l`: the least index where `y` drops below `z`.
      have hSne : (Finset.univ.filter fun i : Fin n => y i < z i).Nonempty :=
        hall.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      set l := (Finset.univ.filter fun i : Fin n => y i < z i).min' hSne
        with hldef
      have hlS : y l < z l :=
        (Finset.mem_filter.mp
          ((Finset.univ.filter fun i : Fin n => y i < z i).min'_mem hSne)).2
      have hlmin : ∀ i, i < l → z i ≤ y i := by
        intro i hil
        by_contra hzy
        push Not at hzy
        exact absurd
          (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy⟩))
          (not_le.mpr hil)
      -- Prefix domination at `l + 1` produces `j < l` with `z j < y j`.
      have hexj : ∃ j, j < l ∧ z j < y j := by
        by_contra h
        push Not at h
        have heq : ∀ i, i < l → z i = y i := fun i hi =>
          le_antisymm (hlmin i hi) (h i hi)
        have hp := hpre ((l : ℕ) + 1)
        have hset : (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) + 1)
            = insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ))
            := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert]
          constructor
          · intro hi
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
            · exact Or.inl (Fin.ext heq')
            · exact Or.inr hlt
          · rintro (rfl | hi)
            · omega
            · omega
        have hlnot :
            l ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) := by
          simp
        rw [hset, Finset.sum_insert hlnot, Finset.sum_insert hlnot] at hp
        have hsum_eq :
            ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ), z i
              = ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ),
                  y i := by
          refine Finset.sum_congr rfl fun i hi => heq i ?_
          exact Fin.lt_def.mpr (Finset.mem_filter.mp hi).2
        rw [hsum_eq] at hp
        linarith
      obtain ⟨j, hjl, hzj⟩ := hexj
      have hjl_ne : j ≠ l := ne_of_lt hjl
      have hjl_nat : (j : ℕ) < (l : ℕ) := Fin.lt_def.mp hjl
      have hzlj : z l ≤ z j := hz_anti hjl.le
      have hylj : y l < y j := by linarith
      -- The transform: move `δ` from coordinate `j` to coordinate `l`.
      set δ : ℝ := min (y j - z j) (z l - y l) with hδdef
      have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
      have hδ₁ : δ ≤ y j - z j := min_le_left _ _
      have hδ₂ : δ ≤ z l - y l := min_le_right _ _
      have hδlt : δ < y j - y l := lt_of_le_of_lt hδ₁ (by linarith)
      have hyjl_pos : 0 < y j - y l := by linarith
      set c₂ : ℝ := δ / (y j - y l) with hc₂def
      have hc₂pos : 0 < c₂ := div_pos hδpos hyjl_pos
      have hc₂lt : c₂ < 1 := (div_lt_one hyjl_pos).mpr hδlt
      have hc₂mul : c₂ * (y j - y l) = δ :=
        div_mul_cancel₀ δ (ne_of_gt hyjl_pos)
      set y' : Fin n → ℝ :=
        Function.update (Function.update y j (y j - δ)) l (y l + δ)
        with hy'def
      have hy'j : y' j = y j - δ := by
        rw [hy'def, Function.update_of_ne hjl_ne, Function.update_self]
      have hy'l : y' l = y l + δ := by rw [hy'def, Function.update_self]
      have hy'i : ∀ i, i ≠ j → i ≠ l → y' i = y i := fun i hij hil => by
        rw [hy'def, Function.update_of_ne hil, Function.update_of_ne hij]
      -- (i) `y'` is a convex combination of `y` and its `(j l)`-swap.
      have hcomb : y' = (1 - c₂) • y + c₂ • (y ∘ Equiv.swap j l) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Function.comp_apply]
        rcases eq_or_ne i j with rfl | hij
        · rw [hy'j, Equiv.swap_apply_left]
          linear_combination hc₂mul
        rcases eq_or_ne i l with rfl | hil
        · rw [hy'l, Equiv.swap_apply_right]
          linear_combination -hc₂mul
        · rw [hy'i i hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
          ring
      -- (ii) `y'` stays nonnegative.
      have hy'0 : ∀ i, 0 ≤ y' i := by
        intro i
        rcases eq_or_ne i j with heq | hij
        · rw [heq, hy'j]
          linarith [hz0 j]
        rcases eq_or_ne i l with heq | hil
        · rw [heq, hy'l]
          linarith [hy0 l]
        · rw [hy'i i hij hil]
          exact hy0 i
      -- (iii) prefix domination survives the transform.
      have hpre' : ∀ m : ℕ,
          ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
            ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y' i := by
        intro m
        rcases le_or_gt m (j : ℕ) with hmj | hmj
        · -- Neither `j` nor `l` lies in the prefix: sums unchanged.
          have hcong : ∀ i ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m), y' i = y i := by
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hij : i ≠ j := fun h => by subst h; omega
            have hil : i ≠ l := fun h => by subst h; omega
            exact hy'i i hij hil
          rw [Finset.sum_congr rfl hcong]
          exact hpre m
        rcases le_or_gt m (l : ℕ) with hml | hml
        · -- `j` in, `l` out: the prefix of `y'` lost exactly `δ`, but the
          -- prefix gap was already at least `y j − z j ≥ δ`.
          have hcong : ∀ i ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m),
              y' i = Function.update y j (y j - δ) i := by
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hil : i ≠ l := fun h => by subst h; omega
            rw [hy'def, Function.update_of_ne hil]
          have hjmem : j ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj⟩
          rw [Finset.sum_congr rfl hcong, Finset.sum_update_of_mem hjmem]
          have hysplit : ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y i
              = y j + ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {j}, y i := by
            rw [← Finset.erase_eq]
            exact (Finset.add_sum_erase _ y hjmem).symm
          have hterm : y j - z j ≤ ∑ i ∈ Finset.univ.filter
              (fun i : Fin n => (i : ℕ) < m), (y i - z i) := by
            refine Finset.single_le_sum (f := fun i => y i - z i) ?_ hjmem
            intro i hi
            have hivm : (i : ℕ) < m := (Finset.mem_filter.mp hi).2
            have hil : i < l := Fin.lt_def.mpr (by omega)
            linarith [hlmin i hil]
          rw [Finset.sum_sub_distrib] at hterm
          linarith [hpre m]
        · -- Both `j` and `l` in the prefix: the transform is sum-preserving.
          have hjmem : j ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          have hlmem : l ∈ Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hml⟩
          have hjmem' : j ∈ (Finset.univ.filter
              fun i : Fin n => (i : ℕ) < m) \ {l} :=
            Finset.mem_sdiff.mpr ⟨hjmem, by simp [hjl_ne]⟩
          have hEq : ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y' i
              = ∑ i ∈ Finset.univ.filter
                fun i : Fin n => (i : ℕ) < m, y i := by
            have h1 : ∑ i ∈ Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m, y' i
                = (y l + δ) + ∑ i ∈ (Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l},
                    Function.update y j (y j - δ) i := by
              rw [hy'def]
              exact Finset.sum_update_of_mem hlmem _ _
            have h2 : ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {l},
                  Function.update y j (y j - δ) i
                = (y j - δ) + ∑ i ∈ ((Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}) \ {j}, y i :=
              Finset.sum_update_of_mem hjmem' _ _
            have h3 : ∑ i ∈ Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m, y i
                = y l + ∑ i ∈ (Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}, y i := by
              rw [← Finset.erase_eq]
              exact (Finset.add_sum_erase _ y hlmem).symm
            have h4 : ∑ i ∈ (Finset.univ.filter
                  fun i : Fin n => (i : ℕ) < m) \ {l}, y i
                = y j + ∑ i ∈ ((Finset.univ.filter
                    fun i : Fin n => (i : ℕ) < m) \ {l}) \ {j}, y i := by
              rw [← Finset.erase_eq, ← Finset.erase_eq]
              exact (Finset.add_sum_erase _ y (by rwa [Finset.erase_eq])).symm
            rw [h1, h2, h3, h4]
            ring
          rw [hEq]
          exact hpre m
      -- (iv) the transform kills at least one disagreement.
      have hsub : (Finset.univ.filter fun i => z i ≠ y' i)
          ⊆ Finset.univ.filter fun i => z i ≠ y i := by
        intro i hi
        obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
        have hij : i ≠ j := by
          rintro rfl
          exact absurd heq hzj.ne
        have hil : i ≠ l := by
          rintro rfl
          exact absurd heq hlS.ne'
        exact hine (by rw [hy'i i hij hil]; exact heq)
      have hwitness : ∃ w ∈ Finset.univ.filter fun i => z i ≠ y i,
          w ∉ Finset.univ.filter fun i => z i ≠ y' i := by
        rcases min_choice (y j - z j) (z l - y l) with hmin | hmin
        · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
          have hj' : y' j = z j := by
            rw [hy'j, hδdef, hmin]
            ring
          simp [hj']
        · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
          have hl' : y' l = z l := by
            rw [hy'l, hδdef, hmin]
            ring
          simp [hl']
      have hcard' : (Finset.univ.filter fun i => z i ≠ y' i).card ≤ d := by
        have hlt := Finset.card_lt_card
          ((Finset.ssubset_iff_of_subset hsub).mpr hwitness)
        omega
      -- (v) one descent step does not increase the gauge; recurse.
      have hstep : Φ y' ≤ Φ y := by
        rw [hcomb]
        calc Φ ((1 - c₂) • y + c₂ • (y ∘ Equiv.swap j l))
            ≤ Φ ((1 - c₂) • y)
              + Φ (c₂ • (y ∘ Equiv.swap j l)) :=
              Φ.add_le _ _
          _ = (1 - c₂) * Φ y + c₂ * Φ y := by
              rw [Φ.real_smul, Φ.real_smul,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c₂),
                abs_of_nonneg hc₂pos.le, Φ.perm]
          _ = Φ y := by ring
      exact le_trans (ih y' hcard' hy'0 hpre') hstep
  exact H _ y le_rfl hy0 hpre


/-- Every finite symmetric gauge is monotone under weak majorization. -/
theorem mono_weaklyMajorized {x y : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x y) : Φ x ≤ Φ y :=
  Φ.le_of_prefixSum_le h.left_antitone h.left_nonneg h.right_nonneg h.prefix_le

end FiniteSymmetricGauge

namespace FiniteVector

variable {n m : ℕ}

/-- The finite real `ℓᵖ` gauge. -/
noncomputable def lpGauge (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

theorem lpGauge_nonneg (p : ℝ) (x : Fin n → ℝ) :
    0 ≤ lpGauge p x := by
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _

@[simp] theorem lpGauge_zero {p : ℝ} (hp : 0 < p) :
    lpGauge p (0 : Fin n → ℝ) = 0 := by
  simp [lpGauge, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]

/-- The finite `ℓᵖ` gauge vanishes exactly on the zero vector. -/
theorem lpGauge_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : Fin n → ℝ) :
    lpGauge p x = 0 ↔ x = 0 := by
  have hsum0 : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [lpGauge, Real.rpow_eq_zero_iff_of_nonneg hsum0]
  constructor
  · rintro ⟨hsum, -⟩
    funext i
    have hi : |x i| ^ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) _)).mp hsum
          i (Finset.mem_univ i)
    have habs : |x i| = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg (x i))).mp hi).1
    exact abs_eq_zero.mp habs
  · rintro rfl
    constructor
    · simp [Real.zero_rpow hp.ne']
    · exact one_div_ne_zero hp.ne'

/-- Positive homogeneity of the finite `ℓᵖ` gauge. -/
theorem lpGauge_smul {p : ℝ} (hp : 0 < p) (c : ℝ) (x : Fin n → ℝ) :
    lpGauge p (c • x) = |c| * lpGauge p x := by
  by_cases hc : c = 0
  · subst c
    simp [lpGauge_zero (n := n) hp]
  have habspos : 0 < |c| := abs_pos.mpr hc
  have hsum : (∑ i, |(c • x) i| ^ p) =
      |c| ^ p * ∑ i, |x i| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow]
    exacts [abs_nonneg c, abs_nonneg (x i)]
  unfold lpGauge
  rw [hsum, Real.mul_rpow]
  · rw [← Real.rpow_mul (abs_nonneg c)]
    have hpinv : p * (1 / p) = 1 := by
      field_simp
    rw [hpinv, Real.rpow_one]
  · exact Real.rpow_nonneg (abs_nonneg c) p
  · exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- Permutation invariance of the finite `ℓᵖ` gauge. -/
theorem lpGauge_perm (p : ℝ) (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    lpGauge p (x ∘ π) = lpGauge p x := by
  unfold lpGauge
  congr 1
  exact Equiv.sum_comp π (fun i => |x i| ^ p)

/-- A single coordinate sign flip does not change the finite `ℓᵖ` gauge. -/
theorem lpGauge_neg_single (p : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    lpGauge p (Function.update x j (-(x j))) = lpGauge p x := by
  unfold lpGauge
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [Function.update_of_ne hij]

/-- Finite-dimensional Minkowski inequality. -/
theorem lpGauge_add_le {p : ℝ} (hp : 1 ≤ p) (x y : Fin n → ℝ) :
    lpGauge p (x + y) ≤ lpGauge p x + lpGauge p y := by
  simpa [lpGauge] using Real.Lp_add_le Finset.univ x y hp

/-- The `ℓᵖ` gauge as a finite symmetric gauge. -/
noncomputable def lpSymmetricGauge (p : ℝ) (hp : 1 ≤ p) :
    FiniteSymmetricGauge n where
  toFun := lpGauge p
  add_le' := lpGauge_add_le hp
  real_smul' := lpGauge_smul (zero_lt_one.trans_le hp)
  perm' := lpGauge_perm p
  neg_single' := lpGauge_neg_single p

/-- `ℓᵖ` gauge monotonicity under weak majorization. -/
theorem lpGauge_mono_weaklyMajorized {p : ℝ} (hp : 1 ≤ p)
    {x y : Fin n → ℝ} (h : WeaklyMajorized x y) :
    lpGauge p x ≤ lpGauge p y :=
  (lpSymmetricGauge (n := n) p hp).mono_weaklyMajorized h

/-- Coordinatewise monotonicity of the `ℓᵖ` gauge on nonnegative vectors. -/
theorem lpGauge_mono {p : ℝ} (hp : 1 ≤ p) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    lpGauge p x ≤ lpGauge p y :=
  (lpSymmetricGauge (n := n) p hp).mono hx0 hxy

/-- Right zero-padding does not change the finite `ℓᵖ` gauge. -/
theorem lpGauge_zeroPadRight (p : ℝ) (x : Fin n → ℝ) :
    lpGauge p (zeroPadRight (m := m) x) = lpGauge p x := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- the outer exponent `1 / 0` is zero, so both gauges collapse to `1`
    simp [lpGauge]
  · unfold lpGauge zeroPadRight
    rw [Fin.sum_univ_add]
    simp [Real.zero_rpow hp]

/-- The finite `ℓ∞` gauge. -/
noncomputable def linftyGauge (x : Fin n → ℝ) : ℝ :=
  ⨆ i, |x i|

theorem linftyGauge_nonneg (x : Fin n → ℝ) : 0 ≤ linftyGauge x := by
  rcases n with _ | n
  · simp [linftyGauge]
  · exact (abs_nonneg (x 0)).trans
      (le_ciSup (Finite.bddAbove_range (fun j : Fin (n + 1) => |x j|)) 0)

@[simp] theorem linftyGauge_zero :
    linftyGauge (0 : Fin n → ℝ) = 0 := by
  simp [linftyGauge]

/-- Coordinatewise domination of absolute values implies `ℓ∞` domination. -/
theorem linftyGauge_mono {x y : Fin n → ℝ}
    (hxy : ∀ i, |x i| ≤ |y i|) : linftyGauge x ≤ linftyGauge y := by
  unfold linftyGauge
  exact ciSup_mono (Finite.bddAbove_range (fun i => |y i|)) hxy

/-- Triangle inequality for the finite `ℓ∞` gauge. -/
theorem linftyGauge_add_le (x y : Fin n → ℝ) :
    linftyGauge (x + y) ≤ linftyGauge x + linftyGauge y := by
  -- `ciSup_le` needs a nonempty index type; the empty gauge is zero
  rcases n with _ | n
  · simp [linftyGauge]
  unfold linftyGauge
  refine ciSup_le fun i => ?_
  exact (abs_add_le (x i) (y i)).trans
    (add_le_add (le_ciSup (Finite.bddAbove_range (fun j => |x j|)) i)
      (le_ciSup (Finite.bddAbove_range (fun j => |y j|)) i))

/-- Positive homogeneity of the finite `ℓ∞` gauge. -/
theorem linftyGauge_smul (c : ℝ) (x : Fin n → ℝ) :
    linftyGauge (c • x) = |c| * linftyGauge x := by
  unfold linftyGauge
  -- `Real.mul_iSup_of_nonneg` is already total in `c`, including `c = 0`
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  apply congrArg iSup
  funext i
  simp [abs_mul, Pi.smul_apply, smul_eq_mul]

/-- Permutation invariance of the finite `ℓ∞` gauge. -/
theorem linftyGauge_perm (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    linftyGauge (x ∘ π) = linftyGauge x := by
  rcases n with _ | n
  · simp [linftyGauge]
  unfold linftyGauge
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    exact le_ciSup (Finite.bddAbove_range (fun j => |x j|)) (π i)
  · refine ciSup_le fun i => ?_
    simpa using le_ciSup (Finite.bddAbove_range (fun j => |x (π j)|)) (π.symm i)

/-- A single sign flip does not change the finite `ℓ∞` gauge. -/
theorem linftyGauge_neg_single (x : Fin n → ℝ) (j : Fin n) :
    linftyGauge (Function.update x j (-(x j))) = linftyGauge x := by
  unfold linftyGauge
  congr 1
  funext i
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Function.update_of_ne hij]

/-- The `ℓ∞` gauge as a finite symmetric gauge. -/
noncomputable def linftySymmetricGauge : FiniteSymmetricGauge n where
  toFun := linftyGauge
  add_le' := linftyGauge_add_le
  real_smul' := linftyGauge_smul
  perm' := linftyGauge_perm
  neg_single' := linftyGauge_neg_single

/-- `ℓ∞` gauge monotonicity under weak majorization. -/
theorem linftyGauge_mono_weaklyMajorized {x y : Fin n → ℝ}
    (h : WeaklyMajorized x y) : linftyGauge x ≤ linftyGauge y :=
  (linftySymmetricGauge (n := n)).mono_weaklyMajorized h

/-- Right zero-padding does not change the finite `ℓ∞` gauge. -/
theorem linftyGauge_zeroPadRight (x : Fin n → ℝ) :
    linftyGauge (zeroPadRight (m := m) x) = linftyGauge x := by
  rcases n with _ | n
  · -- nothing to pad: the padded vector is identically zero
    have hz : zeroPadRight (m := m) x = 0 := by
      funext i
      simp [zeroPadRight]
    rw [hz]
    simp [linftyGauge]
  haveI : Nonempty (Fin (n + 1 + m)) := ⟨⟨0, by omega⟩⟩
  apply le_antisymm
  · unfold linftyGauge
    refine ciSup_le fun i => ?_
    refine Fin.addCases (motive := fun i =>
      |zeroPadRight (m := m) x i| ≤ ⨆ q, |x q|) ?_ ?_ i
    · intro j
      rw [zeroPadRight_left]
      exact le_ciSup (Finite.bddAbove_range (fun q => |x q|)) j
    · intro j
      rw [zeroPadRight_right, abs_zero]
      exact linftyGauge_nonneg x
  · unfold linftyGauge
    refine ciSup_le fun i => ?_
    simpa using le_ciSup
      (Finite.bddAbove_range (fun q => |zeroPadRight (m := m) x q|))
      (Fin.castAdd m i)

end FiniteVector
end TauCeti
