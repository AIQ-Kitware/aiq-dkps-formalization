/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic
public import ForTauCeti.Analysis.Convex.Majorization

/-!
# Finite-vector bridges for Tau Ceti symmetric gauges

The symmetric-gauge structure and its sequence-level laws are provided by Tau Ceti. This module
retains only the DKPS bridge from real finite vectors to that canonical gauge. It lets the existing
finite weak-majorization theorem act on a `TauCeti.SymmetricGauge` without duplicating Tau Ceti's
sequence or extension theory.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti
namespace SymmetricGauge

/-- The componentwise absolute value of a finite real vector, embedded as a finitely supported
nonnegative sequence on `ℕ`. -/
@[expose]
noncomputable def ofFin {n : ℕ} (x : Fin n → ℝ) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range n)
    (fun i => if h : i < n then Real.nnabs (x ⟨i, h⟩) else 0)
    (by
      intro i hi
      by_cases h : i < n
      · exact Finset.mem_range.mpr h
      · simp [h] at hi)

@[simp]
theorem ofFin_apply {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : i < n) :
    (ofFin x) i = Real.nnabs (x ⟨i, h⟩) := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dite_eq_left]

@[simp]
theorem ofFin_apply_of_le {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : ¬ i < n) :
    (ofFin x) i = 0 := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dite_eq_right, not_false_iff]

theorem ofFin_le_ofFin {n : ℕ} {x y : Fin n → ℝ}
    (h : ∀ i, |x i| ≤ |y i|) : ofFin x ≤ ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply x hi, ofFin_apply y hi, ← NNReal.coe_le_coe,
      Real.coe_nnabs, Real.coe_nnabs]
    exact h ⟨i, hi⟩
  · simp [ofFin_apply_of_le, hi]

theorem ofFin_add_le {n : ℕ} (x y : Fin n → ℝ) :
    ofFin (x + y) ≤ ofFin x + ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply (x + y) hi, Finsupp.add_apply, ofFin_apply x hi,
      ofFin_apply y hi, ← NNReal.coe_le_coe]
    simpa using abs_add_le (x ⟨i, hi⟩) (y ⟨i, hi⟩)
  · simp [ofFin_apply_of_le, hi]

theorem ofFin_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    ofFin (c • x) = Real.nnabs c • ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply (c • x) hi, Finsupp.smul_apply, ofFin_apply x hi, smul_eq_mul]
    simp [map_mul]
  · simp [ofFin_apply_of_le, hi]

theorem ofFin_update_neg {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    ofFin (Function.update x j (-x j)) = ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply _ hi, ofFin_apply x hi]
    by_cases hij : (⟨i, hi⟩ : Fin n) = j
    · rw [hij, Function.update_self]
      simp
    · rw [Function.update_of_ne hij]
  · simp [ofFin_apply_of_le, hi]

/-- Extend a permutation of the first `n` coordinates by the identity on `ℕ`. -/
def natPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (π ⟨i, h⟩ : ℕ) else i
  invFun i := if h : i < n then (π.symm ⟨i, h⟩ : ℕ) else i
  left_inv i := by
    by_cases h : i < n
    · simp only [dite_eq_left h, dite_eq_left (π ⟨i, h⟩).isLt]
      simp
    · simp [h]
  right_inv i := by
    by_cases h : i < n
    · simp only [dite_eq_left h, dite_eq_left (π.symm ⟨i, h⟩).isLt]
      simp
    · simp [h]

@[simp]
theorem natPerm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    natPerm π i = (π ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

@[simp]
theorem natPerm_symm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    (natPerm π).symm i = (π.symm ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

theorem ofFin_comp_perm {n : ℕ} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ofFin (x ∘ π) = Finsupp.equivMapDomain (natPerm π).symm (ofFin x) := by
  ext i
  rw [Finsupp.equivMapDomain_apply]
  by_cases hi : i < n
  · have h2 : ((natPerm π).symm).symm i = (π ⟨i, hi⟩ : ℕ) := by simp [natPerm, hi]
    rw [ofFin_apply _ hi, h2, ofFin_apply x (π ⟨i, hi⟩).isLt]
    rfl
  · have h2 : ((natPerm π).symm).symm i = i := by simp [natPerm, hi]
    rw [h2, ofFin_apply_of_le _ hi, ofFin_apply_of_le _ hi]

/-- Restrict a sequence gauge to real vectors by applying it to coordinatewise absolute values. -/
noncomputable def toFiniteSymmetricGauge (Φ : SymmetricGauge) (n : ℕ) :
    FiniteSymmetricGauge n where
  toFun x := (Φ (ofFin x) : ℝ)
  add_le' x y := by
    have h : Φ (ofFin (x + y)) ≤ Φ (ofFin x) + Φ (ofFin y) :=
      (Φ.monotone (ofFin_add_le x y)).trans (Φ.map_add_le _ _)
    exact_mod_cast h
  real_smul' c x := by
    rw [ofFin_smul, Φ.map_smul]
    simp [Real.coe_nnabs]
  perm' x π := by rw [ofFin_comp_perm, Φ.map_equivMapDomain]
  neg_single' x j := by rw [ofFin_update_neg]

theorem le_of_prefixSum_le (Φ : SymmetricGauge) {n : ℕ} {z y : Fin n → ℝ}
    (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, y i) :
    Φ (ofFin z) ≤ Φ (ofFin y) := by
  have h := (Φ.toFiniteSymmetricGauge n).le_of_prefixSum_le hz_anti hz0 hy0 hpre
  exact_mod_cast h

theorem mono_weaklyMajorized (Φ : SymmetricGauge) {n : ℕ} {x y : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x y) : Φ (ofFin x) ≤ Φ (ofFin y) := by
  have h' := (Φ.toFiniteSymmetricGauge n).mono_weaklyMajorized h
  exact_mod_cast h'

/-- For a nonnegative real sequence, the extension is the supremum of its finite views.
This connects Tau Ceti's canonical indicator truncations to DKPS's `Fin`-indexed presentation. -/
theorem extend_eq_iSup_ofFin (Φ : SymmetricGauge) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Φ.extend (fun n => ENNReal.ofReal (a n))
      = ⨆ k : ℕ, ((Φ (ofFin (fun i : Fin k => a i)) : ℝ≥0) : ℝ≥0∞) := by
  have hseq : (fun n => ENNReal.ofReal (a n)) = fun n => ((a n).toNNReal : ℝ≥0∞) := by
    funext n
    exact (ENNReal.ofNNReal_toNNReal (a n)).symm
  rw [hseq, Φ.extend_coe_eq_iSup_indicator]
  refine iSup_congr fun k => ?_
  congr 1
  have hind : Finsupp.indicator (Finset.range k) (fun n _ => (a n).toNNReal) =
      ofFin (fun i : Fin k => a i) := by
    ext n
    by_cases hn : n < k
    · simp [Finsupp.indicator_apply, hn, ofFin_apply, Real.nnabs_of_nonneg (ha n)]
    · simp [Finsupp.indicator_apply, hn, ofFin_apply_of_le]
  rw [hind]

end SymmetricGauge
end TauCeti
