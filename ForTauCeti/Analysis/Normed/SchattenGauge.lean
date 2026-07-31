/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import ForTauCeti.Analysis.Normed.SymmetricGauge
import Mathlib.Analysis.MeanInequalities

/-!
# The `ℓᵖ` symmetric gauge

`Φ_p a = (∑ aₙ ^ p) ^ (1 / p)` for `1 ≤ p`, as a `TauCeti.SymmetricGauge` on
finitely supported nonnegative sequences.  Feeding it to
`TauCeti.symmetricGaugeFamily` produces the Schatten-`p` operator ideal family.

* `TauCeti.schattenGaugeFun` — the underlying function;
* `TauCeti.schattenGauge` — the bundled gauge.

## Sums over a larger index set

The gauge is a sum over `a.support`, but its subadditivity compares three
sequences with three different supports.  `schattenGaugeFun_eq_sum_of_subset`
says the sum may be taken over any `Finset` containing the support — the extra
terms are `0 ^ p = 0`, which needs `p ≠ 0` — so all three can be moved to the
union of their supports before Minkowski applies.  That bookkeeping, rather than
the inequality, is the substance of `add_le`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written against the target signature in
  `ForTauCetiRoadmap/OperatorIdeals/Suggested.lean`.
* Roadmap topic: `OperatorIdeals`.
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

open scoped NNReal

namespace TauCeti

variable {p : ℝ}

/-- The underlying `ℓᵖ` gauge function on finitely supported nonnegative
sequences. -/
noncomputable def schattenGaugeFun (p : ℝ) (a : ℕ →₀ ℝ≥0) : ℝ≥0 :=
  (∑ i ∈ a.support, a i ^ p) ^ (1 / p)

/-- The defining sum may be taken over any finset containing the support: the
extra terms are `0 ^ p = 0`. -/
theorem schattenGaugeFun_eq_sum_of_subset (hp : 0 < p) (a : ℕ →₀ ℝ≥0)
    {s : Finset ℕ} (hs : a.support ⊆ s) :
    schattenGaugeFun p a = (∑ i ∈ s, a i ^ p) ^ (1 / p) := by
  unfold schattenGaugeFun
  rw [Finset.sum_subset hs (fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, NNReal.zero_rpow hp.ne'])]

/-- Positive homogeneity of the `ℓᵖ` gauge. -/
theorem schattenGaugeFun_smul (hp : 1 ≤ p) (c : ℝ≥0) (a : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (c • a) = c * schattenGaugeFun p a := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsub : (c • a).support ⊆ a.support := Finsupp.support_smul
  rw [schattenGaugeFun_eq_sum_of_subset hp0 _ hsub, schattenGaugeFun]
  have hterm : ∀ i ∈ a.support, (c • a) i ^ p = c ^ p * a i ^ p := by
    intro i _
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact NNReal.mul_rpow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_mul, mul_one_div, div_self hp0.ne', NNReal.rpow_one]

/-- **Minkowski.**  Subadditivity of the `ℓᵖ` gauge.

The inequality itself is `NNReal.Lp_add_le`; the work is moving three sums with
three different supports onto their union first. -/
theorem schattenGaugeFun_add_le (hp : 1 ≤ p) (a b : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (a + b) ≤ schattenGaugeFun p a + schattenGaugeFun p b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s : Finset ℕ := a.support ∪ b.support with hs
  have hab : (a + b).support ⊆ s := by
    intro i hi
    simpa [hs] using Finsupp.support_add hi
  have eab : schattenGaugeFun p (a + b) = (∑ i ∈ s, (a i + b i) ^ p) ^ (1 / p) := by
    rw [schattenGaugeFun_eq_sum_of_subset hp0 _ hab]
    rfl
  have ea : schattenGaugeFun p a = (∑ i ∈ s, a i ^ p) ^ (1 / p) :=
    schattenGaugeFun_eq_sum_of_subset hp0 a Finset.subset_union_left
  have eb : schattenGaugeFun p b = (∑ i ∈ s, b i ^ p) ^ (1 / p) :=
    schattenGaugeFun_eq_sum_of_subset hp0 b Finset.subset_union_right
  rw [eab, ea, eb]
  exact NNReal.Lp_add_le s (fun i => a i) (fun i => b i) hp

/-- Permutation invariance of the `ℓᵖ` gauge.

Relabelling the index set is a bijection of the support, so the sum is
unchanged; `Finset.sum_nbij'` states that with the two directions explicit. -/
theorem schattenGaugeFun_symm (_hp : 1 ≤ p) (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (Finsupp.equivMapDomain σ a) = schattenGaugeFun p a := by
  unfold schattenGaugeFun
  congr 1
  refine Finset.sum_nbij' (fun i => σ.symm i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply] at hi ⊢
    exact hi
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply] at hi ⊢
    simpa using hi
  · intro i _; simp
  · intro i _; simp
  · intro i _; simp [Finsupp.equivMapDomain_apply]

/-- Monotonicity of the `ℓᵖ` gauge in the termwise order. -/
theorem schattenGaugeFun_mono (hp : 1 ≤ p) {a b : ℕ →₀ ℝ≥0} (hab : a ≤ b) :
    schattenGaugeFun p a ≤ schattenGaugeFun p b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s : Finset ℕ := a.support ∪ b.support with hs
  rw [schattenGaugeFun_eq_sum_of_subset hp0 a Finset.subset_union_left,
    schattenGaugeFun_eq_sum_of_subset hp0 b Finset.subset_union_right]
  refine NNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact NNReal.rpow_le_rpow (hab i) hp0.le

/-- Normalization: a single unit coordinate has gauge one. -/
theorem schattenGaugeFun_normalized (hp : 1 ≤ p) :
    schattenGaugeFun p (Finsupp.single 0 (1 : ℝ≥0)) = 1 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold schattenGaugeFun
  rw [Finsupp.support_single (0 : ℕ) (one_ne_zero)]
  simp [NNReal.one_rpow]

/-- **The `ℓᵖ` symmetric gauge**, `Φ_p a = (∑ aₙ ^ p) ^ (1 / p)` for `1 ≤ p`.

Feeding this to `TauCeti.symmetricGaugeFamily` produces the Schatten-`p`
operator ideal family, which is what the roadmap's `schattenFamily` names. -/
noncomputable def schattenGauge (p : ℝ) (hp : 1 ≤ p) : SymmetricGauge where
  toFun := schattenGaugeFun p
  add_le := schattenGaugeFun_add_le hp
  smul := schattenGaugeFun_smul hp
  symm := fun σ a => schattenGaugeFun_symm hp σ a
  mono := fun _ _ hab => schattenGaugeFun_mono hp hab
  normalized := schattenGaugeFun_normalized hp

/-- The bundled gauge applies as `schattenGaugeFun`. -/
@[simp]
theorem schattenGauge_apply (hp : 1 ≤ p) (a : ℕ →₀ ℝ≥0) :
    schattenGauge p hp a = schattenGaugeFun p a := rfl

end TauCeti
