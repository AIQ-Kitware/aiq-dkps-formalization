/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.MeanInequalities
public import TauCeti.Analysis.Convex.Majorization
public import Mathlib.Data.Fintype.Order


/-!
# The finite `ℓᵖ` gauges

The real power-sum formula is retained for all real exponents, including the
zero exponent and the quasi-norm range `0 < p < 1`. For positive exponents it
agrees with the native `PiLp` norm. Standard norm and symmetric-gauge laws
are consumed directly from Mathlib and Tau Ceti.

The remaining zero-padding facts preserve these broader exponent formulas
and compare native finite sup norms across dimensions.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Normed.FiniteLpGauge`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `a8d4ea3`.  The majorization layer was split out to
  `ForTauCeti.Analysis.Convex.Majorization` on 2026-07-28, when the T-transform descent it
  contained was found to be one of three copies in this library.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace FiniteVector

variable {n m : ℕ}

/-- The finite real `ℓᵖ` gauge. -/
@[expose]
noncomputable def lpGauge (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The `ℓᵖ` gauge is nonnegative. -/
theorem lpGauge_nonneg (p : ℝ) (x : Fin n → ℝ) :
    0 ≤ lpGauge p x := by
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _

/-- The `ℓᵖ` gauge of zero is zero. -/
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

/-- The positive-exponent formula is the native finite `Lᵖ` norm, also for `p < 1`. -/
theorem lpGauge_eq_norm {p : ℝ} (hp : 0 < p) (x : Fin n → ℝ) :
    lpGauge p x =
      ‖(WithLp.toLp (ENNReal.ofReal p) x : PiLp (ENNReal.ofReal p) fun _ : Fin n => ℝ)‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, lpGauge]

/-- Right zero-padding does not change the finite `ℓᵖ` gauge. -/
theorem lpGauge_append_zero (p : ℝ) (x : Fin n → ℝ) :
    lpGauge p (Fin.append x (0 : Fin m → ℝ)) = lpGauge p x := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- the outer exponent `1 / 0` is zero, so both gauges collapse to `1`
    simp [lpGauge]
  · unfold lpGauge
    rw [Fin.sum_univ_add]
    simp [Real.zero_rpow hp]

/-- Appending zeros preserves the native finite sup norm, including dimension zero. -/
theorem norm_append_zero (x : Fin n → ℝ) :
    ‖Fin.append x (0 : Fin m → ℝ)‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
    intro i
    induction i using Fin.addCases with
    | left i => simpa using norm_le_pi_norm x i
    | right i => simp
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    simpa using norm_le_pi_norm (Fin.append x (0 : Fin m → ℝ)) (Fin.castAdd m i)

end FiniteVector
end TauCeti
