/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidtEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert–Schmidt operators are an `ℓ²` space of columns

Fix a Hilbert basis `b` of `F`.  A bounded operator `T : F →L[𝕜] E` is
Hilbert–Schmidt exactly when its column family `i ↦ T (b i)` is square-summable,
and the Hilbert–Schmidt inner product is the `ℓ²` inner product of the columns.

## Why this file exists

Spectra realises the Hilbert–Schmidt operators as a Hilbert *tensor product* and
builds that space from scratch; the resulting donor closure was measured at
21,581 lines.  None of it is needed.  Mathlib already has

* `lp.instInnerProductSpace` — the inner product on `lp G 2`, and
* completeness of `lp G p` for `1 ≤ p`,

so identifying the Hilbert–Schmidt operators with `lp (fun _ : ι => E) 2` gives
the inner product and completeness — the expensive half of any from-scratch
development — for free, and leaves only the column bijection to prove.

This module supplies the membership half of that identification.  The bijection
itself is the content of
`DavisKahan/Interop/Spectra/HilbertSchmidtColumnExpansion.lean`, whose eleven
`mathAhead_*` declarations are DKPS-authored and are re-based onto `lp` rather
than re-proved.

## Provenance

*New.*  The predicate and energy come from
`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtEnergy.lean`; the target
`lp` space is Mathlib's.  Spectra is credited for the theorem selection — its
`HilbertSchmidtTensor.Space` is the object being replaced — and for nothing else,
since the construction is a different one.
-/

open scoped ENNReal NNReal
open ContinuousLinearMap

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The family of columns of `T` in the Hilbert basis `b`. -/
noncomputable def columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) : ι → E := fun i => T (b i)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem columns_apply (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) (i : ι) :
    columns b T i = T (b i) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem columns_zero (b : HilbertBasis ι 𝕜 F) :
    columns b (0 : F →L[𝕜] E) = 0 := by
  funext i; simp [columns]

omit [CompleteSpace E] [CompleteSpace F] in
theorem columns_add (b : HilbertBasis ι 𝕜 F) (S T : F →L[𝕜] E) :
    columns b (S + T) = columns b S + columns b T := by
  funext i; simp [columns]

omit [CompleteSpace E] [CompleteSpace F] in
theorem columns_smul (b : HilbertBasis ι 𝕜 F) (c : 𝕜) (T : F →L[𝕜] E) :
    columns b (c • T) = c • columns b T := by
  funext i; simp [columns]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Hilbert–Schmidt membership is `ℓ²` membership of the columns.** -/
theorem memLp_columns_iff (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    Memℓp (columns b T) 2 ↔ T.hilbertSchmidtEnergy b ≠ ⊤ := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
    ContinuousLinearMap.hilbertSchmidtEnergy_def]
  have hpow : ∀ i : ι, ‖T (b i)‖ₑ ^ 2 = ((‖T (b i)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    intro i
    rw [enorm_eq_nnnorm, ENNReal.coe_pow]
  rw [tsum_congr hpow, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  refine summable_congr fun i => ?_
  rw [NNReal.coe_pow, coe_nnnorm]
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp]
  exact Real.rpow_natCast _ 2

/-! ## The inverse direction: every square-summable column family is an operator -/

section OfLp

variable (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The column series of an `ℓ²` family is absolutely summable at every vector:
Cauchy--Schwarz against the basis coefficients, which are themselves `ℓ²`. -/
theorem summable_norm_columnSeries (x : F) :
    Summable fun i => ‖(b.repr x i) • f i‖ := by
  have hcoef : Summable fun i => ‖b.repr x i‖ ^ 2 := by
    have := lp.memℓp (b.repr x)
    have h2 := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp this
    refine h2.congr fun i => ?_
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp]
    exact Real.rpow_natCast _ 2
  have hcol : Summable fun i => ‖f i‖ ^ 2 := by
    have h2 := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp f)
    refine h2.congr fun i => ?_
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp]
    exact Real.rpow_natCast _ 2
  -- `ab ≤ (a² + b²)/2` avoids invoking Hölder for the one case that needs it
  have hdom : Summable fun i => (‖b.repr x i‖ ^ 2 + ‖f i‖ ^ 2) / 2 :=
    (hcoef.add hcol).div_const 2
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hdom
  rw [norm_smul]
  nlinarith [sq_nonneg (‖b.repr x i‖ - ‖f i‖), norm_nonneg (b.repr x i), norm_nonneg (f i)]

/-- The squared norms of an `ℓ²` family are summable. -/
theorem summable_sq {G : Type*} [NormedAddCommGroup G]
    (g : lp (fun _ : ι => G) 2) : Summable fun i => ‖g i‖ ^ 2 := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp g)
  refine h.congr fun i => ?_
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp]
  exact Real.rpow_natCast _ 2

/-- The square-sum of an `ℓ²` family is the square of its norm. -/
theorem tsum_sq_eq_norm_sq {G : Type*} [NormedAddCommGroup G]
    (g : lp (fun _ : ι => G) 2) : ∑' i, ‖g i‖ ^ 2 = ‖g‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) g
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp] at h
  rw [← Real.rpow_natCast ‖g‖ 2, h]
  exact tsum_congr fun i => (Real.rpow_natCast _ 2).symm

/-- **The operator with prescribed columns.**  The defining series converges
absolutely by `summable_norm_columnSeries`; the bound is Cauchy--Schwarz in the
rescaled form `ab ≤ (s a² + b²/s)/2`, sharp at `s = ‖f‖/‖x‖`. -/
noncomputable def ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    F →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, (b.repr x i) • f i
      map_add' := fun x y => by
        have hx := (summable_norm_columnSeries b f x).of_norm
        have hy := (summable_norm_columnSeries b f y).of_norm
        rw [← Summable.tsum_add hx hy]
        exact tsum_congr fun i => by
          rw [map_add, lp.coeFn_add, Pi.add_apply, add_smul]
      map_smul' := fun c x => by
        have hx := (summable_norm_columnSeries b f x).of_norm
        rw [RingHom.id_apply, ← Summable.tsum_const_smul c hx]
        exact tsum_congr fun i => by
          rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_assoc] }
    ‖f‖ (by
      intro x
      have hsum := summable_norm_columnSeries b f x
      refine (norm_tsum_le_tsum_norm hsum).trans ?_
      have hcoef : ∑' i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [tsum_sq_eq_norm_sq, b.repr.norm_map]
      have hcol : ∑' i, ‖f i‖ ^ 2 = ‖f‖ ^ 2 := tsum_sq_eq_norm_sq f
      have hsq1 : Summable fun i => ‖b.repr x i‖ ^ 2 := summable_sq _
      have hsq2 : Summable fun i => ‖f i‖ ^ 2 := summable_sq f
      rcases eq_or_lt_of_le (norm_nonneg f) with hf | hf
      · have hf0 : f = 0 := norm_eq_zero.mp hf.symm
        simp [hf0]
      rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
      · have hxz : x = 0 := norm_eq_zero.mp hx0.symm
        simp [hxz]
      set s : ℝ := ‖f‖ / ‖x‖ with hs
      have hspos : 0 < s := div_pos hf hx0
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hterm : ∀ i, ‖(b.repr x i) • f i‖
          ≤ (s * ‖b.repr x i‖ ^ 2 + ‖f i‖ ^ 2 / s) / 2 := by
        intro i
        rw [norm_smul, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
        have hkey : 0 ≤ (s * ‖b.repr x i‖ - ‖f i‖) ^ 2 := sq_nonneg _
        have hexp : s * ‖b.repr x i‖ ^ 2 + ‖f i‖ ^ 2 / s
            - ‖b.repr x i‖ * ‖f i‖ * 2
            = (s * ‖b.repr x i‖ - ‖f i‖) ^ 2 / s := by
          field_simp
          ring
        rw [hexp]
        positivity
      have hdom : Summable fun i =>
          (s * ‖b.repr x i‖ ^ 2 + ‖f i‖ ^ 2 / s) / 2 :=
        (((hsq1.mul_left s).add (hsq2.div_const s)).div_const 2)
      refine (Summable.tsum_le_tsum hterm hsum hdom).trans ?_
      rw [tsum_div_const, Summable.tsum_add (hsq1.mul_left s) (hsq2.div_const s),
        Summable.tsum_mul_left, tsum_div_const, hcoef, hcol, hs]
      · field_simp
        norm_num
      · exact hsq1)

end OfLp

end HilbertSchmidt
end TauCeti
