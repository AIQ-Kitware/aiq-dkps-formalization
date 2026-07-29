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

end HilbertSchmidt
end TauCeti
