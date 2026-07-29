/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.OperatorIdeal.Family.KyFan

/-!
# The trace-class ideal

The **nuclear norm** of a bounded operator is the sum of all its approximation numbers,

```
T.nuclearENorm = ∑' n, ENNReal.ofReal (T.approximationNumber n),
```

and `T` is **trace class** when that is finite.  Like the Hilbert--Schmidt norm it is valued
in `ℝ≥0∞`, so it is defined for every bounded operator and is `∞` exactly off the ideal.

## Why this is now possible

The nuclear norm is the supremum of the Ky Fan gauges, so its triangle inequality *is* the
Ky Fan triangle inequality, taken to the limit.  That inequality is the one whose only
proof in this repository used to run through `vendor/Spectra`'s projection-valued measures;
since 2026-07-28 it is `ContinuousLinearMap.kyFanGauge_add_le`, proved from Mathlib's
continuous functional calculus, and the trace-class ideal follows immediately.

Everything is stated over `ℂ`, which is where the Ky Fan triangle inequality lives.

## Main results

* `ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge`: the nuclear norm is the supremum of
  the Ky Fan gauges;
* `ContinuousLinearMap.nuclearENorm_add_le`, `_smul`, `_adjoint`, `_comp_le`: the ideal laws;
* `ContinuousLinearMap.IsTraceClass` and
  `ContinuousLinearMap.isTraceClass_iff_summable`: the membership predicate and its concrete
  form;
* `TauCeti.traceClassIdealFamily`: the resulting symmetric operator ideal family.

Unlike the Ky Fan families, whose carriers are provably `⊤`, this one need not be all of
`E →L[ℂ] F`, so it is the first family here whose `ℝ≥0∞` gauge is expected to take the value
`∞`.  That it actually does — that some bounded operator is not trace class — is not proved
here; it needs an infinite orthonormal family to exhibit one.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal NNReal InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

universe v

section Basic

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The **nuclear norm**: the sum of all approximation numbers, valued in `ℝ≥0∞` and so
defined for every bounded operator. -/
noncomputable def nuclearENorm (T : E →L[ℂ] F) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n)

/-- The nuclear norm is the supremum of the Ky Fan gauges.  Every property of it below is
read off this identity. -/
theorem nuclearENorm_eq_iSup_kyFanGauge (T : E →L[ℂ] F) :
    T.nuclearENorm = ⨆ k : ℕ, ENNReal.ofReal (T.kyFanGauge k) := by
  rw [nuclearENorm, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun k => ?_
  rw [kyFanGauge, ENNReal.ofReal_sum_of_nonneg]
  exact fun n _ => T.approximationNumber_nonneg n

/-- Every Ky Fan gauge is bounded by the nuclear norm, the latter being their supremum. -/
theorem ofReal_kyFanGauge_le_nuclearENorm (T : E →L[ℂ] F) (k : ℕ) :
    ENNReal.ofReal (T.kyFanGauge k) ≤ T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  exact le_iSup (fun j : ℕ => ENNReal.ofReal (T.kyFanGauge j)) k

@[simp] theorem nuclearENorm_zero : (0 : E →L[ℂ] F).nuclearENorm = 0 := by
  simp [nuclearENorm]

end Basic

section Complete

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The triangle inequality**: the Ky Fan inequality in the limit. -/
theorem nuclearENorm_add_le (S T : E →L[ℂ] F) :
    (S + T).nuclearENorm ≤ S.nuclearENorm + T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  refine iSup_le fun k => ?_
  calc ENNReal.ofReal ((S + T).kyFanGauge k)
      ≤ ENNReal.ofReal (S.kyFanGauge k + T.kyFanGauge k) :=
        ENNReal.ofReal_le_ofReal (S.kyFanGauge_add_le T k)
    _ = ENNReal.ofReal (S.kyFanGauge k) + ENNReal.ofReal (T.kyFanGauge k) :=
        ENNReal.ofReal_add (S.kyFanGauge_nonneg k) (T.kyFanGauge_nonneg k)
    _ ≤ S.nuclearENorm + T.nuclearENorm :=
        add_le_add (S.ofReal_kyFanGauge_le_nuclearENorm k)
          (T.ofReal_kyFanGauge_le_nuclearENorm k)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The nuclear norm is absolutely homogeneous. -/
theorem nuclearENorm_smul (c : ℂ) (T : E →L[ℂ] F) :
    (c • T).nuclearENorm = ‖c‖ₑ * T.nuclearENorm := by
  simp only [nuclearENorm, approximationNumber_smul,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  exact ENNReal.tsum_mul_left

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The nuclear norm dominates the operator norm**, being its zeroth term. -/
theorem enorm_le_nuclearENorm (T : E →L[ℂ] F) : ‖T‖ₑ ≤ T.nuclearENorm := by
  rw [← ofReal_norm, ← T.approximationNumber_index_zero]
  exact ENNReal.le_tsum 0

/-- The nuclear norm is adjoint-invariant, since the approximation numbers are.  This is the
property that makes the trace-class family *symmetric* rather than merely an ideal. -/
theorem nuclearENorm_adjoint (T : E →L[ℂ] F) : T.adjoint.nuclearENorm = T.nuclearENorm := by
  simp only [nuclearENorm, approximationNumber_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The two-sided ideal bound.** -/
theorem nuclearENorm_comp_le {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : F →L[ℂ] G) (T : E →L[ℂ] F) (R : H →L[ℂ] E) :
    (L ∘L T ∘L R).nuclearENorm ≤ ‖L‖ₑ * T.nuclearENorm * ‖R‖ₑ := by
  calc (L ∘L T ∘L R).nuclearENorm
      ≤ ∑' n : ℕ, ENNReal.ofReal (‖L‖ * T.approximationNumber n * ‖R‖) :=
        ENNReal.tsum_le_tsum fun n =>
          ENNReal.ofReal_le_ofReal (approximationNumber_comp_comp_le L T R n)
    _ = ‖L‖ₑ * T.nuclearENorm * ‖R‖ₑ := by
        simp only [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (T.approximationNumber_nonneg _)),
          ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
        rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is **trace class** when its nuclear norm is finite. -/
def IsTraceClass (T : E →L[ℂ] F) : Prop := T.nuclearENorm ≠ ∞

omit [CompleteSpace E] [CompleteSpace F] in
/-- Concretely, `T` is trace class exactly when its approximation numbers are summable. -/
theorem isTraceClass_iff_summable (T : E →L[ℂ] F) :
    T.IsTraceClass ↔ Summable fun n => T.approximationNumber n := by
  rw [IsTraceClass, nuclearENorm]
  have hcoe : (fun n : ℕ => ENNReal.ofReal (T.approximationNumber n))
      = fun n : ℕ => ((T.approximationNumber n).toNNReal : ℝ≥0∞) := rfl
  rw [hcoe, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  refine summable_congr fun n => ?_
  exact Real.coe_toNNReal _ (T.approximationNumber_nonneg n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- On a trace-class operator every Ky Fan gauge is bounded by the nuclear norm read as a
real number. -/
theorem kyFanGauge_le_toReal_nuclearENorm (T : E →L[ℂ] F) (hT : T.IsTraceClass) (k : ℕ) :
    T.kyFanGauge k ≤ T.nuclearENorm.toReal := by
  have h := T.ofReal_kyFanGauge_le_nuclearENorm k
  rw [← ENNReal.ofReal_toReal hT] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

end Complete

end ContinuousLinearMap

namespace TauCeti

universe v

open ContinuousLinearMap

/-- **The trace-class operator ideal.**

Its carrier is `ContinuousLinearMap.IsTraceClass` definitionally, which unlike the Ky Fan
carriers is not provably `⊤`. -/
noncomputable def traceClassIdealFamily : SymmetricOperatorIdealFamily.{0, v} ℂ where
  gauge A := A.nuclearENorm
  gauge_add_le A B := A.nuclearENorm_add_le B
  gauge_smul c A := nuclearENorm_smul c A
  enorm_le_gauge A := A.enorm_le_nuclearENorm
  gauge_comp_le L A R := nuclearENorm_comp_le L A R
  gauge_adjoint A := A.nuclearENorm_adjoint

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[simp] theorem gauge_traceClassIdealFamily (A : E →L[ℂ] F) :
    (traceClassIdealFamily.{v}).gauge A = A.nuclearENorm := rfl

/-- Membership in the trace-class ideal is exactly `IsTraceClass`; true by definition, but stated
so call sites need not unfold the family. -/
theorem mem_traceClassIdealFamily_carrier_iff (A : E →L[ℂ] F) :
    A ∈ (traceClassIdealFamily.{v}).toOperatorIdealFamily.carrier ↔ A.IsTraceClass :=
  Iff.rfl

end TauCeti
