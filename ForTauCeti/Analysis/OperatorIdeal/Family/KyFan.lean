/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
import ForTauCeti.Analysis.OperatorIdeal.Family.Basic

/-!
# The Ky Fan operator ideals

For each `k > 0` the `k`th Ky Fan gauge is a norm on the ideal it defines — which, `k` being
finite, is all of `E →L[ℂ] F` — and so gives a `TauCeti.SymmetricOperatorIdealFamily`.

## The capability class is gone

`DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean` builds the same family
over a general `RCLike` field, but only under a `HasKyFanApproximationGaugeTriangle`
capability hypothesis, because the triangle inequality for the gauge was not available
there.  Over `ℂ` it now is — `ContinuousLinearMap.kyFanGauge_add_le` is unconditional — so
the family constructed here needs no capability class at all, and
`TauCeti.kyFanSymmetricIdealFamily_eq_kyFanIdealFamily` records that the two agree.

The real-scalar case still goes through the capability class, since its triangle inequality
is obtained by complexification.

## Completeness

The ideal is everything and its norm is *equivalent* to the operator norm,

```
‖A‖ ≤ A.kyFanGauge k ≤ k * ‖A‖   (for 0 < k),
```

so completeness is inherited from the bounded operators.  Both inequalities are used: the
first turns an ideal-norm Cauchy sequence into an operator-norm one, the second turns the
operator-norm limit back into an ideal-norm limit.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `kyFanSymmetricIdealFamily, gauge_kyFanSymmetricIdealFamily,`
  `gauge_kyFanSymmetricIdealFamily_ne_top, carrier_kyFanSymmetricIdealFamily,`
  `toReal_gauge_kyFanSymmetricIdealFamily, isComplete_kyFanSymmetricIdealFamily}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and specialised**.  The construction is the original one with
  the scalar field fixed to `ℂ` and the `HasKyFanApproximationGaugeTriangle` hypothesis
  discharged rather than assumed.  The declaration named in the original as its "intended
  destination" is this one.
* Spectra influence: **none**, as of the replacement of the min--max bridge on 2026-07-28.
-/

open scoped ENNReal InnerProductSpace

@[expose] public section

namespace TauCeti

universe v

open ContinuousLinearMap

/-- **The `k`th Ky Fan operator ideal**, as a symmetric family.

`hk : 0 < k` is needed for exactly one law, `enorm_le_gauge`: at `k = 0` the gauge is
identically `0`, which satisfies the other three but is not a norm. -/
noncomputable def kyFanIdealFamily (k : ℕ) (hk : 0 < k) :
    SymmetricOperatorIdealFamily.{0, v} ℂ where
  gauge A := ENNReal.ofReal (A.kyFanGauge k)
  gauge_add_le A B := by
    rw [← ENNReal.ofReal_add (A.kyFanGauge_nonneg k) (B.kyFanGauge_nonneg k)]
    exact ENNReal.ofReal_le_ofReal (A.kyFanGauge_add_le B k)
  gauge_smul c A := by
    rw [kyFanGauge_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  enorm_le_gauge A := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (A.opNorm_le_kyFanGauge hk)
  gauge_comp_le L A R := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg L),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (A.kyFanGauge_nonneg k))]
    exact ENNReal.ofReal_le_ofReal (kyFanGauge_comp_le L A R k)
  gauge_adjoint A := by rw [kyFanGauge_adjoint]

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[simp] theorem gauge_kyFanIdealFamily (k : ℕ) (hk : 0 < k) (A : E →L[ℂ] F) :
    (kyFanIdealFamily.{v} k hk).gauge A = ENNReal.ofReal (A.kyFanGauge k) := rfl

/-- Every bounded operator has finite Ky Fan gauge -- a finite sum of approximation numbers, each
bounded by the operator norm -- so the Ky Fan ideal is all of `E →L[𝕜] F`. -/
theorem gauge_kyFanIdealFamily_ne_top (k : ℕ) (hk : 0 < k) (A : E →L[ℂ] F) :
    (kyFanIdealFamily.{v} k hk).gauge A ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Every bounded operator lies in a finite Ky Fan ideal: the gauge is a finite sum of
approximation numbers, so it never reaches `∞`. -/
@[simp] theorem carrier_kyFanIdealFamily (k : ℕ) (hk : 0 < k) :
    (kyFanIdealFamily.{v} k hk).toOperatorIdealFamily.carrier (E := E) (F := F) = ⊤ := by
  ext A
  simp

/-- The real-valued Ky Fan gauge is recovered from the canonical one. -/
@[simp] theorem toReal_gauge_kyFanIdealFamily (k : ℕ) (hk : 0 < k) (A : E →L[ℂ] F) :
    ((kyFanIdealFamily.{v} k hk).gauge A).toReal = A.kyFanGauge k :=
  ENNReal.toReal_ofReal (A.kyFanGauge_nonneg k)

/-- The finite Ky Fan ideal is complete. -/
instance isComplete_kyFanIdealFamily (k : ℕ) (hk : 0 < k) :
    (kyFanIdealFamily.{v} k hk).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hnorm : ∀ x : (kyFanIdealFamily.{v} k hk).toOperatorIdealFamily.Elem E F,
        ‖x‖ = x.val.kyFanGauge k :=
      fun x => ENNReal.toReal_ofReal (x.val.kyFanGauge_nonneg k)
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val := by
      rw [Metric.cauchySeq_iff] at ha ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
      rw [dist_eq_norm, dist_eq_norm, hnorm]
      exact ContinuousLinearMap.opNorm_le_kyFanGauge _ hk
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk (gauge_kyFanIdealFamily_ne_top k hk L), ?_⟩
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Metric.tendsto_atTop] at hL ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hL (ε / k) (div_pos hε hkR)
    refine ⟨M, fun n hn => ?_⟩
    rw [dist_eq_norm, hnorm]
    calc ((a n).val - L).kyFanGauge k
        ≤ (k : ℝ) * ‖(a n).val - L‖ :=
          ContinuousLinearMap.kyFanGauge_le_nat_mul_opNorm _ k
      _ < (k : ℝ) * (ε / k) := by
          refine mul_lt_mul_of_pos_left ?_ hkR
          simpa [dist_eq_norm] using hM n hn
      _ = ε := by field_simp

end TauCeti
