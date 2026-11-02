/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CanonicalGauge

/-!
# Finite-dimensional localization of approximation numbers

The `n`th approximation number of a bounded operator between Hilbert spaces is already
determined by the restrictions of the operator to `(n+1)`-generated subspaces of its source:

```
aₙ(T) = sSup { aₙ (T ∘L (span {v 0, …, v n}).subtypeL) | v : Fin (n + 1) → E }.
```

The supremum is a genuine least upper bound (`approximationNumber_isLUB_finiteRestrictions`),
not merely a bound, and the family is indexed by *all* families of `n + 1` vectors —
linearly dependent ones are harmless, contributing restrictions to smaller subspaces.

## Native converse min–max input

The conditional localization results below extend accepted
`TauCeti.HasMinMaxLowerBound`. Complete inner-product sources satisfy that
predicate by `TauCeti.HasMinMaxLowerBound.of_completeSpace`, uniformly over
`RCLike`, without target completeness. No separate predicate, capability class,
or real/complex threshold implementation is defined here.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.{`
  `approximationNumber_comp_subtypeL_le, finiteRestrictionApproximationNumbers,`
  `finiteRestrictionApproximationNumbers_upperBound,`
  `exists_finiteRestrictionApproximationNumber_gt_of_lt,`
  `approximationNumber_isLUB_finiteRestrictions,`
  `lt_approximationNumber_iff_exists_finiteDimensional_lowerBound}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The statements are unchanged apart from
  the generalisation of `approximationNumber_comp_subtypeL_le` to an arbitrary `RCLike`
  field; the declarations move from `TauCeti.DavisKahan.Experimental` to
  `ContinuousLinearMap`, so that dot notation resolves.
* Spectra influence: **none**.  The module was under `DavisKahan/Interop/Spectra/` because
  its threshold theorem was once proved from `vendor/Spectra`'s projection-valued measures.
  That proof was replaced on 2026-07-28 by
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, after which
  nothing here touched Spectra and the module belonged in the staging layer.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

universe u v w

section Restriction

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Restriction to a subspace cannot increase an approximation number. -/
theorem approximationNumber_comp_subtypeL_le
    (T : E →L[𝕜] F) (n : ℕ) (V : Submodule 𝕜 E) :
    ((T ∘L V.subtypeL).singularValue n : ℝ) ≤ (T.singularValue n : ℝ) := by
  have h := (NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_right T V.subtypeL n))
  have hsub : ‖V.subtypeL‖ ≤ (1 : ℝ) := V.norm_subtypeL_le
  calc
    ((T ∘L V.subtypeL).singularValue n : ℝ)
        ≤ (T.singularValue n : ℝ) * ‖V.subtypeL‖ := h
    _ ≤ (T.singularValue n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hsub ((T.singularValue n).coe_nonneg)
    _ = (T.singularValue n : ℝ) := by rw [mul_one]

/-- The approximation numbers of the restrictions of `T` to the spans of `n + 1` vectors.

Linearly dependent families are deliberately not excluded: they merely contribute
restrictions to subspaces of smaller dimension, which the supremum ignores. -/
def finiteRestrictionApproximationNumbers (T : E →L[𝕜] F) (n : ℕ) : Set ℝ :=
  Set.range fun v : Fin (n + 1) → E =>
    ((T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).singularValue n : ℝ)

/-- The ambient approximation number bounds every finite restriction. -/
theorem finiteRestrictionApproximationNumbers_upperBound (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ∈ upperBounds (T.finiteRestrictionApproximationNumbers n) := by
  rintro _ ⟨v, rfl⟩
  exact T.approximationNumber_comp_subtypeL_le n (Submodule.span 𝕜 (Set.range v))

end Restriction

end

end ContinuousLinearMap

namespace TauCeti.HasMinMaxLowerBound

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]


/-- Every strict lower threshold for the ambient approximation number is exceeded by an
approximation number of an `(n+1)`-generated restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (T.singularValue n : ℝ)) :
    ∃ v : Fin (n + 1) → E,
      r < ((T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).singularValue n : ℝ) := by
  obtain ⟨s, hrs, v, hv, hV⟩ := TauCeti.hasMinMaxLowerBound_iff.mp h T n hr0
    (by exact hr)
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
  let w : Fin (n + 1) → V := fun i => b i
  have hw : LinearIndependent 𝕜 w := by
    simpa only [w] using b.linearIndependent
  have hsNN : s ≤ ((T ∘L V.subtypeL).singularValue n : ℝ) := by
    apply (T ∘L V.subtypeL).le_singularValue_of_linearIndependent hw
    intro x _
    exact hV (x : E) x.property
  exact ⟨v, by simpa only [V] using hrs.trans_le hsNN⟩

/-- **Exact finite-dimensional localization.**  The ambient approximation number is the
least upper bound of the approximation numbers of the restrictions to spans of `n + 1`
vectors.

Approximation numbers are real-valued, so `IsLUB` is the conditionally-complete
formulation appropriate to `ℝ`; the family is nonempty and bounded above by the ambient
approximation number. -/
theorem approximationNumber_isLUB_finiteRestrictions
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB (T.finiteRestrictionApproximationNumbers n) ((T.singularValue n : ℝ)) := by
  refine ⟨T.finiteRestrictionApproximationNumbers_upperBound n, ?_⟩
  intro b hb
  -- Every upper bound of a nonempty family of nonnegative reals is nonnegative.
  have hb0 : 0 ≤ b :=
    ((ContinuousLinearMap.singularValue _ n).coe_nonneg).trans (hb ⟨fun _ => 0, rfl⟩)
  by_contra hnot
  obtain ⟨v, hv⟩ :=
    h.exists_finiteRestrictionApproximationNumber_gt_of_lt T n hb0 (lt_of_not_ge hnot)
  exact (not_le_of_gt hv) (hb ⟨v, rfl⟩)

/-- **Epsilon form of the min--max characterisation.**  `r` is strictly below `aₙ(T)`
exactly when `T` has a strictly larger uniform lower modulus on some `(n+1)`-dimensional
subspace.

The forward direction is the hypothesis and the reverse is
`ContinuousLinearMap.le_singularValue_of_linearIndependent`, so this is the statement
in which both halves of the min--max theorem appear together. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < (T.singularValue n : ℝ) ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
          ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · intro hr
    exact TauCeti.hasMinMaxLowerBound_iff.mp h T n hr0
      (by exact hr)
  · rintro ⟨s, hrs, v, hv, hV⟩
    refine hrs.trans_le ?_
    exact T.le_singularValue_of_linearIndependent hv hV

/-- Every positive tolerance admits a finite source restriction whose approximation number
is within that tolerance of the ambient one.  This is the exact hypothesis
`ContinuousLinearMap.kyFanGaugeReal_add_le_of_exists_finiteRestriction` consumes, so it is the
last step before the Ky Fan triangle inequality holds over any field with a min--max lower
bound rather than over `ℂ` alone. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E,
      (T.singularValue n : ℝ) <
        ((T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).singularValue n : ℝ) + ε := by
  by_cases hsmall : (T.singularValue n : ℝ) < ε
  · exact ⟨fun _ => 0, hsmall.trans_le
      (le_add_of_nonneg_left ((ContinuousLinearMap.singularValue _ _).coe_nonneg))⟩
  · have hεle : ε ≤ (T.singularValue n : ℝ) := le_of_not_gt hsmall
    obtain ⟨v, hv⟩ := h.exists_finiteRestrictionApproximationNumber_gt_of_lt T n
      (sub_nonneg.mpr hεle) (sub_lt_self _ hε)
    exact ⟨v, by linarith⟩


end TauCeti.HasMinMaxLowerBound
