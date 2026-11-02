/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: pinching contracts every Ky Fan approximation gauge.
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core
public import TauCeti.Analysis.InnerProductSpace.Projection.Block

/-!
# Pinching contracts Ky Fan approximation gauges

Discarding the off-diagonal blocks of an operator relative to an orthogonal
decomposition `E = U ⊕ Uᗮ` cannot increase any Ky Fan sum of its approximation
numbers:

```
∑_{n<k} aₙ(P_U A P_U + P_Uᗮ A P_Uᗮ)  ≤  ∑_{n<k} aₙ(A).
```

This is the Fan--Hoffman pinching contraction at approximation-number scope,
which is what an arbitrary unitarily invariant ideal gauge sees through Fan
dominance.  In the Davis--Kahan development it is the step that turns a
statement about the two *restricted* displacements into one about the full
displacement — Proposition 4.3's route.

## Why it is three lines

The pinch is an average of two unitary conjugations.  `Submodule.reflection`
`J = 2P_U − 1` is a self-adjoint unitary, and

```
2 (P_U A P_U + P_Uᗮ A P_Uᗮ) = A + J A J
```

(`Submodule.two_smul_diagBlock`).  Conjugating by a
contraction cannot increase a Ky Fan gauge, and the gauge is subadditive, so the
average is dominated.  No majorization theory is needed at this level: the
majorization content is already inside subadditivity of the gauge.

The pinching theorem below is stated over `ℂ`. Its proof now uses the accepted
scalar-generic Ky Fan triangle inequality directly.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and
  `ForTauCeti`.
-/

public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Conjugating by a reflection preserves Ky Fan approximation gauges.**

A reflection is an isometry in both slots, so the gauge cannot grow; it is
also involutive, so it cannot shrink either.  Only the `≤` direction is used
below, but the equality is the honest statement. -/
theorem kyFanApproximationGauge_reflectionConjugate_le
    [CompleteSpace E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (k : ℕ) :
    (((U.reflection : E →L[ℂ] E) ∘L A ∘L (U.reflection : E →L[ℂ] E)).kyFanGauge k : ℝ) ≤
      (A.kyFanGauge k : ℝ) := by
  let J : E →L[ℂ] E := U.reflection
  have h := (NNReal.coe_le_coe.mpr (ContinuousLinearMap.kyFanGauge_comp_comp_le J A J k))
  have hJ : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro x
    change ‖U.reflection x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using le_of_eq (U.reflection.norm_map x)
  have hnn : 0 ≤ (A.kyFanGauge k : ℝ) :=
    (NNReal.coe_nonneg (A.kyFanGauge k))
  refine h.trans ?_
  have h1 : ‖J‖ *
      (A.kyFanGauge k : ℝ) ≤ 1 * (A.kyFanGauge k : ℝ) :=
    mul_le_mul_of_nonneg_right hJ hnn
  calc
    ‖J‖ * (A.kyFanGauge k : ℝ) * ‖J‖ ≤
        1 * (A.kyFanGauge k : ℝ) * 1 :=
      mul_le_mul h1 hJ (norm_nonneg _) (by linarith)
    _ = (A.kyFanGauge k : ℝ) := by ring

omit [CompleteSpace E] in
/-- **Conjugating by a contraction pair cannot increase a Ky Fan approximation gauge.**

The two-sided ideal inequality with both norms at most one.  Stated for a bare pair of
contractions rather than for an isometry equivalence, so that the equality below can apply
it twice with the roles exchanged. -/
theorem kyFanApproximationGauge_conj_le_complex {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {L : E →L[ℂ] F} {R : F →L[ℂ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (A : E →L[ℂ] E) (k : ℕ) :
    ((L ∘L A ∘L R).kyFanGauge k : ℝ) ≤ (A.kyFanGauge k : ℝ) := by
  refine ((NNReal.coe_le_coe.mpr (ContinuousLinearMap.kyFanGauge_comp_comp_le L A R k))).trans ?_
  have hnn : 0 ≤ (A.kyFanGauge k : ℝ) := (NNReal.coe_nonneg (A.kyFanGauge k))
  have h1 : ‖L‖ * (A.kyFanGauge k : ℝ) ≤ 1 * (A.kyFanGauge k : ℝ) :=
    mul_le_mul_of_nonneg_right hL hnn
  calc
    ‖L‖ * (A.kyFanGauge k : ℝ) * ‖R‖ ≤ 1 * (A.kyFanGauge k : ℝ) * 1 :=
      mul_le_mul h1 hR (norm_nonneg _) (by linarith)
    _ = (A.kyFanGauge k : ℝ) := by ring

/-- **Ky Fan approximation gauges are invariant under conjugation by an isometry
equivalence**, in the form the block chart needs: a contraction pair with `R ∘L L = 1`.

Only the one-sided hypothesis `R ∘L L = 1` is used.  The `≤` direction is
`kyFanApproximationGauge_conj_le_complex`; the `≥` direction is the *same* lemma with `L` and `R`
exchanged, applied to `L ∘L A ∘L R`, since `R ∘L (L ∘L A ∘L R) ∘L L = A`.  Proving it once
and applying it twice is what keeps this off a self-referential rewrite. -/
theorem kyFanApproximationGauge_conj_eq_complex {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {L : E →L[ℂ] F} {R : F →L[ℂ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hRL : R ∘L L = ContinuousLinearMap.id ℂ E)
    (A : E →L[ℂ] E) (k : ℕ) :
    ((L ∘L A ∘L R).kyFanGauge k : ℝ) = (A.kyFanGauge k : ℝ) := by
  refine le_antisymm (kyFanApproximationGauge_conj_le_complex hL hR A k) ?_
  have hRLapp : ∀ y : E, R (L y) = y := by
    intro y
    have h := congrArg (fun T : E →L[ℂ] E => T y) hRL
    simpa using h
  have hcomp : R ∘L (L ∘L A ∘L R) ∘L L = A := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hRLapp x, hRLapp (A x)]
  have h := kyFanApproximationGauge_conj_le_complex hR hL (L ∘L A ∘L R) k
  rwa [hcomp] at h

/-- **Pinching contracts every Ky Fan approximation gauge.**

`∑_{n<k} aₙ(P_U A P_U + P_Uᗮ A P_Uᗮ) ≤ ∑_{n<k} aₙ(A)`.

The pinch is the average of `A` and its reflection conjugate, and the gauge is
subadditive and conjugation-invariant. -/
theorem kyFanApproximationGauge_diagBlock_le_complex
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (k : ℕ) :
    ((U.diagBlock A).kyFanGauge k : ℝ) ≤
      (A.kyFanGauge k : ℝ) := by
  have hsplit : (2 : ℂ) • U.diagBlock A =
      A + (U.reflection : E →L[ℂ] E) ∘L A ∘L (U.reflection : E →L[ℂ] E) := by
    simpa [← Nat.cast_smul_eq_nsmul ℂ] using
      (Submodule.two_smul_diagBlock (𝕜 := ℂ) U A)
  have hsum : (((2 : ℂ) • U.diagBlock A).kyFanGauge k : ℝ) ≤
      2 * (A.kyFanGauge k : ℝ) := by
    rw [hsplit]
    have htri := ContinuousLinearMap.kyFanGauge_add_le A
      ((U.reflection : E →L[ℂ] E) ∘L A ∘L (U.reflection : E →L[ℂ] E)) k
    have hreal : ((A + (U.reflection : E →L[ℂ] E) ∘L A ∘L (U.reflection : E →L[ℂ] E)).kyFanGauge k
      : ℝ) ≤
        (A.kyFanGauge k : ℝ) + (((U.reflection : E →L[ℂ] E) ∘L A ∘L (U.reflection : E →L[ℂ]
          E)).kyFanGauge k : ℝ) := by
      exact_mod_cast htri
    refine hreal.trans ?_
    have := kyFanApproximationGauge_reflectionConjugate_le U A k
    linarith
  rw [ContinuousLinearMap.kyFanGauge_smul, NNReal.coe_mul, coe_nnnorm] at hsum
  have hnorm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm] at hsum
  linarith

end ApproximationNumber
end TauCeti
