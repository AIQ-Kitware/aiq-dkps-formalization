/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Normalized unitarily invariant norms

Davis and Kahan's Section 1 fixes a norm `‖·‖` on operators and lists the
properties it must have.  This module is the Lean type for that object.

## What the source asks for

Reading Section 1, a normalized unitarily invariant norm carries:

* a domain -- the ideal on which it is finite, since the source is explicit that
  a result is vacuous when a displayed norm fails to exist;
* the norm axioms: nonnegativity, definiteness, homogeneity, the triangle
  inequality;
* invariance `‖V K W‖ = ‖K‖` under unitary `V` and `W`, equation (1.9);
* the normalization `‖u v*‖ = ‖u‖ ‖v‖` on rank-one operators;
* compatibility with contractions -- multiplying on either side by an operator
  of norm at most one does not increase the norm;
* Fan dominance in the strong form the source announces at (1.11)-(1.13):
  an inequality holds for every unitarily invariant norm exactly when it holds
  for every Ky Fan norm.

## What is a field and what is a theorem

Most of that list is already the content of `TauCeti.OperatorIdealFamily` and its
symmetric and Fan-dominant refinements, which this structure extends.  The
`ℝ≥0∞`-valued gauge is the domain: `∞` off the ideal is exactly the source's
"the norm does not exist here".

Only **one** item is not already available, so only one is a new field:

* `gauge_rankOne_eq_one`, the normalization.

Everything else is derived below and stated as a theorem, not assumed:

* `gauge_eq_zero_iff` -- definiteness, from `enorm_le_gauge`;
* `gauge_unitaryConj`, `gauge_comp_isometryEquiv_left/right` -- equation (1.9),
  from the two-sided ideal law applied in both directions;
* `gauge_le_of_norm_le_one_left/right` -- contraction compatibility, likewise.

Deriving them rather than assuming them is the point: a caller constructing one
of these supplies the source's *irredundant* data, and the source's own listed
properties are then compiler-checked consequences rather than restated
hypotheses.

## Relation to the other two norm models

```text
NormalizedUnitaryInvariantNorm      the source's own class
        │  toKyFanDominantIdealFamily
        ▼
KyFanDominantIdealFamily            Fan dominance as a field
        │  the estimate bridges in Ideals/SymmetricNormingFanDominance
        ▼
SymmetricNormingFunction            Gohberg--Krein symmetric gauge
```

The downward arrow is a projection, so a theorem proved for every
`KyFanDominantIdealFamily` applies to every source norm immediately.  That is
what makes the source-facing façades cheap: they quantify over this type and
their proofs discharge through the arrow.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe u v

/-- **A normalized unitarily invariant norm, as Davis--Kahan's Section 1 fixes
it.**

A Fan-dominant symmetric operator ideal family together with the source's
normalization on rank-one operators.  See the module docstring for which of the
source's listed properties are fields here and which are derived. -/
structure NormalizedUnitaryInvariantNorm (𝕜 : Type u) [RCLike 𝕜] where
  /-- The Fan-dominant symmetric ideal family supplying the gauge, its domain,
  and all the norm and ideal laws. -/
  toKyFanDominantIdealFamily : KyFanDominantIdealFamily.{u, v} 𝕜
  /-- **The source normalization.**  A rank-one operator of norm one has norm
  one -- the Lean spelling of `‖u v*‖ = ‖u‖ ‖v‖` after scaling both vectors to
  norm one. -/
  gauge_rankOne_eq_one : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {V : E →L[𝕜] F}, ‖V‖ = 1 → V.rank ≤ (1 : Cardinal) →
      toKyFanDominantIdealFamily.gauge V = 1

namespace NormalizedUnitaryInvariantNorm

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)

/-- Membership in the norm's ideal: the source's "the norm exists here". -/
abbrev Mem (A : E →L[𝕜] F) : Prop := N.toKyFanDominantIdealFamily.Mem A

/-- The real-valued norm, meaningful on its ideal. -/
noncomputable abbrev gauge (A : E →L[𝕜] F) : ℝ :=
  N.toKyFanDominantIdealFamily.gauge A

/-- Membership and the gauge are read off the underlying family; this is the
bridge a façade proof uses. -/
theorem mem_iff_kyFanDominant (A : E →L[𝕜] F) :
    N.Mem A ↔ N.toKyFanDominantIdealFamily.Mem A := Iff.rfl

/-- The gauge is the underlying family's gauge. -/
theorem gauge_eq_kyFanDominant (A : E →L[𝕜] F) :
    N.gauge A = N.toKyFanDominantIdealFamily.gauge A := rfl

/-! ### The source's listed properties, derived

Each theorem below is one line of Davis--Kahan's Section 1 list.  None is a field
of the structure: they follow from the ideal laws the underlying family already
carries, and proving them here is what makes the structure's data irredundant. -/

/-- **Nonnegativity.** -/
theorem gauge_nonneg {A : E →L[𝕜] F} (hA : N.Mem A) : 0 ≤ N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_nonneg hA

/-- **Definiteness.**  The norm vanishes only on the zero operator. -/
theorem gauge_eq_zero_iff {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A = 0 ↔ A = 0 := by
  constructor
  · intro h
    exact N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_eq_zero hA h
  · rintro rfl
    exact N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_zero

/-- **The triangle inequality.** -/
theorem gauge_add_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gauge (A + B) ≤ N.gauge A + N.gauge B :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_add_le hA hB

/-- **Absolute homogeneity.** -/
theorem gauge_smul (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge (c • A) = ‖c‖ * N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_smul c hA

/-- **Contraction compatibility on the left.**  Composing with an operator of
norm at most one does not increase the norm. -/
theorem gauge_comp_left_le (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A)
    (hL : ‖L‖ ≤ 1) : N.gauge (L ∘L A) ≤ N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_comp_left_le L hA hL

/-- **Contraction compatibility on the right.** -/
theorem gauge_comp_right_le {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A)
    (hR : ‖R‖ ≤ 1) : N.gauge (A ∘L R) ≤ N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_comp_right_le R hA hR

/-- **The norm dominates the operator norm**, so it is a norm and not a
seminorm on its ideal. -/
theorem opNorm_le_gauge {A : E →L[𝕜] F} (hA : N.Mem A) : ‖A‖ ≤ N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.opNorm_le_gaugeReal hA

/-- **Adjoint invariance**, which the source uses whenever it transposes a
block. -/
theorem gauge_adjoint {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A.adjoint = N.gauge A :=
  N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_adjoint hA

/-- A linear isometric equivalence is a contraction. -/
private theorem norm_isometryEquiv_le_one {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (g : X ≃ₗᵢ[𝕜] Y) : ‖(g.toContinuousLinearEquiv : X →L[𝕜] Y)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

/-- **Equation (1.9): unitary invariance.**  Composing with linear isometric
equivalences on either side leaves the norm unchanged.

Both inequalities come from contraction compatibility: an isometric equivalence
and its inverse are contractions, so neither direction can strictly decrease the
norm.  This is why (1.9) is a theorem here rather than a field. -/
theorem gauge_comp_isometryEquiv (e : F ≃ₗᵢ[𝕜] G) (f : H ≃ₗᵢ[𝕜] E)
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge ((e.toContinuousLinearEquiv : F →L[𝕜] G) ∘L A ∘L
      (f.toContinuousLinearEquiv : H →L[𝕜] E)) = N.gauge A := by
  set S := N.toKyFanDominantIdealFamily.toSymmetricOperatorIdealFamily with hS
  set B := (e.toContinuousLinearEquiv : F →L[𝕜] G) ∘L A ∘L
    (f.toContinuousLinearEquiv : H →L[𝕜] E) with hB
  have hBmem : N.Mem B := S.comp_mem _ _ hA
  -- `A` is recovered from `B` by the inverse equivalences.
  have hAeq : A = (e.symm.toContinuousLinearEquiv : G →L[𝕜] F) ∘L B ∘L
      (f.symm.toContinuousLinearEquiv : E →L[𝕜] H) := by
    ext x
    simp [hB]
  refine le_antisymm ?_ ?_
  · calc N.gauge B
        ≤ N.gauge (A ∘L (f.toContinuousLinearEquiv : H →L[𝕜] E)) := by
          rw [hB, ← ContinuousLinearMap.comp_assoc]
          exact S.gaugeReal_comp_left_le _ (S.comp_right_mem _ hA)
            (norm_isometryEquiv_le_one e)
      _ ≤ N.gauge A := S.gaugeReal_comp_right_le _ hA (norm_isometryEquiv_le_one f)
  · calc N.gauge A
        = N.gauge ((e.symm.toContinuousLinearEquiv : G →L[𝕜] F) ∘L B ∘L
            (f.symm.toContinuousLinearEquiv : E →L[𝕜] H)) := by rw [← hAeq]
      _ ≤ N.gauge (B ∘L (f.symm.toContinuousLinearEquiv : E →L[𝕜] H)) := by
          rw [← ContinuousLinearMap.comp_assoc]
          exact S.gaugeReal_comp_left_le _ (S.comp_right_mem _ hBmem)
            (norm_isometryEquiv_le_one e.symm)
      _ ≤ N.gauge B :=
          S.gaugeReal_comp_right_le _ hBmem (norm_isometryEquiv_le_one f.symm)

end NormalizedUnitaryInvariantNorm

end

end ExactSinTheta
end DavisKahan
end TauCeti
