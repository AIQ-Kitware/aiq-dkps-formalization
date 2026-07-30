/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Interop.TauCeti.RectangularFamilyAdapter

/-!
# Real-valued view of a canonical symmetric ideal family

`TauCeti.SymmetricOperatorIdealFamily` stores its gauge in `ℝ≥0∞`, extended by `∞`
off the ideal.  That is the right presentation for the library: it makes the gauge
total, gives the structure an `ext` lemma, and is what a Mathlib-bound development
wants.  The Davis--Kahan estimates, by contrast, are stated and proved in `ℝ` — the
paper's constants are real, and the proofs run on `linarith`, `nlinarith` and
`mul_le_mul_of_nonneg_*`, none of which work over `ℝ≥0∞`.

This file supplies the missing `ℝ` view, so that migrating a theorem off the
historical `RectangularSymmetricIdealFamily` record is a **retype and not a
re-proof**.

## Why this file exists at all

Phase C of the §13.2 migration was released three times without being started, and
the recorded reason each time was that it is "a re-proof over a differently-valued
gauge": every conclusion changes type from `ℝ` to `ℝ≥0∞`, `gauge_nonneg` goes
vacuous, `∞` cases appear, and Neumann summability in `ℝ` and in `ℝ≥0∞` are
different theorems.

All of that is true, and all of it is about a question the lane does not have to
answer.  *Which structure parameterizes a theorem* and *which numeric type its
estimate lives in* are separable, and they had been conflated because the canonical
family had no `ℝ` view to migrate onto — only `KyFanDominantIdealFamily` had one,
and that structure is strictly stronger, so retyping onto it would weaken every
theorem it touched.  With the view below, the 18 remaining legacy-binder modules
change their binder and keep their proofs; restating the estimates in `ℝ≥0∞` becomes
a separate and genuinely optional decision.

## Statements first, proofs later

Every lemma here is *stated* over `N.gaugeReal` and `N.Mem` and *proved* by handing
the goal to the corresponding field of `N.toRectangular` — legitimate because
`toRectangular` defines exactly `Mem A := gauge A ≠ ∞` and
`gauge A := (gauge A).toReal`, so the two sides are the same term.

That split is deliberate.  Consumers migrate against these statements now, while the
adapter is still the thing that discharges them; when
`RectangularFamilyAdapter.lean` is finally deleted, only the *proofs* in this one
file need to be redone, and no consumer moves again.  The alternative — migrating
consumers directly onto the adapter — would have to be undone later at every site.
-/

open scoped ENNReal

namespace TauCeti

namespace SymmetricOperatorIdealFamily

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
variable [N.toOperatorIdealFamily.IsComplete]

/-- Membership in the ideal: the gauge is finite.

The same predicate as `OperatorIdealFamily.carrier`, spelled as the `Mem` the
Davis--Kahan statements are written against. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toOperatorIdealFamily.gauge A ≠ ∞

/-- The ideal gauge read in `ℝ`.  Meaningful on members; off the ideal the stored
gauge is `∞` and `ENNReal.toReal` sends it to `0`, which is why every lemma below
that needs a value carries a `Mem` hypothesis. -/
noncomputable abbrev gaugeReal (A : E →L[𝕜] F) : ℝ :=
  (N.toOperatorIdealFamily.gauge A).toReal

omit [N.toOperatorIdealFamily.IsComplete] in
/-- `Mem` is exactly membership in the canonical carrier. -/
theorem mem_iff_mem_carrier (A : E →L[𝕜] F) :
    N.Mem A ↔ A ∈ N.toOperatorIdealFamily.carrier := Iff.rfl

omit [N.toOperatorIdealFamily.IsComplete] in
/-- The real gauge is the `toReal` of the stored `ℝ≥0∞` gauge. -/
theorem gaugeReal_eq_toReal (A : E →L[𝕜] F) :
    N.gaugeReal A = (N.toOperatorIdealFamily.gauge A).toReal := rfl

/-- The zero operator lies in every ideal. -/
theorem zero_mem : N.Mem (0 : E →L[𝕜] F) :=
  N.toRectangular.zero_mem

/-- Ideals are closed under addition. -/
theorem add_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A + B) :=
  N.toRectangular.add_mem hA hB

/-- Ideals are closed under scalar multiplication. -/
theorem smul_mem (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (c • A) :=
  N.toRectangular.smul_mem c hA

/-- A symmetric ideal is closed under adjoints. -/
theorem adjoint_mem {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem A.adjoint :=
  N.toRectangular.adjoint_mem hA

/-- The two-sided ideal law: outer composition stays in the ideal. -/
theorem comp_mem (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.Mem (L ∘L A ∘L R) :=
  N.toRectangular.comp_mem L R hA

/-- The real gauge is nonnegative on members. -/
theorem gaugeReal_nonneg {A : E →L[𝕜] F} (hA : N.Mem A) : 0 ≤ N.gaugeReal A :=
  N.toRectangular.gauge_nonneg hA

/-- The zero operator has zero gauge. -/
theorem gaugeReal_zero : N.gaugeReal (0 : E →L[𝕜] F) = 0 :=
  N.toRectangular.gauge_zero

/-- The real gauge is subadditive on members. -/
theorem gaugeReal_add_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gaugeReal (A + B) ≤ N.gaugeReal A + N.gaugeReal B :=
  N.toRectangular.gauge_add_le hA hB

/-- The real gauge is absolutely homogeneous on members. -/
theorem gaugeReal_smul (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal (c • A) = ‖c‖ * N.gaugeReal A :=
  N.toRectangular.gauge_smul c hA

/-- The real gauge is adjoint-invariant. -/
theorem gaugeReal_adjoint {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal A.adjoint = N.gaugeReal A :=
  N.toRectangular.gauge_adjoint hA

/-- The two-sided estimate, in `ℝ`. -/
theorem gaugeReal_comp_le (L : F →L[𝕜] G) (R : H →L[𝕜] E) {A : E →L[𝕜] F}
    (hA : N.Mem A) :
    N.gaugeReal (L ∘L A ∘L R) ≤ ‖L‖ * N.gaugeReal A * ‖R‖ :=
  N.toRectangular.gauge_comp_le L R hA

/-- The operator norm is dominated by the real gauge on members. -/
theorem opNorm_le_gaugeReal {A : E →L[𝕜] F} (hA : N.Mem A) : ‖A‖ ≤ N.gaugeReal A :=
  N.toRectangular.opNorm_le_gauge hA

/-- Left composition stays in the ideal. -/
theorem comp_left_mem (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.Mem (L ∘L A) :=
  N.toRectangular.comp_left_mem L hA

/-- Left composition is bounded by the operator norm times the gauge. -/
theorem gaugeReal_comp_left_le_mul (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal (L ∘L A) ≤ ‖L‖ * N.gaugeReal A :=
  N.toRectangular.gauge_comp_left_le_mul L hA

/-- Right composition stays in the ideal. -/
theorem comp_right_mem (R : H →L[𝕜] E) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.Mem (A ∘L R) :=
  N.toRectangular.comp_right_mem R hA

/-- Right composition is bounded by the gauge times the operator norm. -/
theorem gaugeReal_comp_right_le_mul (R : H →L[𝕜] E) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal (A ∘L R) ≤ N.gaugeReal A * ‖R‖ :=
  N.toRectangular.gauge_comp_right_le_mul R hA

/-- Ideals are closed under subtraction. -/
theorem sub_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A - B) :=
  N.toRectangular.sub_mem hA hB

/-- The real gauge is subadditive for differences. -/
theorem gaugeReal_sub_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gaugeReal (A - B) ≤ N.gaugeReal A + N.gaugeReal B :=
  N.toRectangular.gauge_sub_le hA hB

end SymmetricOperatorIdealFamily

end TauCeti
