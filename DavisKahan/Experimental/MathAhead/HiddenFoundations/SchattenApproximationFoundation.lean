/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Approximation-number foundation for rectangular Schatten ideals

The remaining Schatten and trace-class work is not a collection of missing
names.  It is the analytic theorem that the `ell^p` gauge of approximation
numbers is a complete rectangular operator ideal and satisfies the triangle
inequality.  This file makes that theorem a first-class interface, defines the
intended membership and gauge without fictional APIs, and proves that any
implementation of the analytic interface immediately produces the coherent
family consumed by the Davis--Kahan ideal layer.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace HiddenFoundations

noncomputable section

universe u v

variable {k : Type u} [RCLike k]

/-- Real approximation-number sequence. -/
def approximationNumberSequence
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
    (T : E →L[k] F) (n : ℕ) : ℝ :=
  T.approximationNumber n

/-- `p`-power energy of the approximation-number sequence. -/
def schattenEnergy
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
    (p : ℝ) (T : E →L[k] F) : ℝ :=
  ∑' n : ℕ, (approximationNumberSequence T n) ^ p

/-- Membership in the rectangular Schatten class, expressed directly by
summability of the approximation-number `p` powers. -/
def IsSchatten
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
    (p : ℝ) (T : E →L[k] F) : Prop :=
  Summable (fun n : ℕ => (approximationNumberSequence T n) ^ p)

/-- Schatten gauge derived from the `p`-power energy. -/
def schattenGauge
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
    (p : ℝ) (T : E →L[k] F) : ℝ :=
  (schattenEnergy p T) ^ (p⁻¹)

/-- The full analytic campaign needed to turn approximation-number `ell^p`
energy into a coherent rectangular ideal.  The fields correspond exactly to
the Tomić--Weyl majorization argument, adjoint invariance, ideal domination,
and Fatou/completeness passage. -/
structure SchattenApproximationFoundation (p : ℝ) (hp : 1 ≤ p) where
  zero_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F],
      IsSchatten p (0 : E →L[k] F)
  add_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A B : E →L[k] F}, IsSchatten p A → IsSchatten p B →
      IsSchatten p (A + B)
  smul_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      (c : k) {A : E →L[k] F}, IsSchatten p A → IsSchatten p (c • A)
  adjoint_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A : E →L[k] F}, IsSchatten p A → IsSchatten p A.adjoint
  comp_mem :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
      (L : F →L[k] G) {A : E →L[k] F} (R : H →L[k] E),
      IsSchatten p A → IsSchatten p (L ∘L A ∘L R)
  gauge_nonneg :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A : E →L[k] F}, IsSchatten p A → 0 ≤ schattenGauge p A
  gauge_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F],
      schattenGauge p (0 : E →L[k] F) = 0
  gauge_eq_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A : E →L[k] F}, IsSchatten p A → schattenGauge p A = 0 → A = 0
  triangle :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A B : E →L[k] F}, IsSchatten p A → IsSchatten p B →
      schattenGauge p (A + B) ≤ schattenGauge p A + schattenGauge p B
  gauge_smul :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      (c : k) {A : E →L[k] F}, IsSchatten p A →
      schattenGauge p (c • A) = ‖c‖ * schattenGauge p A
  gauge_adjoint :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A : E →L[k] F}, IsSchatten p A →
      schattenGauge p A.adjoint = schattenGauge p A
  gauge_comp_le :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
      (L : F →L[k] G) {A : E →L[k] F} (R : H →L[k] E),
      IsSchatten p A →
      schattenGauge p (L ∘L A ∘L R) ≤
        ‖L‖ * schattenGauge p A * ‖R‖
  opNorm_le_gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      {A : E →L[k] F}, IsSchatten p A → ‖A‖ ≤ schattenGauge p A
  complete :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace k F] [CompleteSpace F]
      (A : ℕ → E →L[k] F),
      (∀ n, IsSchatten p (A n)) →
      (∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ m n,
        N ≤ m → N ≤ n → schattenGauge p (A m - A n) < epsilon) →
      ∃ L : E →L[k] F, IsSchatten p L ∧
        ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n,
          N ≤ n → schattenGauge p (A n - L) < epsilon

/-- A completed approximation-number campaign produces the family consumed by
the exact rectangular Davis--Kahan theory. -/
noncomputable def SchattenApproximationFoundation.toFamily
    {p : ℝ} {hp : 1 ≤ p}
    (D : SchattenApproximationFoundation (k := k) p hp) :
    RectangularSymmetricIdealFamily (𝕜 := k) :=
  { Mem := fun T => IsSchatten p T
    gauge := fun T => schattenGauge p T
    zero_mem := D.zero_mem
    add_mem := D.add_mem
    smul_mem := D.smul_mem
    adjoint_mem := D.adjoint_mem
    comp_mem := D.comp_mem
    gauge_nonneg := D.gauge_nonneg
    gauge_zero := D.gauge_zero
    gauge_eq_zero := D.gauge_eq_zero
    gauge_add_le := D.triangle
    gauge_smul := D.gauge_smul
    gauge_adjoint := D.gauge_adjoint
    gauge_comp_le := D.gauge_comp_le
    opNorm_le_gauge := D.opNorm_le_gauge
    gauge_complete := D.complete }

/-- The trace-class campaign is the `p=1` specialization. -/
abbrev TraceClassApproximationFoundation :=
  SchattenApproximationFoundation.{u, v} (k := k) (1 : ℝ) le_rfl

/-- The Hilbert--Schmidt campaign is the `p=2` specialization.  Over complex
scalars this can be discharged by the canonical Hilbert-tensor construction
in `HilbertSchmidtComplexFamily`. -/
abbrev HilbertSchmidtApproximationFoundation :=
  SchattenApproximationFoundation.{u, v} (k := k) (2 : ℝ) (by norm_num)

end
end HiddenFoundations
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
