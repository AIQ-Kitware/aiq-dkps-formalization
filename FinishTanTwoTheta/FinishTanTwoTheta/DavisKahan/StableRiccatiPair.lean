/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.FunctionalCalculus.DoubleAngleTangent
import DavisKahan.Experimental.Scratch.Section7.InfiniteTanTwoThetaCore

/-!
# Stable approximate singular-pair Riccati estimate

The existing proof gives the sharp coefficient estimate for an exact singular
pair.  This file records the uniform stability theorem needed to use the
approximate leading singular families available for arbitrary bounded
operators.  The stability constant is selected *before* the approximation
tolerance, so the final epsilon limit is logically valid.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open DavisKahanExt DavisKahanTheory
open Experimental.Scratch.Section7

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Residual size for an approximate left/right singular pair. -/
def singularPairResidual (X : E0 →L[ℂ] E1)
    (s : ℝ) (x : E0) (y : E1) : ℝ :=
  ‖X x - (s : ℂ) • y‖ +
    ‖X.adjoint y - (s : ℂ) • x‖

/-- Predicate asserting that `C` is one uniform stability constant for every
unit approximate singular pair with singular parameter in `[0,r]`. -/
def IsStableRiccatiConstant
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (d r : ℝ)
    (X : E0 →L[ℂ] E1) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (s : ℝ) (x : E0) (y : E1),
      0 ≤ s → s ≤ r → ‖x‖ = 1 → ‖y‖ = 1 →
      d * TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar s ≤
        2 * (-RCLike.re ⟪x, B.B01 y⟫_ℂ) +
          C * singularPairResidual X s x y

/-- **Uniform stability of equation (7.6).**

On a fixed contraction interval `0 <= s <= r < 1`, there is one constant valid
for every approximate pair and every later approximation tolerance. -/
theorem exists_stableRiccatiPair_constant
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d r : ℝ} (hd0 : 0 ≤ d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X) (hXr : ‖X‖ ≤ r) :
    ∃ C : ℝ, IsStableRiccatiConstant B d r X C := by
  /-
  Expand the pointwise Riccati identity exactly as in
  `exactSingularPair_doubleAngleTangent_le_neg_re_inner`, but retain
  `e=Xx-sy` and `f=X*y-sx`.  Every new term is bounded by Cauchy--Schwarz and
  operator norms.  Division by `1-s^2` is uniformly safe because
  `1-s^2 >= 1-r^2 > 0`.  Collect the finitely many coefficients into one
  explicit nonnegative constant.
  -/
  sorry

/-- Summed stable estimate for one approximate leading singular family, using
a constant chosen independently of the family and its tolerance. -/
theorem transformed_selected_sum_le_kyFan_add_error
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d r ε C : ℝ} (hr0 : 0 ≤ r)
    {X : E0 →L[ℂ] E1} (hXr : ‖X‖ ≤ r)
    (hC : IsStableRiccatiConstant B d r X C)
    {k : ℕ}
    (F : TauCeti.FinishTanTwoTheta.ApproximateLeadingSingularFamily X k ε) :
    d * ∑ i : Fin F.count,
        TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar
          (X.approximationNumber i) ≤
      2 * kyFanApproximationGauge F.count B.B01 +
        (2 * C) * F.count * ε := by
  /-
  Apply `hC` to every selected pair.  Each of the two residuals is at most
  `ε`, hence their sum is at most `2ε`.  Sum the signed coefficients and use
  the dimension-free orthonormal Ky Fan variational bound.  Monotonicity of
  approximation numbers and `hXr` place every selected scalar in `[0,r]`.
  -/
  sorry

end FinishTanTwoTheta
end DavisKahan
end TauCeti
