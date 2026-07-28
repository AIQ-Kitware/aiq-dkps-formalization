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
  let C : ℝ := (8 * (‖B.A0‖ + ‖B.A1‖ + ‖B.B01‖ +
    ‖B.B10‖ + d + 1)) / (1 - r ^ 2)
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  refine ⟨C, ?_, ?_⟩
  · unfold C
    positivity
  · intro s x y hs0 hsr hx hy
    exact stable_exactSingularPair_doubleAngleTangent_le
      B hd0 hr0 hr1 hA0 hA1 hX hXr
      (s := s) (x := x) (y := y) hs0 hsr hx hy

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
  have hs_le : ∀ i : Fin F.count, X.approximationNumber i ≤ r := by
    intro i
    exact (X.approximationNumber_le_norm i).trans hXr
  have hpoint : ∀ i : Fin F.count,
      d * TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar
          (X.approximationNumber i) ≤
        2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
          (2 * C) * ε := by
    intro i
    have hi := hC.2 (X.approximationNumber i) (F.right i) (F.left i)
      (X.approximationNumber_nonneg i) (hs_le i)
      (F.norm_right i) (F.norm_left i)
    have hres : singularPairResidual X (X.approximationNumber i)
        (F.right i) (F.left i) ≤ 2 * ε := by
      unfold singularPairResidual
      linarith [F.apply_residual i, F.adjoint_residual i]
    exact hi.trans (by gcongr; nlinarith [hC.1])
  have hcoeff :
      (∑ i : Fin F.count, -RCLike.re
        ⟪F.right i, B.B01 (F.left i)⟫_ℂ) ≤
        kyFanApproximationGauge F.count B.B01 := by
    simpa [neg_re_inner_eq_re_inner_neg] using
      sum_re_inner_le_kyFanApproximationGauge
        B.B01 F.left (fun i => -F.right i)
        F.left_orthonormal F.orthonormal_neg_right
  calc
    d * ∑ i : Fin F.count,
        TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar
          (X.approximationNumber i)
        = ∑ i : Fin F.count, d *
            TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar
              (X.approximationNumber i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin F.count,
          (2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
            (2 * C) * ε) := Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * (∑ i : Fin F.count,
          -RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) +
          (2 * C) * F.count * ε := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ ≤ 2 * kyFanApproximationGauge F.count B.B01 +
          (2 * C) * F.count * ε := by
      gcongr

end FinishTanTwoTheta
end DavisKahan
end TauCeti
