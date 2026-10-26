/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSquare

/-!
# The Schatten Gram identity in arbitrary complex Hilbert dimension

For `p>=2`, `||T* T||_(p/2) = ||T||_p^2` in the accepted Schatten
families, including infinite values. This is the classical Q-norm identity.
The proof consumes the existing unmerged Gram approximation-number
theorem; no second Schatten family or norm is defined.
-/

public section

noncomputable section

namespace TauCeti.OperatorIdealFamily

open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The literal Gram Schatten power equals the original Schatten power,
with no dimension, compactness or finite-cost hypothesis. -/
theorem gauge_schatten_gram_rpow (p : ℝ) (hp : 2 ≤ p) (T : E →L[ℂ] F) :
    (schatten ℂ (p / 2) (by linarith)).gauge (T.adjoint ∘L T) ^ (p / 2) =
      (schatten ℂ p (by linarith)).gauge T ^ p := by
  rw [gauge_schatten_rpow, gauge_schatten_rpow]
  apply tsum_congr
  intro n
  have hreal := ApproximationNumber.approximationNumber_gramOperator_complex T n
  simp only [ContinuousLinearMap.approximationNumber_eq_singularValue_toReal] at hreal
  have hsq : (T.adjoint ∘L T).singularValue n = T.singularValue n ^ 2 := by
    apply NNReal.coe_injective
    simpa only [ApproximationNumber.gramOperator, NNReal.coe_pow] using hreal
  rw [hsq, ENNReal.coe_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (p / 2) = p by ring]

/-- **The Schatten Q-norm identity**, for the accepted Hilbert-space
families. The equality remains literal at infinite ideal cost. -/
theorem gauge_schatten_gram_eq_sq (p : ℝ) (hp : 2 ≤ p) (T : E →L[ℂ] F) :
    (schatten ℂ (p / 2) (by linarith)).gauge (T.adjoint ∘L T) =
      (schatten ℂ p (by linarith)).gauge T ^ (2 : ℝ) := by
  apply ENNReal.rpow_left_injective (by linarith : p / 2 ≠ 0)
  dsimp only
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring]
  exact gauge_schatten_gram_rpow p hp T

end TauCeti.OperatorIdealFamily
