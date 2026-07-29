/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
import ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Stone

/-!
# Stone's theorem, the uniqueness half

`genToGroup hA` builds the unitary group of a self-adjoint `A`.  This module
proves that its generator is `A` again.

## Why only one inclusion has to be proved

`generator (genToGroup hA)` is self-adjoint by
`OneParameterUnitaryGroup.isSelfAdjoint_generator` (Stone's forward direction),
and `eq_of_le_of_isSelfAdjoint` says a self-adjoint operator has no proper
self-adjoint extension.  So `A ≤ generator (genToGroup hA)` already gives
equality, and the reverse inclusion — which would need a description of the
generator's domain — is never required.

## The route

The Yosida file stops at the *Lipschitz* bound
`‖expLimit hA τ ψ - ψ‖ ≤ |τ| ‖A ψ‖`; what is wanted is the derivative at
`τ = 0`.  The step from one to the other is the integral identity

`expLimit hA t ψ - ψ = ∫₀ᵗ i · expLimit hA s (A ψ) ds`  for `ψ ∈ dom A`,

after which the difference quotient is the *average* of
`s ↦ expLimit hA s (A ψ)` over `[0, t]`, and that tends to the value at `0`
because the integrand is continuous.

The identity itself is ordinary calculus for the bounded Yosida approximants
(`hasDerivAt_expTime`), and passes to the limit under the integral sign: the
integrand converges pointwise in `s` and is dominated by a constant, since a
convergent sequence of vectors is bounded.

Two other routes were tried and rejected, recorded here so they are not
retried.  The mean-value inequality applied to `s ↦ exp(isAₙ)ψ - ψ - isAₙψ`
has the right shape but needs `exp(isAₙ)φ → expLimit hA s φ` *uniformly* on
compact `s`-intervals, which is a separate equicontinuity argument.  A
second-order Duhamel estimate brings in `‖Aₙ² ψ‖`, which blows up with `n`.
-/

open scoped InnerProductSpace
open Filter Topology Complex MeasureTheory intervalIntegral

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-! ### The bounded case: an exact integral identity -/

/-- `s ↦ exp(s • B) ψ` differentiates to `exp(s • B) (B ψ)`. -/
theorem hasDerivAt_expTime_apply' (B : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun s : ℝ => expTime B s ψ) (expTime B s (B ψ)) s := by
  have h := ((ContinuousLinearMap.apply ℂ H ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_expTime B s)
  exact HasDerivAt.congr_deriv h rfl

/-- `s ↦ exp(s • B) ψ` is continuous. -/
theorem continuous_expTime_apply (B : H →L[ℂ] H) (ψ : H) :
    Continuous fun s : ℝ => expTime B s ψ := by
  have hdiff : Differentiable ℝ fun s : ℝ => expTime B s ψ := fun s =>
    (hasDerivAt_expTime_apply' B ψ s).differentiableAt
  exact hdiff.continuous

/-- **The exact integral identity for a bounded generator.** -/
theorem integral_expTime_apply (B : H →L[ℂ] H) (ψ : H) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, expTime B s (B ψ)) = expTime B t ψ - ψ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => expTime B s ψ) (expTime B s (B ψ)) s :=
    fun s _ => hasDerivAt_expTime_apply' B ψ s
  have hint : IntervalIntegrable (fun s : ℝ => expTime B s (B ψ)) volume 0 t :=
    (continuous_expTime_apply B (B ψ)).intervalIntegrable 0 t
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

end LinearPMap
end TauCeti
