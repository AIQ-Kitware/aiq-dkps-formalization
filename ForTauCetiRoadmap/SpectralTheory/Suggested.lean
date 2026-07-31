/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Spectral theory of self-adjoint operators: suggested signatures

The roadmap prose is authoritative.  This file records representative target
shapes using names already present in the staged `ForTauCeti` implementation;
it is not exhaustive, and discharging everything here finishes neither a Part
nor the roadmap.  The representation decision runs through every signature:
an unbounded operator is a Mathlib `LinearPMap` (`H →ₗ.[𝕜] H`), and
closedness, dense domain, and self-adjointness are hypotheses on it.
-/

namespace TauCetiRoadmap.SpectralTheory

open scoped InnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Part A -- one-parameter unitary groups and Stone's theorem (T13) -/

/-- A strongly continuous one-parameter unitary group on a complex Hilbert
space. -/
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  identity : U 0 = ContinuousLinearMap.id ℂ H
  strong_continuous : ∀ ψ : H, Continuous fun t : ℝ => U t ψ

/-- The generator: a `LinearPMap` defined on exactly the vectors where the
difference quotient converges. -/
noncomputable def generator (U : OneParameterUnitaryGroup H) : H →ₗ.[ℂ] H := sorry

/-- **Stone's theorem, forward direction**: the generator is self-adjoint, with
density of the domain derived rather than assumed. -/
theorem isSelfAdjoint_generator (U : OneParameterUnitaryGroup H) :
    IsSelfAdjoint (generator U) := sorry

/-- The commutant lemma: an operator commuting with the group leaves the
generator's domain invariant and commutes with the generator. -/
theorem generator_commutant (U : OneParameterUnitaryGroup H) (T : H →L[ℂ] H)
    (hT : ∀ t, (U.U t).comp T = T.comp (U.U t)) : True := sorry

/-! ## Part B -- the Borel functional calculus and projection-valued measures (T14) -/

section BorelCalculus

variable (a : H →L[ℂ] H)

/-- The bounded Borel functional calculus of a normal operator, extending the
continuous calculus along dominated convergence of diagonal measures. -/
noncomputable def borelCalculus (ha : IsStarNormal a)
    (f : spectrum ℂ a → ℂ) (hf : Measurable f) (hb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    H →L[ℂ] H := sorry

/-- Multiplicativity of the Borel calculus, carried from the continuous calculus
by the polarised transport principle. -/
theorem borelCalculus_mul (ha : IsStarNormal a) : True := sorry

/-- A projection-valued measure on the Borel sets of `ℝ`: projections, countable
additivity in the strong topology, and the diagonal scalar measures as data. -/
structure ProjValMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  proj : Set ℝ → (H →L[ℂ] H)
  isIdempotent : ∀ s, MeasurableSet s → (proj s).comp (proj s) = proj s
  isSelfAdjoint : ∀ s, MeasurableSet s → IsSelfAdjoint (proj s)
  empty : proj ∅ = 0
  univ : proj Set.univ = ContinuousLinearMap.id ℂ H

end BorelCalculus

/-! ## Part C -- closed operators on LinearPMap: graphs, constructions, form bounds (T15a) -/

section ClosedOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Perturbation of a partial map by an operator on its domain, the domain-aware
sum that keeps the carrier a `LinearPMap`. -/
noncomputable def perturb (A : E →ₗ.[𝕜] E) (V : A.domain →ₗ[𝕜] E) : E →ₗ.[𝕜] E := sorry

/-- Self-adjointness survives a bounded symmetric perturbation
(Kato--Rellich at relative bound zero). -/
theorem isSelfAdjoint_perturb_bounded {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) : True := sorry

/-- The domain-aware Sylvester difference `X ↦ A X − X B` on partial maps, the
shape the perturbation roadmap consumes. -/
noncomputable def sylvesterPMap (A B : E →ₗ.[𝕜] E) : True := sorry

/-- Quadratic-form lower bounds transport along the graph norm: the form-bound
vocabulary consumed by the spectral-gap statements. -/
theorem quadraticForm_lowerBound_target : True := sorry

end ClosedOperators

/-! ## Part D -- resolvents of self-adjoint LinearPMap operators (T15b)

Mathlib's `spectrum`/`resolvent` are Banach-algebra notions and do not apply to
a partial map, so the resolvent set is defined here and bridged to Mathlib's in
the bounded case. -/

section Resolvents

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The resolvent set of a partial map: the points where `A − z` has a bounded
two-sided inverse. -/
def resolventSet (A : E →ₗ.[𝕜] E) : Set 𝕜 :=
  { z | ∃ R : E →L[𝕜] E,
      (∀ ψ : A.domain, R (A ψ - z • (ψ : E)) = (ψ : E)) ∧
      (∀ φ : E, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) }

/-- The named resolvent at a point of the resolvent set. -/
noncomputable def resolvent (A : E →ₗ.[𝕜] E) {z : 𝕜} (hz : z ∈ resolventSet A) :
    E →L[𝕜] E := sorry

/-- A self-adjoint partial map has every non-real point in its resolvent set. -/
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := sorry

/-- The quantitative resolvent bound `‖R z‖ ≤ |Im z|⁻¹`. -/
theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A (mem_resolventSet_of_im_ne_zero hA hz)‖ ≤ |z.im|⁻¹ := sorry

/-- The first resolvent identity on the common resolvent set. -/
theorem resolvent_sub_resolvent {A : E →ₗ.[𝕜] E} {z w : 𝕜}
    (hz : z ∈ resolventSet A) (hw : w ∈ resolventSet A) : True := sorry

end Resolvents

/-! ## Part E -- the spectral measure of an unbounded self-adjoint operator (T15c) -/

section SpectralMeasure

variable (A : H →ₗ.[ℂ] H)

/-- **The spectral theorem**: the projection-valued measure of an unbounded
self-adjoint operator, constructed through the Cayley transform. -/
noncomputable def spectralPVM (hA : IsSelfAdjoint A) : ProjValMeasure H := sorry

/-- The resolvent formula: the diagonal matrix elements of the resolvent are
Cauchy--Stieltjes transforms of the diagonal spectral measures. -/
theorem spectralPVM_resolvent_formula (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (hzr : z ∈ resolventSet A) (ξ : H) : True := sorry

/-- The unitary group generated by a self-adjoint operator, `t ↦ e^{itA}`. -/
noncomputable def genToGroup (hA : IsSelfAdjoint A) : OneParameterUnitaryGroup H := sorry

/-- **Stone's theorem, uniqueness half**: the generator of the generated group
is the operator, closing the loop with Part A. -/
theorem generator_genToGroup (hA : IsSelfAdjoint A) :
    generator (genToGroup A hA) = A := sorry

/-- Yosida approximants: bounded self-adjoint approximations converging strongly
on the domain, the bridge a Hilbert--Schmidt block argument needs. -/
noncomputable def yosidaApproximant (hA : IsSelfAdjoint A) (n : ℕ) : H →L[ℂ] H := sorry

end SpectralMeasure

end TauCetiRoadmap.SpectralTheory
