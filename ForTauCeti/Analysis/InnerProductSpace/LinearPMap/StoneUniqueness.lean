/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
public import ForTauCeti.Analysis.Semigroups.Group.ComplexOperator

/-!
# The native Stone generator of the Yosida limit group

`genToGroup hA` constructs a native strongly continuous unitary group from the
explicit Yosida strong limit. This module proves that its native Stone
generator is `A`. Tau Ceti already supplies abstract Stone existence and group
uniqueness; the analysis here identifies the generator of this particular
limit, using its integral identity.

## Why only one inclusion has to be proved

`(genToGroup hA).val.stoneGenerator (genToGroup hA).property` is self-adjoint by
`StronglyContinuousGroup.isSelfAdjoint_stoneGenerator` (Stone's forward direction),
and `eq_of_le_of_isSelfAdjoint` says a self-adjoint operator has no proper
self-adjoint extension. The inclusion of `A` in that native Stone generator gives
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

## Provenance

* **Original repository:** none — **authored in place** in the AIQ DKPS
  formalization (`https://github.com/AIQ-Kitware/aiq-dkps-formalization`),
  commit `c9c8502c`, for staging into Tau Ceti.
* **Original module:** none; written directly at this path.
* **Original authors / copyright / licence:** Copyright (c) 2026 Kitware, Inc.;
  `Authors: Jon Crall, Claude Opus 5`; Apache 2.0 (this repository's `LICENSE`).
  No third-party code is incorporated, so no donor notice is carried.
* **Extraction class:** *authored in place*, for upstreaming to Tau Ceti.
* **Relation to existing libraries:** the uniqueness half of Stone's theorem for
  the explicit Yosida limit of a self-adjoint `LinearPMap`. The native Stone
  theorem now supplies self-adjointness. Only one inclusion is proved: its generator is
  self-adjoint by the forward direction, and a self-adjoint operator admits no
  proper self-adjoint extension, so the forward graph inclusion already
  gives equality — the reverse inclusion, which would need a description of the
  generator's domain, is never required.
* **Semantic differences from a donor:** not applicable.
-/

public section

open scoped InnerProductSpace
open TauCeti.Semigroups.StronglyContinuousGroup (ofBoundedExp stoneDiffQuot_apply)
open Filter Topology Complex MeasureTheory intervalIntegral

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

/-! ### The bounded case: an exact integral identity -/

/-- `s ↦ exp(s • B) ψ` is continuous. -/
@[simp]
theorem continuous_expTime_apply (B : H →L[ℂ] H) (ψ : H) :
    Continuous fun s : ℝ => expTime B s ψ := by
  have hdiff : Differentiable ℝ fun s : ℝ => expTime B s ψ := fun s =>
    (hasDerivAt_expTime_apply B ψ s).differentiableAt
  exact hdiff.continuous

/-- **The exact integral identity for a bounded generator.** -/
@[simp]
theorem integral_expTime_apply (B : H →L[ℂ] H) (ψ : H) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, expTime B s (B ψ)) = expTime B t ψ - ψ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => expTime B s ψ) (expTime B s (B ψ)) s :=
    fun s _ => hasDerivAt_expTime_apply B ψ s
  have hint : IntervalIntegrable (fun s : ℝ => expTime B s (B ψ)) volume 0 t :=
    (continuous_expTime_apply B (B ψ)).intervalIntegrable 0 t
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-! ### Passing the identity to the limit -/

/-- The identity, for the Yosida approximants. -/
theorem integral_yosidaFlow (n : ℕ+) (ψ : H) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (I : ℂ) • ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) s
      (A.symmetricYosidaApproximation (n : ℝ) ψ))
      = ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t ψ - ψ := by
  have h := integral_expTime_apply ((I : ℂ) • A.symmetricYosidaApproximation (n : ℝ)) ψ t
  simp only [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  simpa only [expTime_def, Complex.coe_smul, smul_apply, map_smul] using h

/-- **The integral identity for the limit flow.**  The approximants converge
pointwise in `s` and are bounded by a constant, because a convergent sequence of
vectors is bounded and each native bounded flow is unitary. -/
theorem integral_expLimit (hA : IsSelfAdjoint A) {ψ : H} (hψ : ψ ∈ A.domain) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩)) = expLimit hA t ψ - ψ := by
  let V (n : ℕ+) := ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ))
  have hconv :=
    ((hA.tendsto_symmetricYosidaApproximation_apply ⟨ψ, hψ⟩).mono_left
      atTop_le_cocompact).comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
  -- a uniform bound on the approximant images
  have hnorm : Tendsto (fun n : ℕ+ => ‖A.symmetricYosidaApproximation (n : ℝ) ψ‖)
      atTop (𝓝 ‖A ⟨ψ, hψ⟩‖) :=
    hconv.norm
  set C : ℝ := ‖A ⟨ψ, hψ⟩‖ + 1 with hCdef
  have hCle : ∀ᶠ n : ℕ+ in atTop, ‖A.symmetricYosidaApproximation (n : ℝ) ψ‖ ≤ C :=
    hnorm.eventually_le_const (by rw [hCdef]; linarith)
  -- the integrands converge pointwise
  have hlim : ∀ s : ℝ, Tendsto
      (fun n : ℕ+ => (I : ℂ) • V n s
        (A.symmetricYosidaApproximation (n : ℝ) ψ)) atTop
      (𝓝 ((I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩))) := by
    intro s
    refine Filter.Tendsto.const_smul ?_ (I : ℂ)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsplit : ∀ n : ℕ+,
        ‖V n s (A.symmetricYosidaApproximation
          (n : ℝ) ψ) - expLimit hA s (A ⟨ψ, hψ⟩)‖
          ≤ ‖A.symmetricYosidaApproximation (n : ℝ) ψ - A ⟨ψ, hψ⟩‖
            + ‖V n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := by
      intro n
      calc ‖V n s
            (A.symmetricYosidaApproximation (n : ℝ) ψ) - expLimit hA s (A ⟨ψ, hψ⟩)‖
          = ‖V n s
            (A.symmetricYosidaApproximation (n : ℝ) ψ - A ⟨ψ, hψ⟩)
              + (V n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩))‖ := by
            rw [map_sub]; congr 1; abel
        _ ≤ ‖V n s
          (A.symmetricYosidaApproximation (n : ℝ) ψ - A ⟨ψ, hψ⟩)‖
              + ‖V n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := norm_add_le _ _
        _ = ‖A.symmetricYosidaApproximation (n : ℝ) ψ - A ⟨ψ, hψ⟩‖
              + ‖V n s (A ⟨ψ, hψ⟩) - expLimit hA s (A ⟨ψ, hψ⟩)‖ := by
            rw [(Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation _)).norm_map]
    refine squeeze_zero (fun n => norm_nonneg _) hsplit ?_
    have h1 : Tendsto (fun n : ℕ+ => ‖A.symmetricYosidaApproximation (n : ℝ) ψ - A ⟨ψ, hψ⟩‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hconv
    have h2 : Tendsto
        (fun n : ℕ+ => ‖V n s (A ⟨ψ, hψ⟩) -
          expLimit hA s (A ⟨ψ, hψ⟩)‖)
        atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_expLimitFun hA s (A ⟨ψ, hψ⟩))
    simpa using h1.add h2
  -- dominated convergence
  have hint : Tendsto
      (fun n : ℕ+ => ∫ s in (0 : ℝ)..t,
        (I : ℂ) • V n s
          (A.symmetricYosidaApproximation (n : ℝ) ψ))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun n =>
        ((((V n).continuous_orbit
          (A.symmetricYosidaApproximation (n : ℝ) ψ)).const_smul
          (I : ℂ)).aestronglyMeasurable)
    · filter_upwards [hCle] with n hn
      refine Eventually.of_forall fun s _ => ?_
      rw [norm_smul, Complex.norm_I, one_mul,
        (Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation _)).norm_map]
      exact hn
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s _ => hlim s
  -- and the right-hand sides converge too
  have hrhs : Tendsto (fun n : ℕ+ => V n t ψ -
    ψ) atTop
      (𝓝 (expLimit hA t ψ - ψ)) :=
    (tendsto_expLimitFun hA t ψ).sub tendsto_const_nhds
  refine tendsto_nhds_unique hint ?_
  refine hrhs.congr fun n => ?_
  exact (integral_yosidaFlow n ψ t).symm

/-- The difference quotient of the limit flow converges to `A ψ` on the domain:
the integral identity turns it into the *average* of a continuous integrand. -/
theorem tendsto_stoneDiffQuot_genToGroup (hA : IsSelfAdjoint A) {ψ : H} (hψ : ψ ∈ A.domain) :
    Tendsto ((genToGroup hA).val.stoneDiffQuot ψ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (A ⟨ψ, hψ⟩)) := by
  set g : ℝ → H := fun s => (I : ℂ) • expLimit hA s (A ⟨ψ, hψ⟩) with hg
  have hgcont : Continuous g := (continuous_expLimit hA (A ⟨ψ, hψ⟩)).const_smul (I : ℂ)
  have hg0 : g 0 = (I : ℂ) • A ⟨ψ, hψ⟩ := by rw [hg]; simp
  have hderiv : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, g s) ((I : ℂ) • A ⟨ψ, hψ⟩) 0 := by
    have h := (hgcont.integral_hasStrictDerivAt 0 0).hasDerivAt
    rwa [hg0] at h
  have hderiv' : HasDerivAt (fun u : ℝ => expLimit hA u ψ - ψ) ((I : ℂ) • A ⟨ψ, hψ⟩) 0 := by
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards with u
    exact (integral_expLimit hA hψ u).symm
  rw [hasDerivAt_iff_tendsto_slope] at hderiv'
  have hres := hderiv'.const_smul (-(I : ℂ))
  have hval : (-(I : ℂ)) • ((I : ℂ) • A ⟨ψ, hψ⟩) = A ⟨ψ, hψ⟩ := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [hval] at hres
  refine hres.congr fun t => ?_
  have hf0 : expLimit hA 0 ψ - ψ = 0 := by rw [expLimit_zero]; simp
  simp only [slope_def_module, hf0, sub_zero,
    stoneDiffQuot_apply, genToGroup]
  have hcast : (t⁻¹ : ℝ) • ((expLimit hA t) ψ - ψ)
      = (((t : ℂ))⁻¹) • ((expLimit hA t) ψ - ψ) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (t⁻¹ : ℝ) ((expLimit hA t) ψ - ψ)]
    norm_cast
  rw [hcast, smul_smul, mul_inv, Complex.inv_I]
  rfl

/-! ### The derivative at zero, and the identification -/

/-- **Stone's theorem, uniqueness half.**  The generator of the unitary group of
a self-adjoint operator is that operator again. -/
theorem stoneGenerator_genToGroup (hA : IsSelfAdjoint A) :
    (genToGroup hA).val.stoneGenerator (genToGroup hA).property = A := by
  refine (_root_.LinearPMap.eq_of_le_of_isSelfAdjoint hA
    ((genToGroup hA).val.isSelfAdjoint_stoneGenerator (genToGroup hA).property) ?_).symm
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · -- the domain inclusion, which is the same limit computation
    exact (genToGroup hA).val.mem_stoneGenerator_domain_of_tendsto
      (genToGroup hA).property (tendsto_stoneDiffQuot_genToGroup hA hψ)
  · rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ hEq
    simp only at hEq
    subst hEq
    exact (tendsto_nhds_unique
      ((genToGroup hA).val.tendsto_stoneDiffQuot (genToGroup hA).property ⟨ψ, hψ'⟩)
      (tendsto_stoneDiffQuot_genToGroup hA hψ)).symm

end LinearPMap
end TauCeti
