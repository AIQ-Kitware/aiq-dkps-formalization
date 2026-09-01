/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Challenge
import DavisKahan.All

/-!
# Solution: the four Section 2 theorems

The Challenge states Davis and Kahan's four theorems in ordinary mathematical
vocabulary.  This module proves them from the development, and the first job is
to show that the Challenge's vocabulary *is* the development's -- not merely
analogous to it.
-/

namespace RotationOfEigenvectors

open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u v

/-! ## 1. The norm vocabulary is the development's -/

section NormBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The Challenge's singular values are the development's approximation
numbers, definitionally. -/
theorem singularValue_eq_approximationNumber (T : E →L[𝕜] F) (n : ℕ) :
    singularValue T n = T.approximationNumber n := rfl

/-- A Challenge unitarily invariant seminorm is one of the development's. -/
def UISeminorm.toTauCeti {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G) :
    TauCeti.UnitarilyInvariantSeminorm ℂ G where
  toFun := N.toFun
  add_le' := N.add_le
  smul' := N.smul
  invariant' := N.invariant

/-- The Challenge's diagonal operator is the development's. -/
theorem diagOp_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    diagOp b x = TauCeti.diagOp b x := rfl

/-- Hence so is its symmetric gauge. -/
theorem UISeminorm.gauge_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G)
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    N.gauge b x = N.toTauCeti.gauge b x := rfl

/-- **A Challenge unitarily invariant norm is a source unitarily invariant norm.**

Field for field: the finite seminorms, the normalisation and the zero-padding
axiom transfer with no adjustment, because the two definitions are the same
definition. -/
def UINorm.toPaper (N : UINorm) : PaperUnitaryInvariantNorm where
  finiteNorm n := (N.finiteNorm n).toTauCeti
  normalized := N.normalized
  zero_pad := N.zero_pad

/-- The two norms take the same value on every operator. -/
theorem UINorm.eval_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.eval T = N.toPaper.extendedGauge T := rfl

/-- The two ideals are the same ideal. -/
theorem UINorm.finite_iff (N : UINorm) (T : E →L[𝕜] F) :
    N.Finite T ↔ N.toPaper.Mem T := Iff.rfl

/-- The two real-valued norms agree. -/
theorem UINorm.norm_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.norm T = N.toPaper.gauge T := rfl

end NormBridge

/-! ## 2. The block data and the separation are the development's -/

section VocabularyBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's isometry condition is the development's. -/
theorem isIsometric_iff (T : F →L[𝕜] E) :
    IsIsometric T ↔ TauCeti.DavisKahan.IsometricEmbedding T := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's trial-residual data is the development's. -/
theorem isTrialResidual_iff (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔ _root_.DavisKahan1970.IsTrialResidual A A₀ E₀ R := by
  constructor
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩

/-- The Challenge's exact decomposition is the development's. -/
theorem isExactDecomposition_iff (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) :
    IsExactDecomposition A Λ₁ F₀ F₁ ↔
      _root_.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ := by
  constructor
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩

omit [CompleteSpace E] in
/-- The Challenge's real resolvent set is the development's. -/
theorem realResolventSet_eq (A : E →ₗ.[𝕜] E) :
    realResolventSet A = TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff]
  rfl

omit [CompleteSpace E] in
/-- Hence so is the real spectrum. -/
theorem realSpectrum_eq (A : E →ₗ.[𝕜] E) :
    realSpectrum A = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, realSpectrum, Set.mem_compl_iff,
    realResolventSet_eq]

omit [CompleteSpace E] in
/-- The Challenge's lower form bound is the development's. -/
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔ TauCeti.LinearPMap.SemiboundedBelow A c := by
  rw [TauCeti.LinearPMap.semiboundedBelow_iff]
  exact Iff.rfl

omit [CompleteSpace E] in
/-- The Challenge's upper form bound is the development's. -/
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔ TauCeti.LinearPMap.SemiboundedAbove A c := by
  rw [TauCeti.LinearPMap.semiboundedAbove_iff]
  exact Iff.rfl

/-- **The Challenge's separation is the development's**, constructor by
constructor -- including both half-infinite configurations. -/
theorem sylvesterGap_iff (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) :
    SylvesterGap A B δ ↔ FormBoundedSylvesterGap A B δ := by
  constructor
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap, ← realSpectrum_eq, ← realSpectrum_eq]
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).1 hA)
        ((semiboundedAbove_iff _ _).1 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).1 hA)
        ((semiboundedBelow_iff _ _).1 hB)
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap] at hgap
      rw [← realSpectrum_eq, ← realSpectrum_eq] at hgap
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).2 hA)
        ((semiboundedAbove_iff _ _).2 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).2 hA)
        ((semiboundedBelow_iff _ _).2 hB)

end VocabularyBridge

/-! ## 3. The `sin Θ` theorem

Every Challenge object above is the development's, so the Challenge statement is
the development's statement.  What is left is the scalar field: the development
proves this at `ℝ` and at `ℂ`, and its `RCLike`-generic form carries two
capability binders that are instances at exactly those two fields. -/

section SinTheta

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The Challenge's `sin Θ` statement, discharged from the development.**

The two binders are the development's proof capabilities, not source hypotheses:
the unbounded Sylvester Ky Fan estimate and the min--max lower bound.  Both are
instances at `ℝ` and at `ℂ`, so at either of the paper's fields this theorem is
the Challenge statement with nothing assumed. -/
theorem sinTheta_of_capabilities
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R :=
  _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike
    N.toPaper A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
    ((isTrialResidual_iff A A₀ E₀ R).1 hres)
    ((isExactDecomposition_iff A Λ₁ F₀ F₁).1 hdec)
    hδ ((sylvesterGap_iff A₀ Λ₁ δ).1 hgap) hR

end SinTheta

/-! ## 4. The two capability classes at the paper's fields -/

section Capabilities

/-- Both capabilities are instances at `ℂ`. -/
example : ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{0, v} ℂ := inferInstance

example : HasUnboundedSylvesterKyFan.{0, v} ℂ := inferInstance

/-- And at `ℝ`. -/
example : ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{0, v} ℝ := inferInstance

example : HasUnboundedSylvesterKyFan.{0, v} ℝ := inferInstance

end Capabilities

/-! ## 5. Status of the remaining three theorems

This file is a **feasibility candidate**, not a finished submission, and the
honest state of each of the four is recorded here rather than papered over with
an axiom or a `sorry` on the Solution side.

**`sinTheta` — proved, modulo the scalar field.**  `sinTheta_of_capabilities`
above *is* the Challenge statement, discharged from
`DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`.  At `ℂ` and at
`ℝ` the two capability binders are found by instance search, so at either of the
paper's own fields the Challenge theorem holds with nothing assumed.  What is
missing for the `[RCLike 𝕜]` statement is exactly:

    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜
    HasUnboundedSylvesterKyFan 𝕜

for an arbitrary `RCLike` field.  These are *proof capabilities of the
development*, not source hypotheses, and they are not a Palomar problem: they are
a Solution-side obligation.  Mathlib now supplies the dispatch they would be
proved by -- `RCLike.I_eq_zero_or_im_I_eq_one` with `RCLike.realLinearIsometryEquiv`
and `RCLike.complexLinearIsometryEquiv` -- so what remains is transporting a
Hilbert space, its partial maps, its gap predicate and its Ky Fan gauges along a
scalar-field isometry.  That is a bounded piece of work and it would discharge
both classes once for every theorem here.

**`sinTwoTheta` — the ambient clause has a matching endpoint; the directed clause
is stated too strongly.**  The ambient clause corresponds to
`sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`, up to one
missing development lemma: that reflection through a subspace *reducing* the
perturbed operator preserves the unperturbed domain and intertwines, which the
development currently proves only for a *spectral* subspace
(`add_reflectionPerturbation_intertwines`).  The directed clause as stated here
quantifies over an arbitrary reducing subspace, while the development's directed
residual endpoint selects its subspace from a measurable spectral set.  The
Challenge is therefore *stronger* than what is proved, and the honest repair is
either to prove the directed endpoint for an arbitrary reducing subspace or to
weaken the clause -- **not** to leave it as a claim.

**`tanTheta`, `tanTwoTheta` — statements written, correspondence not attempted.**
Their development endpoints exist at both fields
(`tanTheta_directed_unboundedTrial_paperUINorm_*`,
`tanTheta_ambient_unboundedRitz_paperUINorm_*`,
`tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_*`,
`tanTwoTheta_ambient_unbounded_paperUINorm_*`), and the tangent characterisation
used here is the development's own
(`HasTheorem63DirectedTangentApproximationNumbersInfinite`), so the shapes match;
the mapping has simply not been carried out.

What this file does establish is the part that was in doubt: the Challenge's
vocabulary is not an approximation of the development's, it *is* the
development's, and the norm -- the object most at risk of being quietly weakened
in a compact restatement -- corresponds by `rfl`. -/

end

end RotationOfEigenvectors
