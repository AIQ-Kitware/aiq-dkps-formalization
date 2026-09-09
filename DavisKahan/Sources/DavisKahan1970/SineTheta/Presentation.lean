/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.SineThetaSourceInventory
import DavisKahan.SinTheta.Canonical
import DavisKahan.SinTheta.Real.Canonical
import DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

open TauCeti.DavisKahan.Sylvester

/-!
# The Davis--Kahan 1970 sine-theta theorem family

This module contains both the stronger symmetric-norming implementation theorems and the
fixed-field where-defined norm declarations currently selected by the result ledger.
Source fidelity is a property recorded by that ledger, not by theorem names.

`sinTheta_unbounded_formGap_symmetricNorming_rclike` is the scalar-generic implementation
API.  It proves ideal membership together with the inequality for every
`SymmetricNormingFunction`.  The later source review found that membership transfer is extra
structure relative to Davis--Kahan's convention that a displayed unitarily invariant norm
statement is vacuous when either norm is undefined.

The ledger points to the scalar-generic
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike`.  It exposes ambient separability and
states only the where-defined inequality.  The complex and real declarations are thin
specializations of that theorem rather than independent source-fidelity boundaries.

Presentation forms that inline one gap branch or expose an explicit `sinTheta₀` parameter
remain useful for review and compatibility, but they are not substitutes for the ledger.
-/
namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


open scoped InnerProductSpace

noncomputable section

universe u v

open TauCeti.DavisKahan

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The trial-coordinate part of the Davis--Kahan Section 2 setup.

`E₀` is an isometric coordinate map for the trial subspace and `R` is exactly
the residual `A E₀ - E₀ A₀` on the domain of the possibly unbounded trial
operator `A₀`. -/
structure IsTrialResidual
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) : Prop where
  isometry : IsometricEmbedding E₀
  mapsDomain : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain
  residualEquation : ∀ x : A₀.domain,
    A ⟨E₀ (x : F), mapsDomain x⟩ -
      E₀ (A₀ x) = R (x : F)

/-- The trial residual *relation* alone: `E₀` carries `dom A₀` into `dom A`, and
`R` is the residual `A E₀ − E₀ A₀` there.

This is `IsTrialResidual` with the isometry dropped, and it is the half the
Section 6 generalized theorems share with the Section 2 sine theorem.  Section 2
asks for an isometric trial map; Theorems 6.1 and 6.2 ask only for a lower frame
bound `LowerFrameBound E₀ ε`, which an isometry satisfies with `ε = 1` but which
a general trial map satisfies with a smaller constant -- and that constant is the
factor the printed generalized bound carries.  Splitting the predicate is what
lets both surfaces take the same residual hypothesis without either of them
being over- or under-strengthened. -/
structure IsTrialResidualEquation
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) : Prop where
  mapsDomain : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain
  residualEquation : ∀ x : A₀.domain,
    A ⟨E₀ (x : F), mapsDomain x⟩ -
      E₀ (A₀ x) = R (x : F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `IsTrialResidual` is exactly the residual relation together with the
isometry.  The Section 2 API is unchanged; this records the decomposition. -/
theorem isTrialResidual_iff_equation_and_isometry
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔
      IsTrialResidualEquation A A₀ E₀ R ∧ IsometricEmbedding E₀ := by
  constructor
  · intro h
    exact ⟨⟨h.mapsDomain, h.residualEquation⟩, h.isometry⟩
  · rintro ⟨he, hiso⟩
    exact ⟨hiso, he.mapsDomain, he.residualEquation⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- The residual relation underlying a Section 2 trial residual. -/
theorem IsTrialResidual.toEquation
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E}
    (h : IsTrialResidual A A₀ E₀ R) : IsTrialResidualEquation A A₀ E₀ R :=
  ⟨h.mapsDomain, h.residualEquation⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- Fully expanded mathematical meaning of `IsTrialResidual`. -/
theorem isTrialResidual_iff
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔
      IsometricEmbedding E₀ ∧
        ∃ hdom : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain,
          ∀ x : A₀.domain,
            A ⟨E₀ (x : F), hdom x⟩ -
              E₀ (A₀ x) = R (x : F) := by
  constructor
  · intro h
    exact ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · rintro ⟨hE₀, hdom, heq⟩
    exact ⟨hE₀, hdom, heq⟩

/-- The exact spectral-coordinate part of the Section 2 sine theorem.

`F₀` represents the desired exact subspace, while `F₁` represents its
orthogonal complement.  The complementary coordinates intertwine the ambient
operator `A` with the exact complementary block `Λ₁`. -/
structure IsExactSpectralDecomposition
    (A : E →ₗ.[𝕜] E)
    (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E) : Prop where
  desiredIsometry : IsometricEmbedding F₀
  complementIsometry : IsometricEmbedding F₁
  orthogonal : F₀.adjoint ∘L F₁ = 0
  complete :
    F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
      ContinuousLinearMap.id 𝕜 E
  mapsDomain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), mapsDomain y⟩ =
      F₁ (Λ₁ y)

/-- Fully expanded mathematical meaning of `IsExactSpectralDecomposition`. -/
theorem isExactSpectralDecomposition_iff
    (A : E →ₗ.[𝕜] E)
    (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E) :
    IsExactSpectralDecomposition A Λ₁ F₀ F₁ ↔
      IsometricEmbedding F₀ ∧
        IsometricEmbedding F₁ ∧
          F₀.adjoint ∘L F₁ = 0 ∧
            F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
              ContinuousLinearMap.id 𝕜 E ∧
            ∃ hdom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain,
              ∀ y : Λ₁.domain,
                A ⟨F₁ (y : G), hdom y⟩ =
                  F₁ (Λ₁ y) := by
  constructor
  · intro h
    exact ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal,
      h.complete, h.mapsDomain, h.intertwines⟩
  · rintro ⟨hF₀, hF₁, horth, hcomplete, hdom, hintertwines⟩
    exact ⟨hF₀, hF₁, horth, hcomplete, hdom, hintertwines⟩

/-- **Davis--Kahan 1970, Section 2 sine-theta theorem, presentation form.**

**Not the theorem to cite.**  The result ledger now selects
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; this presentation form is kept because its
explicit `sinTheta₀` parameter makes the printed inequality legible in the
signature, and because callers already depend on it.

It is generic over `RCLike 𝕜`, so it retains the real/complex and
infinite-dimensional scope of the proved headline theorem, but its separation
hypothesis is only the interval/exterior branch of `FormBoundedSylvesterGap`, so
it states a strictly smaller theorem.

The source object `sinTheta₀` is an explicit parameter, and `hSinTheta₀` states
its concrete realization `(I - F₀ F₀*) E₀` in the theorem signature.  The
claim after the colon is therefore the printed factor-one inequality itself.
The stronger supporting theorem `sinTheta_unbounded_intervalExterior_symmetricNorming_rclike` additionally
certifies membership of this operator in the source norm ideal. -/
theorem sinTheta_unbounded_intervalExterior_characterizedWitness_rclike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E)
    (sinTheta₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hSinTheta₀ :
      sinTheta₀ =
        (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hδ : 0 < δ)
    (hspectral :
      (LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    δ * N.gauge sinTheta₀ ≤ N.gauge R := by
  have hfull := TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_rclike
    N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
    htrial.isometry hexact.desiredIsometry hexact.complementIsometry
    hexact.orthogonal hexact.complete htrial.mapsDomain hexact.mapsDomain
    htrial.residualEquation hexact.intertwines hβα hδ hspectral hR
  rw [← hSinTheta₀] at hfull
  exact hfull.2

/-! ## Scalar-generic implementation and fixed-field statement boundaries

`sinTheta_unbounded_formGap_symmetricNorming_rclike` below is the scalar-generic
implementation theorem. It is stronger than the current ledger-selected boundary:
it quantifies over `SymmetricNormingFunction`, requires residual membership, and
concludes membership transfer. The fixed-field where-defined wrappers later in
this file expose the current source norm convention directly. A matching `RCLike`
where-defined wrapper is tested in the standalone Fan-dominance probe before any
short public alias is rebound.

`sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` above is the
presentation declaration, and it inlines the finite interval/exterior branch of
the separation.  `FormBoundedSylvesterGap` is the general form-bounded gap, and
the interval/exterior configuration is one of its constructors
(`FormBoundedSylvesterGap.intervalExterior`); the ordered half-line
configurations the Appendix needs are others.  Stating the headline with the
interval branch inlined therefore fixes a strictly smaller theorem than the one
that is proved.

The result ledger, rather than any declaration name or this module comment, records
which fixed-field declarations currently witness source fidelity. -/

/-- **Davis--Kahan 1970, the `sin Theta` theorem, over an arbitrary `RCLike` field.**

This is the scalar-generic implementation theorem used by the Section 2 sine
development. It has the full unbounded operator and `FormBoundedSylvesterGap`
scope, but its `SymmetricNormingFunction` membership-transfer boundary is stronger
than the where-defined norm convention currently selected by the result ledger.

`IsTrialResidual` and `IsExactSpectralDecomposition` are the same two structural
predicates the complex and real statements take, and they were already
scalar-generic; `isTrialResidual_iff` and `isExactSpectralDecomposition_iff`
expand them.

The analytic capabilities consumed by the proof hold at every `RCLike` field and
reach it by instance search. This theorem remains an implementation API while the
where-defined scalar-generic wrapper is validated separately. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_ofComponents_rclike
    N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial.isometry hexact.desiredIsometry
    hexact.complementIsometry hexact.orthogonal hexact.complete
    htrial.mapsDomain hexact.mapsDomain htrial.residualEquation
    hexact.intertwines hδ hgap hR

/-- **Davis--Kahan 1970, the `sin Theta` theorem at the where-defined norm boundary,
scalar-generic over `RCLike`.**

This is the production form of the scalar-generic endpoint validated by the Fan-dominance
exploration.  It exposes the paper's separable ambient scope and normalized symmetric
operator-ideal norm family, but does not turn Ky Fan dominance into a membership-transfer
claim.  The displayed inequality is asserted exactly where both norms are defined. -/
theorem sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) →
    N.Mem R →
      δ * N.gaugeReal ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gaugeReal R := by
  change N.ScaledGaugeLEWhereDefined δ
    ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) R
  apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le hδ
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hmain :=
      sinTheta_unbounded_formGap_symmetricNorming_rclike
        (𝕜 := 𝕜) (kyFanNormingFunction k hk) A A₀ Λ₁ E₀ F₀ F₁ R
        hA hA₀ hΛ₁ htrial hexact hδ hgap
        (kyFanNormingFunction_mem k hk R)
    simpa only [kyFanNormingFunction_gauge] using hmain.2

section FixedField

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the sine-theta theorem, over `ℂ`.**

For an unbounded self-adjoint ambient operator `A`, a trial pair `(A₀, E₀)` with
domain-aware residual `R`, an exact complementary spectral decomposition
`(Λ₁, F₀, F₁)`, and a form-bounded Sylvester gap `δ` between the trial and
complementary spectra, the sine of the angle between the trial and desired
subspaces is controlled by the residual in every source unitarily invariant
norm:

`δ · N(sin Θ₀) ≤ N(R)`, where `sin Θ₀ = (1 − F₀F₀*) E₀`.

The theorem also concludes that `sin Θ₀` lies in the norm's ideal, which in
infinite dimension is part of the statement rather than a side condition.

This is the full gap scope: `FormBoundedSylvesterGap` covers the interval and
exterior configuration of Section 2 and the ordered half-line configurations of
the Appendix alike. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hR ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmain :=
      FormBoundedIsometricSinThetaProblem.result_complex
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos)
        { data :=
            { A := A, A₀ := A₀, Λ₁ := Λ₁, X := E₀, F₁ := F₁, residual := R
              X_maps_domain := htrial.mapsDomain
              F₁_maps_domain := hexact.mapsDomain
              residual_eq := htrial.residualEquation
              intertwines := hexact.intertwines }
          exactMap := F₀
          ambient_selfAdjoint := hA
          trial_selfAdjoint := hA₀
          complement_selfAdjoint := hΛ₁
          trial_isometry := htrial.isometry
          exact_decomposition :=
            { isometry₀ := hexact.desiredIsometry
              isometry₁ := hexact.complementIsometry
              orthogonal := hexact.orthogonal
              projection_sum := hexact.complete }
          gap := δ
          gap_pos := hδ
          spectral_gap := hgap
          residual_mem := KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hkpos R }
    simpa only [KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

/-- **Conformance: the complex endpoint is the scalar-generic one at `𝕜 = ℂ`.**

This restates `sinTheta_unbounded_formGap_symmetricNorming_complex`'s type verbatim --
same data, same structural predicates, same full `FormBoundedSylvesterGap`, same
`SymmetricNormingFunction`, same ideal membership, same factor-one inequality --
and discharges it by applying `sinTheta_unbounded_formGap_symmetricNorming_rclike`
with no adapter.  If any hypothesis or the conclusion differed mathematically,
this would not elaborate.

The generic theorem carries no capability class, so this is a plain
instantiation. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_unbounded_formGap_symmetricNorming_rclike N A A₀ Λ₁ E₀ F₀ F₁ R
    hA hA₀ hΛ₁ htrial hexact hδ hgap hR

/-- **The familiar Section 2 interval form, over `ℂ`.**

`sinTheta_unbounded_formGap_symmetricNorming_complex` with the gap spelled out as the printed separation: the
trial spectrum inside `[β, α]` and the complementary spectrum outside
`(β − δ, α + δ)`, or the same with the two roles exchanged.  This is one
constructor of `FormBoundedSylvesterGap`; the Appendix's ordered half-line
configurations are others, and they reach the theorem above directly. -/
theorem sinTheta_unbounded_intervalExterior_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hspectral :
      (TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (TauCeti.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_unbounded_formGap_symmetricNorming_complex N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα hspectral) hR

/-! ### The where-defined normalized-UIN boundary

Davis and Kahan work on a separable Hilbert space and use the convention that a
displayed norm comparison is vacuous when a norm does not exist.  These declarations
expose that weaker norm boundary directly.  The result ledger records whether a given
declaration is the current fidelity witness; the theorem name does not.

Only the ambient space carries separability, because that is all the source assumes. -/

/-- **Davis--Kahan 1970, the sine-theta theorem, at the printed source scope over
`ℂ`.**

Separable ambient Hilbert space, arbitrary normalized symmetric operator ideal
family, unbounded self-adjoint ambient operator, and the full form-bounded gap.
The conclusion implements the paper's convention that a displayed norm
comparison is vacuous when either norm does not exist: whenever both norms are
defined, `δ · N(sin Θ₀) ≤ N(R)`.

No residual-membership hypothesis and no membership-transfer conclusion appear
at this source-facing boundary.  The two `N.Mem` arrows are written literally
after the colon: they are the logical form of the paper's vacuity convention,
not hypotheses required to invoke the theorem. -/
theorem sinTheta_unbounded_formGap_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) →
    N.Mem R →
      δ * N.gaugeReal ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gaugeReal R :=
  sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    (𝕜 := ℂ) N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

end FixedField

section FixedFieldReal

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the sine-theta theorem, over `ℝ`.**

The real-scalar sibling of `sinTheta_unbounded_formGap_symmetricNorming_complex`, with the same argument list and
the same full gap scope.  The real proof descends from the complex one by
complexification inside `result_real`; the descent is not visible here. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hR ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmain :=
      FormBoundedIsometricSinThetaProblem.result_real
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hkpos)
        { data :=
            { A := A, A₀ := A₀, Λ₁ := Λ₁, X := E₀, F₁ := F₁, residual := R
              X_maps_domain := htrial.mapsDomain
              F₁_maps_domain := hexact.mapsDomain
              residual_eq := htrial.residualEquation
              intertwines := hexact.intertwines }
          exactMap := F₀
          ambient_selfAdjoint := hA
          trial_selfAdjoint := hA₀
          complement_selfAdjoint := hΛ₁
          trial_isometry := htrial.isometry
          exact_decomposition :=
            { isometry₀ := hexact.desiredIsometry
              isometry₁ := hexact.complementIsometry
              orthogonal := hexact.orthogonal
              projection_sum := hexact.complete }
          gap := δ
          gap_pos := hδ
          spectral_gap := hgap
          residual_mem := KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℝ) k hkpos R }
    simpa only [KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

/-- **The familiar Section 2 interval form, over `ℝ`.**

`sinTheta_unbounded_formGap_symmetricNorming_real` with the gap spelled out as the printed separation: the
trial spectrum inside `[β, α]` and the complementary spectrum outside
`(β − δ, α + δ)`, or the same with the two roles exchanged.  This is one
constructor of `FormBoundedSylvesterGap`; the Appendix's ordered half-line
configurations are others, and they reach the theorem above directly. -/
theorem sinTheta_unbounded_intervalExterior_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hspectral :
      (TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (TauCeti.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_unbounded_formGap_symmetricNorming_real N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα hspectral) hR

/-- **Conformance: the real endpoint is the scalar-generic one at `𝕜 = ℝ`.**

The real twin of `sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike`, and
the more informative of the two: the real endpoint's own proof descends from the
complex one by complexification, while this one reaches the same statement
directly from the scalar-generic engine.  Both routes therefore land on the same
type. -/
theorem sinTheta_unbounded_formGap_symmetricNorming_real_ofRCLike
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_unbounded_formGap_symmetricNorming_rclike N A A₀ Λ₁ E₀ F₀ F₁ R
    hA hA₀ hΛ₁ htrial hexact hδ hgap hR

/-- **Davis--Kahan 1970, the sine-theta theorem, at the printed source scope over
`ℝ`.**

The real sibling of `sinTheta_unbounded_formGap_whereDefinedUIN_complex`, with the
same partial-norm/vacuity boundary and the same explicit `Mem → Mem →`
conclusion shape. -/
theorem sinTheta_unbounded_formGap_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) →
    N.Mem R →
      δ * N.gaugeReal ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gaugeReal R :=
  sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    (𝕜 := ℝ) N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

end FixedFieldReal


/-! ### The conformance is tied to the fixed-field declarations by name

`..._ofRCLike` restates a type; on its own that is a *copy*, and a copy cannot
notice if the declaration it claims to mirror changes.  The two equations below
close that hole.  An equation between two constants elaborates only if both sides
have the same type, so `@sinTheta_unbounded_formGap_symmetricNorming_complex =
@sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike` is exactly the assertion
that the restatement is the endpoint's type; `rfl` then discharges it by proof
irrelevance.  If either endpoint's statement changes, these stop elaborating.

What they do *not* say: anything about the two proofs.  Proof irrelevance makes
any two proofs of one `Prop` equal, so this is a type-level check by design. -/

theorem sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike_conforms :
    @sinTheta_unbounded_formGap_symmetricNorming_complex
      = @sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike := rfl

theorem sinTheta_unbounded_formGap_symmetricNorming_real_ofRCLike_conforms :
    @sinTheta_unbounded_formGap_symmetricNorming_real
      = @sinTheta_unbounded_formGap_symmetricNorming_real_ofRCLike := rfl

end

end DavisKahan1970
end TauCeti
