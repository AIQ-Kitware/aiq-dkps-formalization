/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-6
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation

/-!
# Davis--Kahan 1970: explicit-separation sine-theta statement

This source-facing module states a *proved inequality* with its separation
conditions expanded in the theorem signature. It
packages hypotheses already proved sufficient in
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; it does not reprove the
analytic estimate. The scalar `𝕜` can be real or complex, the spaces can be
infinite-dimensional, and `T`, `A₀`, and `Λ₁` can be unbounded.

The question for an independent expert is whether this presentation is exactly
the intended 1970 sine-theta result. In particular, the norm-class coverage,
original cosine-defined angle, and domain conventions remain review questions;
successful Lean elaboration does not settle those source-fidelity questions.

See `docs/semantic-alignment/davis-kahan-sin-theta-sme-review.md` for the
mathematical statement and the review questions.
-/

open scoped InnerProductSpace
open TauCeti.DavisKahan (IsometricEmbedding)
open TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.ExactSinTheta

namespace TauCeti.DavisKahan1970

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Davis--Kahan sine-theta bound (1970), full-scope review candidate.**

`E₀` gives trial coordinates; `F₀` gives exact desired coordinates; `F₁`
gives the orthogonal complement. The residual is `R = T E₀ - E₀ A₀` on
`dom A₀`, where `R` is a bounded extension. The exact complementary equation
is `T F₁ = F₁ Λ₁` on `dom Λ₁`. Both domain inclusions are explicit below.

The separation premise is written out in the theorem below, not hidden
behind a new alias or the library's `FormBoundedSylvesterGap` inductive.
All four spectral inclusions refer to the canonical
`_root_.LinearPMap.realSpectrum` supplied by TauCeti; they do not mention
the retired donor spectrum:

1. One real spectrum lies in `[β, α]` and the other at least `δ` outside,
   allowing either orientation.
2. `A₀` is semibounded below by `c + δ` and `Λ₁` above by `c`.
3. `A₀` is semibounded above by `c` and `Λ₁` below by `c + δ`.

These form bounds allow both diagonal blocks to be genuinely unbounded.
The proof converts the three stated alternatives to the existing library
inductive only to invoke the already-proved inequality.

`sourceDirectedSinThetaOperator E₀ F₀` is the *literal functional-calculus sine*
of the reconstructed positive directed angle on trial coordinates. It is proved
equal to the positive modulus of the projection block, but the relationship to
the paper's cosine-defined angle is an SME review point.

The inequality holds for every member of the formal normalized symmetric
operator-ideal norm family when **both** norms are defined (`N.Mem`). Whether
that family represents *every* unitarily invariant norm intended in the paper
is a distinct source-fidelity question, not certified by this wrapper. -/
theorem sinTheta_unbounded_explicitSeparation_whereDefinedUIN_rclike
    [TopologicalSpace.SeparableSpace E]
    -- Three self-adjoint operators; none is assumed bounded.
    (T : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hT : IsSelfAdjoint T) (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    -- Isometric trial and exact coordinates, orthogonality, completeness.
    (hE₀ : IsometricEmbedding E₀)
    (hF₀ : IsometricEmbedding F₀)
    (hF₁ : IsometricEmbedding F₁)
    (horth : F₀.adjoint ∘L F₁ = 0)
    (hcomplete :
      F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
        ContinuousLinearMap.id 𝕜 E)
    -- Domain-aware residual and exact complementary operator equations.
    (hE₀dom : ∀ x : A₀.domain, E₀ (x : F) ∈ T.domain)
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ T.domain)
    (hR : ∀ x : A₀.domain,
      T ⟨E₀ (x : F), hE₀dom x⟩ - E₀ (A₀ x) = R (x : F))
    (hΛ₁eq : ∀ y : Λ₁.domain,
      T ⟨F₁ (y : G), hF₁dom y⟩ = F₁ (Λ₁ y))
    {δ : ℝ} (hδ : 0 < δ)
    (hseparation :
      -- Bounded spectral interval, with the other spectrum outside the gap.
      -- Either A₀ or Λ₁ may occupy the interval.
      (∃ β α : ℝ, β ≤ α ∧
        ((_root_.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          _root_.LinearPMap.realSpectrum Λ₁ ⊆
            {t : ℝ | t ≤ β - δ ∨ α + δ ≤ t}) ∨
         (_root_.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          _root_.LinearPMap.realSpectrum A₀ ⊆
            {t : ℝ | t ≤ β - δ ∨ α + δ ≤ t}))) ∨
      -- The trial block lies above the complementary block.
      (∃ c : ℝ,
        TauCeti.LinearPMap.SemiboundedBelow A₀ (c + δ) ∧
        TauCeti.LinearPMap.SemiboundedAbove Λ₁ c) ∨
      -- The trial block lies below the complementary block.
      (∃ c : ℝ,
        TauCeti.LinearPMap.SemiboundedAbove A₀ c ∧
        TauCeti.LinearPMap.SemiboundedBelow Λ₁ (c + δ))) :
    let sinΘ₀ : F →L[𝕜] F := sourceDirectedSinThetaOperator E₀ F₀
    ∀ (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜),
      N.Mem sinΘ₀ ∧ N.Mem R →
        δ * N.gaugeReal sinΘ₀ ≤ N.gaugeReal R := by
  -- A named-field proof shows exactly which public hypotheses are bundled.
  have trialResidual : IsTrialResidual T A₀ E₀ R := {
    isometry := hE₀
    mapsDomain := hE₀dom
    residualEquation := hR
  }
  have exactDecomposition : IsExactSpectralDecomposition T Λ₁ F₀ F₁ := {
    desiredIsometry := hF₀
    complementIsometry := hF₁
    orthogonal := horth
    complete := hcomplete
    mapsDomain := hF₁dom
    intertwines := hΛ₁eq
  }
  -- Convert the explicit alternatives to the internal hypothesis of the
  -- already-proved estimate; no extra assumptions are introduced.
  have formGap : FormBoundedSylvesterGap A₀ Λ₁ δ := by
    rcases hseparation with hinterval | hordered
    · rcases hinterval with ⟨β, α, hβα, hgap⟩
      exact .intervalExterior hβα hgap
    · rcases hordered with habove | hbelow
      · rcases habove with ⟨c, hA, hB⟩
        exact .leftAboveRightBelow c hA hB
      · rcases hbelow with ⟨c, hA, hB⟩
        exact .leftBelowRightAbove c hA hB
  -- Reduce the presentation-only `let` before introducing the norm family.
  dsimp only
  intro N ⟨hsin_mem, hR_mem⟩
  exact sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    (𝕜 := 𝕜) N T A₀ Λ₁ E₀ F₀ F₁ R
    hT hA₀ hΛ₁ trialResidual exactDecomposition hδ formGap hsin_mem hR_mem

end

end TauCeti.DavisKahan1970
