/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-6 (configuration undetermined)
-/

/-
# Section 2 source UIN conformance probes

This maintained standalone file checks the scalar-generic, where-defined `sin Θ`
and `sin 2Θ` endpoints against the current source-facing Davis--Kahan API. The
older 47-probe exploration is preserved under `Explorations/Historical/`; its
proofs were written against APIs retired during the Tau Ceti migrations.

Compile with `lake env lean DavisKahan/Explorations/SourceUnitaryInvariantNormFanDominance.lean`.
-/

import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
import DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedRCLike
import DavisKahan.Sources.DavisKahan1970.SectionTwo

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace SourceUINConformance

open scoped ENNReal InnerProductSpace TauCeti.CompleteSubspace

noncomputable section

universe u v

/-- **Probe 44: the repaired sine-theta norm boundary is available at arbitrary
`RCLike` scalar field.**

This is the scalar-generic counterpart of the fixed-field where-defined wrappers:
no residual-membership premise is needed to invoke the theorem, and no membership
transfer is concluded.  The two `N.Mem` arrows are the source's convention that
the displayed inequality is asserted where both partial norms are defined. -/
theorem sinTheta_unbounded_formGap_whereDefinedUIN_rclike_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    N.Mem (TauCeti.DavisKahan1970.sourceDirectedSinThetaOperator E₀ F₀) →
    N.Mem R →
      δ * N.gaugeReal (TauCeti.DavisKahan1970.sourceDirectedSinThetaOperator E₀ F₀) ≤
        N.gaugeReal R := by
  exact TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    (𝕜 := 𝕜) N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

/-- **Probe 45: the ambient `sin 2Θ` clause has the same where-defined RCLike
boundary.**

The existing analytic theorem is already scalar-generic.  This probe changes only
the norm boundary, using every Ky Fan norm and then where-defined Fan dominance.
The factor two is handled by proving the equivalent `(δ / 2)` estimate first. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (Hop : E →L[𝕜] E) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
    N.Mem Hop →
      δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal Hop := by
  exact TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
    (𝕜 := 𝕜) N hA Hop hHop hPred hQred hδ hgap

/-- **Probe 46: the production directed `sin 2Θ₀` theorem is scalar-generic.**

This is now a conformance probe rather than an assumed-core probe.  It exercises the
production reducing-subspace/residual engine all the way through the where-defined UIN
boundary over arbitrary `RCLike`. -/
theorem sinTwoTheta_directed_whereDefinedUIN_rclike_production_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {trial gapCarrier : Submodule 𝕜 E}
    [trial.HasOrthogonalProjection] [gapCarrier.HasOrthogonalProjection]
    {M : trial →L[𝕜] trial} {R : trial →L[𝕜] E}
    (hred : _root_.LinearPMap.IsReducing A gapCarrier)
    (htrialDom : ∀ v : trial, (v : E) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : E), htrialDom v⟩ = R v + ((M v : trial) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) →
    N.Mem R →
      δ * N.gaugeReal
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gaugeReal R := by
  exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
    N hA hred htrialDom hres hδ hgap

/-- Probe 47: the complete scalar-generic source-facing Section 2 theorem. -/
theorem sinTwoTheta_complete_whereDefinedUIN_rclike_production_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A T : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule 𝕜 E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hP : _root_.LinearPMap.IsReducing A P)
    (hQ : _root_.LinearPMap.IsReducing T Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Qᗮ hQ.orthogonal) δ) :
    (∀ R : P →L[𝕜] E,
      (∀ p : P, ∀ hp : (p : E) ∈ T.domain,
        T ⟨(p : E), hp⟩ = A ⟨(p : E), by rw [← hdom]; exact hp⟩ + R p) →
      N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) →
      N.Mem R →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal R) ∧
    (∀ Hop : E →L[𝕜] E, Hop.IsSymmetric →
      T = TauCeti.LinearPMap.addBounded A Hop →
      N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
      N.Mem Hop →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) := by
  simpa only [TauCeti.DavisKahan1970.sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator] using
    (TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta
      N hA hT hdom hP hQ hδ hgap)

end

end SourceUINConformance
end ExactSinTheta
end DavisKahan
end TauCeti
