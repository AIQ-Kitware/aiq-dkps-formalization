/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Natural.GenuineGeneralized
import DavisKahan.SinTheta.Natural.Real

/-!
# Bounded natural spectral-subspace specializations

These wrappers convert bounded self-adjoint operators to full-domain closed
operators and apply the natural unbounded spectral-subspace theorems. The
residual is the ordinary bounded defect `A X - X A0`.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

noncomputable section

universe v

section Complex

-- `open SpectraBridge` would resolve to the nested
-- `ExactSinTheta.SpectraBridge` namespace introduced by `RealSpectrumBridge`,
-- which shadows the intended one, so the full path is spelled out here.
open ForMathlib.DavisKahan.Experimental.SpectraBridge

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Bounded complex isometric theorem with a canonical spectral subspace. -/
theorem sinTheta_bounded_spectralSubspace_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (selfAdjointSpectralRestriction
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
        Sᶜ hS.compl) δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem
      (generalResidual A X A0)) :
    N.toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS ∘L
        (selfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS).adjoint) ∘L X) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id ℂ E -
          selfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS ∘L
          (selfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS).adjoint) ∘L X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge
          (generalResidual A X A0) := by
  apply sinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap
    N (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
      S hS (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A0 hA0)
      X (generalResidual A X A0) hX
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hδ => exact hδ
  case hgap => exact hgap
  case hR => exact hR

/-- Bounded complex lower-frame theorem with a canonical spectral subspace. -/
theorem generalizedSinTheta_bounded_spectralSubspace_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : GenuineUnboundedSylvesterGap
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (selfAdjointSpectralRestriction
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
        Sᶜ hS.compl) δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem
      (generalResidual A X A0)) :
    N.toRectangularSymmetricIdealFamily.Mem
      (directedSinThetaOperator X
        (selfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS) hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
        (directedSinThetaOperator X
          (selfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS) hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge
          (generalResidual A X A0) := by
  apply generalizedSinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap
    N (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
      S hS (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A0 hA0)
      X (generalResidual A X A0) hδ hε hframe
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hgap => exact hgap
  case hR => exact hR

end Complex

section Real

open SpectraBridge.RealSpectralRestriction

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Bounded real isometric theorem with a canonical descended spectral
subspace. -/
theorem sinTheta_bounded_real_spectralSubspace
    (N : UnitaryInvariantIdealFamily (𝕜 := ℝ))
    (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℝ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℝ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (realSelfAdjointSpectralRestriction
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
        Sᶜ hS.compl) δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem
      (generalResidual A X A0)) :
    N.toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS ∘L
        (realSelfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS).adjoint) ∘L X) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id ℝ E -
          realSelfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS ∘L
          (realSelfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS).adjoint) ∘L X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge
          (generalResidual A X A0) := by
  apply sinTheta_unbounded_real_spectralSubspace
    N (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
      S hS (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A0 hA0)
      X (generalResidual A X A0) hX
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hδ => exact hδ
  case hgap => exact hgap
  case hR => exact hR

/-- Bounded real lower-frame theorem with a canonical descended spectral
subspace. -/
theorem generalizedSinTheta_bounded_real_spectralSubspace
    (N : UnitaryInvariantIdealFamily (𝕜 := ℝ))
    (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℝ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℝ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : UnboundedSylvesterGap
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (realSelfAdjointSpectralRestriction
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
        (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
        Sᶜ hS.compl) δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem
      (generalResidual A X A0)) :
    N.toRectangularSymmetricIdealFamily.Mem
      (directedSinThetaOperatorReal X
        (realSelfAdjointSpectralSubspaceInclusion
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
          (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
          S hS) hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
        (directedSinThetaOperatorReal X
          (realSelfAdjointSpectralSubspaceInclusion
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
            (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
            S hS) hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge
          (generalResidual A X A0) := by
  apply generalizedSinTheta_unbounded_real_spectralSubspace
    N (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A hA)
      S hS (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A0)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint A0 hA0)
      X (generalResidual A X A0) hδ hε hframe
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hgap => exact hgap
  case hR => exact hR

end Real

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
