/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Natural.Genuine

/-!
# Generalized complex sine-theta theorem from natural spectral inputs

The compiler-accepted `NaturalGenuine` module contains the canonical isometric
specialization.  This separate leaf adds the lower-frame result without
modifying that verified module.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open SpectraBridge

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Public generalized complex unbounded sine-theta theorem from natural
spectral inputs. The lower-frame polar factorization and every complementary
spectral restriction are constructed internally. -/
theorem generalizedSinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (hA : A.IsSelfAdjoint) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F))
    (hA0 : A0.IsSelfAdjoint)
    (X Rop : F →L[ℂ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ - X (A0.toLinearMap x) = Rop (x : F))
    (hgap : GenuineUnboundedSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem Rop) :
    N.toRectangularSymmetricIdealFamily.Mem
      (directedSinThetaOperator X
        (selfAdjointSpectralSubspaceInclusion A hA S hS)
        hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
        (directedSinThetaOperator X
          (selfAdjointSpectralSubspaceInclusion A hA S hS)
          hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge Rop := by
  let D := unboundedSinThetaDataOfSpectralSubspace
    A hA S hS A0 X Rop hXdom hReq
  have hLambda : D.Λ₁.IsSelfAdjoint := by
    exact selfAdjointSpectralRestriction_isSelfAdjoint A hA Sᶜ hS.compl
  have hdecomp : OrthogonalExactDecomposition
      (selfAdjointSpectralSubspaceInclusion A hA S hS) D.F₁ := by
    simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using
      spectralSubspace_orthogonalExactDecomposition A hA S hS
  have hmain := generalizedSinTheta_unbounded_exact_of_genuineSpectrumGap
    N D (selfAdjointSpectralSubspaceInclusion A hA S hS)
      hA hA0 hLambda hdecomp hδ hε hframe hgap hR
  simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using hmain

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti