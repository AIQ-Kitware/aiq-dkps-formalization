/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Frontier.RemainingSourceSurface

/-!
# Correct source wrappers for Section 7

The sine-double-angle source wrapper is an exact application of the compiled
unbounded ideal theorem.  The tangent theorem necessarily carries the positive
double-cosine denominator at the present level of generality; deleting that
denominator is not a promotion step.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open Set
open ExactSinTheta
open SpectraBridge
open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Compiler-facing exact wrapper for the source sine-double-angle theorem. -/
theorem section7_sinTwoTheta_source_ideal_completed
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
    delta * N.gauge (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
      2 * N.gauge E := by
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem

/-- Correct tangent-double-angle wrapper with the required double-cosine
denominator. -/
theorem section7_tanTwoTheta_source_ideal_corrected
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ∧
    delta * N.gauge (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ≤
      (2 * N.gauge E) /
        (1 - 2 * directedGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (A.addBounded E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem hquarter

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
