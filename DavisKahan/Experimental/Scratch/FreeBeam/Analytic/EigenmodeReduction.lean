/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Scratch.FreeBeam.Classical.CharacteristicConverse
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeamAnalyticFoundation
import Mathlib.Tactic

/-!
# Reduction of positive free-beam eigenvalues to the characteristic equation

The remaining ODE-to-spectrum bridge has two logically separate parts:

1. compact-resolvent spectral theory turns a positive spectral point into an
   eigenvector;
2. one-dimensional regularity and the constant-coefficient ODE classify that
   eigenvector by the trigonometric-hyperbolic mode family.

This file packages the second part as an explicit certificate and proves the
characteristic and numerical consequences.  It also records the exact
hypothesis needed to turn these certificates into the
`positive_spectrum_characterization` field of `SobolevTraceFoundation`.
-/

open Set
open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace FreeBeam
namespace Analytic

noncomputable section

open MathAhead.HiddenFoundations.FreeBeam

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A point-spectrum eigenpair for a closed operator, with the eigenvector
stored in the operator domain. -/
def ClosedOperatorEigenpair
    (A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H))
    (lambda : ℝ) (x : A.domain) : Prop :=
  (x : H) ≠ 0 ∧ A.toLinearMap x = (lambda : ℂ) • (x : H)

/-- Classical mode data obtained from regularity of a positive eigenvector. -/
structure PositiveClassicalModeCertificate (lambda : ℝ) where
  beta : ℝ
  beta_pos : 0 < beta
  eigenvalue_eq : lambda = beta ^ 4
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  coefficients_nontrivial : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0
  free_boundary :
    MathAhead.HiddenFoundations.FreeBeam.FreeBoundary beta a b c d

namespace PositiveClassicalModeCertificate

/-- Every positive classical-mode certificate satisfies the characteristic
equation. -/
theorem characteristic_eq_zero
    {lambda : ℝ} (C : PositiveClassicalModeCertificate lambda) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic C.beta = 0 := by
  exact MathAhead.HiddenFoundations.FreeBeam.characteristic_eq_zero_of_freeBoundary
    C.beta_pos.ne' C.free_boundary C.coefficients_nontrivial

/-- A localized first root forces every certified positive eigenvalue above
`500`. -/
theorem eigenvalue_gt_five_hundred
    (L : MathAhead.HiddenFoundations.FreeBeam.PositiveRootLocalization)
    {lambda : ℝ} (C : PositiveClassicalModeCertificate lambda) :
    500 < lambda := by
  rw [C.eigenvalue_eq]
  exact MathAhead.HiddenFoundations.FreeBeam.positive_root_fourth_power_gt_five_hundred
    L C.beta_pos C.characteristic_eq_zero

end PositiveClassicalModeCertificate

/-- Regularity/classification package for one concrete free-beam operator. -/
structure PositiveEigenmodeRegularity
    (A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)) where
  classify : ∀ {lambda : ℝ} {x : A.domain},
    0 < lambda → ClosedOperatorEigenpair A lambda x →
      PositiveClassicalModeCertificate lambda

namespace PositiveEigenmodeRegularity

/-- Every positive eigenpair of a regular free-beam realization gives a
positive characteristic root. -/
theorem eigenpair_characteristic
    {A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    (R : PositiveEigenmodeRegularity A)
    {lambda : ℝ} {x : A.domain}
    (hlambda : 0 < lambda)
    (hx : ClosedOperatorEigenpair A lambda x) :
    ∃ beta : ℝ,
      0 < beta ∧
      MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0 ∧
      lambda = beta ^ 4 := by
  let C := R.classify hlambda hx
  exact ⟨C.beta, C.beta_pos, C.characteristic_eq_zero, C.eigenvalue_eq⟩

end PositiveEigenmodeRegularity

/-- Spectral discreteness input: every positive spectral value is represented
by a nonzero domain eigenvector. -/
def PositiveSpectrumIsPointSpectrum
    (A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)) : Prop :=
  ∀ lambda : ℝ,
    lambda ∈ A.realSpectrum → 0 < lambda →
      ∃ x : A.domain, ClosedOperatorEigenpair A lambda x

/-- Compact-resolvent discreteness plus ODE regularity gives the exact positive
spectrum characterization required by the paper-facing foundation. -/
theorem positive_spectrum_characterization_of_pointSpectrum_and_regularity
    (A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H))
    (hpoint : PositiveSpectrumIsPointSpectrum A)
    (hregular : PositiveEigenmodeRegularity A) :
    ∀ lambda : ℝ,
      lambda ∈ A.realSpectrum → 0 < lambda →
      ∃ beta : ℝ,
        0 < beta ∧
        MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0 ∧
        lambda = beta ^ 4 := by
  intro lambda hlambda hpositive
  obtain ⟨x, hx⟩ := hpoint lambda hlambda hpositive
  exact hregular.eigenpair_characteristic hpositive hx

/-- Once root localization is known, every positive spectral point lies above
`500`. -/
theorem positive_spectrum_gt_five_hundred_of_pointSpectrum_and_regularity
    (A : DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H))
    (L : MathAhead.HiddenFoundations.FreeBeam.PositiveRootLocalization)
    (hpoint : PositiveSpectrumIsPointSpectrum A)
    (hregular : PositiveEigenmodeRegularity A)
    {lambda : ℝ} (hlambda : lambda ∈ A.realSpectrum)
    (hpositive : 0 < lambda) :
    500 < lambda := by
  obtain ⟨beta, hbeta, hroot, hlambda_beta⟩ :=
    positive_spectrum_characterization_of_pointSpectrum_and_regularity
      A hpoint hregular lambda hlambda hpositive
  rw [hlambda_beta]
  exact MathAhead.HiddenFoundations.FreeBeam.positive_root_fourth_power_gt_five_hundred
    L hbeta hroot

end

end Analytic
end FreeBeam
end Scratch
end Experimental
end DavisKahan
end ForMathlib
