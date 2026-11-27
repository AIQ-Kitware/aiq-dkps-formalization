/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.SpectralTheory.AbstractSpectrum
public import DavisKahan.SpectralTheory.PartialMap.RealSpectrum
public import DavisKahan.Sylvester.ClosedSylvesterEquation
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Genuine spectral half-line localization

This leaf converts half-line containment of the spectrum of a closed
self-adjoint operator into the quadratic-form semibounds consumed by the ordered
branches of the unbounded Sylvester theorem.

The native support theorem makes the projection on the open complement
vanish. Tau Ceti's half-line criterion gives the form bound on the domain.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace TauCeti
namespace DavisKahan


universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine spectral containment in `[c, ∞)` implies the matching lower
quadratic-form bound. -/
theorem semiboundedBelow_of_spectrum_subset_Ici
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' _root_.LinearPMap.spectrum A ⊆
        Set.Ici c) :
    TauCeti.LinearPMap.SemiboundedBelow A c := by
  apply (LinearPMap.semiboundedBelow_iff _ _).mpr
  intro x
  have hzero :
      (A.spectralPVM hA).proj (Set.Iio c) measurableSet_Iio = 0 := by
    refine hA.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet measurableSet_Iio ?_
    intro lam hlam
    by_contra hnot
    have hroot : (lam : ℂ) ∈ _root_.LinearPMap.spectrum A := by
      rw [_root_.LinearPMap.mem_spectrum_iff]
      exact hnot
    exact absurd (hσ hroot) (by simpa using not_le.mpr hlam)
  exact (hA.spectralPVM_proj_Iio_eq_zero_iff c).mp hzero x

/-- Genuine spectral containment in `(-∞, c]` implies the matching upper
quadratic-form bound. -/
theorem semiboundedAbove_of_spectrum_subset_Iic
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' _root_.LinearPMap.spectrum A ⊆
        Set.Iic c) :
    TauCeti.LinearPMap.SemiboundedAbove A c := by
  apply (LinearPMap.semiboundedAbove_iff _ _).mpr
  intro x
  have hzero :
      (A.spectralPVM hA).proj (Set.Ioi c) measurableSet_Ioi = 0 := by
    refine hA.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet measurableSet_Ioi ?_
    intro lam hlam
    by_contra hnot
    have hroot : (lam : ℂ) ∈ _root_.LinearPMap.spectrum A := by
      rw [_root_.LinearPMap.mem_spectrum_iff]
      exact hnot
    exact absurd (hσ hroot) (by simpa using not_le.mpr hlam)
  exact (hA.spectralPVM_proj_Ioi_eq_zero_iff c).mp hzero x

end DavisKahan
end TauCeti
