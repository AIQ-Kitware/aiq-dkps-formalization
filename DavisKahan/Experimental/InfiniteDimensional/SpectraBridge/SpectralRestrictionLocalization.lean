/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.SpectralRestrictionOperator
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import Spectra.Mathlib.CharFunBridge
import Spectra.SpectralTheory.Calculus.PMapSquareRoot
import Spectra.SpectralTheory.Spectrum

/-!
# Spectral localization of Stone generators on spectral ranges

The Stone generator constructed on the range of `E_A(B)` must inherit the
spectral localization encoded by `B`.  This file proves that inheritance
without an independent adjoint or resolvent calculation.

The key observation is scalar: for a vector in the spectral range, the
restricted unitary group and the ambient unitary group have identical matrix
coefficients.  Fourier uniqueness therefore identifies their diagonal Borel
measures.  The ambient measure is the restriction to `B`, because the vector
is fixed by `E_A(B)`.

Consequences:

* if `B ⊆ [β, α]`, the restricted Stone generator has quadratic form in
  `[β, α]`;
* if `B` is disjoint from an open interval, every point of that interval lies
  in the resolvent set of the restricted generator.

These are the final analytic localization inputs needed by the independent
bounded-perturbation sine-theta path.
-/

open scoped InnerProductSpace ENNReal
open Complex Filter MeasureTheory Topology

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.Resolvent
open ForMathlib.DavisKahan.Experimental.ExactSinTheta

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The scalar spectral measure of the restricted Stone group is the ambient
scalar spectral measure of the included vector. -/
theorem borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : selfAdjointSpectralSubspace A hA B hB) :
    borelMeasure (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) x =
      borelMeasure (genToGroup hA) (x : H) := by
  haveI : IsFiniteMeasure
      (borelMeasure (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) x) :=
    borelMeasure_isFiniteMeasure _ _
  haveI : IsFiniteMeasure (borelMeasure (genToGroup hA) (x : H)) :=
    borelMeasure_isFiniteMeasure _ _
  apply Spectra.Fourier.measure_ext_of_fourier
  intro t
  rw [← borelMeasure_fourier
      (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) x t,
    ← borelMeasure_fourier (genToGroup hA) (x : H) t]
  change ⟪(x : H), (genToGroup hA).U t (x : H)⟫_ℂ =
    ⟪(x : H), (genToGroup hA).U t (x : H)⟫_ℂ
  rfl

/-- The scalar spectral measure of a spectral-range vector is the ambient
measure restricted to the selecting set. -/
theorem borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup_restrict
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : selfAdjointSpectralSubspace A hA B hB) :
    borelMeasure (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) x =
      (borelMeasure (genToGroup hA) (x : H)).restrict B := by
  have hfix : spectralProjection (genToGroup hA) B hB (x : H) = (x : H) := by
    change (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA).proj
        B hB (x : H) = (x : H)
    exact pvmProjection_eq_self_of_mem_rangeSubspace
      (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA)
      B hB x.property
  calc
    borelMeasure (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) x =
        borelMeasure (genToGroup hA) (x : H) :=
      borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup A hA B hB x
    _ = borelMeasure (genToGroup hA)
          (spectralProjection (genToGroup hA) B hB (x : H)) :=
      congrArg (borelMeasure (genToGroup hA)) hfix.symm
    _ = (borelMeasure (genToGroup hA) (x : H)).restrict B :=
      borelMeasure_spectralProjection_restrict (genToGroup hA) B hB (x : H)

/-- A spectral projection of the restricted group vanishes whenever its set is
disjoint from the selecting set. -/
theorem spectralProjection_selfAdjointSpectralSubspaceUnitaryGroup_eq_zero_of_inter_eq_empty
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hCB : C ∩ B = ∅) :
    spectralProjection (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB)
      C hC = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [zero_apply]
  apply (spectralProjection_eq_zero_iff_measure_zero
    (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) C hC x).mpr
  rw [borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup_restrict
      A hA B hB x,
    Measure.restrict_apply hC, hCB, measure_empty]

/-- The Stone generator on `E_A(B)H` inherits interval form bounds from the
set containment `B ⊆ [β, α]`. -/
theorem selfAdjointSpectralRestriction_semibounded_of_subset_Icc
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    {β α : ℝ} (hBsub : B ⊆ Set.Icc β α) :
    SemiboundedBelow (selfAdjointSpectralRestriction A hA B hB) β ∧
      SemiboundedAbove (selfAdjointSpectralRestriction A hA B hB) α := by
  let U := selfAdjointSpectralSubspaceUnitaryGroup A hA B hB
  constructor
  · intro x
    have hmom := weak_first_moment U x
    have hmemB : ∀ᵐ s ∂(borelMeasure U
        (x : selfAdjointSpectralSubspace A hA B hB)), s ∈ B := by
      rw [borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup_restrict
        A hA B hB (x : selfAdjointSpectralSubspace A hA B hB)]
      exact ae_restrict_mem hB
    have hge : ∀ᵐ s ∂(borelMeasure U
        (x : selfAdjointSpectralSubspace A hA B hB)), β ≤ s := by
      filter_upwards [hmemB] with s hs
      exact (hBsub hs).1
    change β * ‖(x : selfAdjointSpectralSubspace A hA B hB)‖ ^ 2 ≤
      (⟪generator U x,
        (x : selfAdjointSpectralSubspace A hA B hB)⟫_ℂ).re
    calc
      β * ‖(x : selfAdjointSpectralSubspace A hA B hB)‖ ^ 2 =
          ∫ _s, β ∂(borelMeasure U
            (x : selfAdjointSpectralSubspace A hA B hB)) := by
        rw [integral_const, smul_eq_mul, Measure.real_def,
          borelMeasure_mass, mul_comm]
      _ ≤ ∫ s, s ∂(borelMeasure U
            (x : selfAdjointSpectralSubspace A hA B hB)) :=
        integral_mono_ae (integrable_const _) hmom.1 hge
      _ = (⟪(x : selfAdjointSpectralSubspace A hA B hB),
            generator U x⟫_ℂ).re := hmom.2
      _ = (⟪generator U x,
            (x : selfAdjointSpectralSubspace A hA B hB)⟫_ℂ).re := by
        rw [← inner_conj_symm, Complex.conj_re]
  · intro x
    have hmom := weak_first_moment U x
    have hmemB : ∀ᵐ s ∂(borelMeasure U
        (x : selfAdjointSpectralSubspace A hA B hB)), s ∈ B := by
      rw [borelMeasure_selfAdjointSpectralSubspaceUnitaryGroup_restrict
        A hA B hB (x : selfAdjointSpectralSubspace A hA B hB)]
      exact ae_restrict_mem hB
    have hle : ∀ᵐ s ∂(borelMeasure U
        (x : selfAdjointSpectralSubspace A hA B hB)), s ≤ α := by
      filter_upwards [hmemB] with s hs
      exact (hBsub hs).2
    change (⟪generator U x,
        (x : selfAdjointSpectralSubspace A hA B hB)⟫_ℂ).re ≤
      α * ‖(x : selfAdjointSpectralSubspace A hA B hB)‖ ^ 2
    calc
      (⟪generator U x,
          (x : selfAdjointSpectralSubspace A hA B hB)⟫_ℂ).re =
          (⟪(x : selfAdjointSpectralSubspace A hA B hB),
            generator U x⟫_ℂ).re := by
        rw [← inner_conj_symm, Complex.conj_re]
      _ = ∫ s, s ∂(borelMeasure U
            (x : selfAdjointSpectralSubspace A hA B hB)) := hmom.2.symm
      _ ≤ ∫ _s, α ∂(borelMeasure U
            (x : selfAdjointSpectralSubspace A hA B hB)) :=
        integral_mono_ae hmom.1 (integrable_const _) hle
      _ = α * ‖(x : selfAdjointSpectralSubspace A hA B hB)‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, Measure.real_def,
          borelMeasure_mass, mul_comm]

/-- If the selecting set is disjoint from an open interval, the spectrum of
the restricted Stone generator avoids that interval. -/
theorem selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    {a b : ℝ} (hdisj : B ∩ Set.Ioo a b = ∅) :
    ∀ lam ∈ Set.Ioo a b,
      lam ∉ spectrum (selfAdjointSpectralRestriction A hA B hB).toLinearPMap := by
  intro lam hlam
  let ε : ℝ := min (lam - a) (b - lam) / 2
  have hleft : 0 < lam - a := by linarith [hlam.1]
  have hright : 0 < b - lam := by linarith [hlam.2]
  have hmin : 0 < min (lam - a) (b - lam) := lt_min hleft hright
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos hmin (by norm_num)
  have hhalf : ε ≤ min (lam - a) (b - lam) := by
    dsimp [ε]
    linarith [hmin]
  have hεleft : ε ≤ lam - a := hhalf.trans (min_le_left _ _)
  have hεright : ε ≤ b - lam := hhalf.trans (min_le_right _ _)
  have hsub : Set.Ioo (lam - ε) (lam + ε) ⊆ Set.Ioo a b := by
    intro s hs
    rw [Set.mem_Ioo] at hs ⊢
    exact ⟨by linarith [hs.1, hεleft], by linarith [hs.2, hεright]⟩
  have hinter : Set.Ioo (lam - ε) (lam + ε) ∩ B = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false,
      iff_false]
    intro hs
    have hsbad : s ∈ B ∩ Set.Ioo a b := ⟨hs.2, hsub hs.1⟩
    rw [hdisj] at hsbad
    exact hsbad
  have hzero : spectralProjection
      (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB)
      (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo = 0 :=
    spectralProjection_selfAdjointSpectralSubspaceUnitaryGroup_eq_zero_of_inter_eq_empty
      A hA B (Set.Ioo (lam - ε) (lam + ε)) hB measurableSet_Ioo hinter
  have hres : (lam : ℂ) ∈ resolventSet
      (generator (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB)) :=
    mem_resolventSet_of_spectralProjection_Ioo_eq_zero
      (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB) hε hzero
  change ¬ ((lam : ℂ) ∉ resolventSet
    (generator (selfAdjointSpectralSubspaceUnitaryGroup A hA B hB)))
  intro hnot
  exact hnot hres

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
