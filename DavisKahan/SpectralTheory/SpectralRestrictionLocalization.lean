/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import DavisKahan.SpectralTheory.SpectralRestrictionOperator
public import DavisKahan.Sylvester.ClosedSylvesterEquation
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import DavisKahan.SpectralTheory.PartialMap.RealSpectrum

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Spectral localization of the restriction to a spectral range

The restriction of `A` to the range of `E_A(B)` must inherit the spectral
localization encoded by `B`:

* if `B ⊆ [β, α]`, the restriction has quadratic form in `[β, α]`;
* if `B` is disjoint from an open interval, every point of that interval lies
  in the resolvent set of the restriction.

These are the final analytic localization inputs needed by the independent
bounded-perturbation sine-theta path.

## Provenance

Until 2026-07-29 both statements were routed through `vendor/Spectra`'s Stone
theory: the restricted operator was the generator of the restricted unitary
group, and the two facts came from that group's *scalar* Borel measure —
identified with the ambient one by Fourier uniqueness
(`Spectra.Fourier.measure_ext_of_fourier`), then restricted to `B` because the
vector is fixed by `E_A(B)`, after which `weak_first_moment` and
`mem_resolventSet_of_spectralProjection_Ioo_eq_zero` finished the job.

The form bounds apply Tau Ceti's half-line estimates on the spectral range.
Open-interval localization applies the spectral-measure gap resolvent to a
smaller interval centered at the point in question.
-/

open scoped InnerProductSpace ENNReal
open Complex Filter MeasureTheory Topology

namespace TauCeti
namespace DavisKahan


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The restriction to `E_A(B)H` inherits interval form bounds from the set
containment `B ⊆ [β, α]`. -/
theorem selfAdjointSpectralRestriction_semibounded_of_subset_Icc
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {β α : ℝ} (hBsub : B ⊆ Set.Icc β α) :
    TauCeti.LinearPMap.SemiboundedBelow (selfAdjointSpectralRestriction A hA B hB) β ∧
      TauCeti.LinearPMap.SemiboundedAbove (selfAdjointSpectralRestriction A hA B hB) α := by
  constructor
  · apply (TauCeti.LinearPMap.semiboundedBelow_iff _ _).mpr
    intro x
    change β * ‖(x.val : H)‖ ^ 2 ≤
      (⟪selfAdjointSpectralSubspaceInclusion A hA B hB
        (selfAdjointSpectralRestriction A hA B hB x), (x.val : H)⟫_ℂ).re
    rw [← selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB x]
    exact hA.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj hB
      (fun _ hs => (hBsub hs).1)
      (x := ⟨x.val.val, selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB x⟩)
      x.val.property
  · apply (TauCeti.LinearPMap.semiboundedAbove_iff _ _).mpr
    intro x
    change (⟪selfAdjointSpectralSubspaceInclusion A hA B hB
        (selfAdjointSpectralRestriction A hA B hB x), (x.val : H)⟫_ℂ).re ≤
      α * ‖(x.val : H)‖ ^ 2
    rw [← selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB x]
    exact hA.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj hB
      (fun _ hs => (hBsub hs).2)
      (x := ⟨x.val.val, selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB x⟩)
      x.val.property

/-- If the selecting set is disjoint from an open interval, the spectrum of the
restriction avoids that interval. -/
theorem selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {a b : ℝ} (hdisj : B ∩ Set.Ioo a b = ∅) :
    ∀ lam ∈ Set.Ioo a b,
      (lam : ℂ) ∉ _root_.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA B hB) := by
  intro lam hlam
  let ε := min (lam - a) (b - lam)
  have hε : 0 < ε := lt_min (sub_pos.mpr hlam.1) (sub_pos.mpr hlam.2)
  have hsubset : Set.Ioo (lam - ε) (lam + ε) ⊆ Set.Ioo a b :=
    Set.Ioo_subset_Ioo
      (by dsimp [ε]; linarith [min_le_left (lam - a) (b - lam)])
      (by dsimp [ε]; linarith [min_le_right (lam - a) (b - lam)])
  have hempty : B ∩ Set.Ioo (lam - ε) (lam + ε) = ∅ :=
    Set.eq_empty_of_subset_empty (hdisj ▸ Set.inter_subset_inter_right B hsubset)
  have hgap : (A.spectralPVM hA).proj (B ∩ Set.Ioo (lam - ε) (lam + ε))
      (hB.inter measurableSet_Ioo) = 0 := by
    simp only [hempty, ProjValMeasure.proj_empty]
  intro h
  exact (_root_.LinearPMap.mem_spectrum_iff _ _).mp h
    (hA.mem_resolventSet_restrict_range_spectralPVM_proj hB hε hgap)

end DavisKahan
end TauCeti
