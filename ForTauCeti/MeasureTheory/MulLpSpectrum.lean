/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.MeasureTheory.MulLpAlgebra
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Function.Lp.MaximalMultiplication.Spectrum

/-!
# The spectrum of a bounded scalar multiplier

TauCeti's maximal multiplication spectrum identifies the bounded operator's
spectrum with the support of the measure pushed forward by the symbol. This
lets the spectral models corestrict the symbol to the spectrum almost everywhere.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α} [SigmaFinite ρ]

/-- The spectrum of the bounded multiplier is the support of the distribution of its symbol. -/
theorem spectrum_multiplicationOperator_eq_support_map {g : α → ℂ} (hg : MemLp g ∞ ρ) :
    spectrum ℂ (Lp.multiplicationOperator (E := ℂ) (p := 2) (hg.toLp g)) =
      (ρ.map g).support := by
  have h := Lp.maximalMultiplication_coeFn_eq_multiplicationOperator
    (E := ℂ) (p := 2) (hg.toLp g)
  rw [Lp.maximalMultiplication_congr_ae hg.coeFn_toLp] at h
  rw [← ContinuousLinearMap.spectrum_toPMap_top, ← h,
    Lp.spectrum_maximalMultiplication hg.aestronglyMeasurable]
  ext z
  rw [Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Set.mem_ofPred_eq, pos_iff_ne_zero]
  refine forall_congr' fun ε => imp_congr_right fun _ => ?_
  rw [Measure.map_apply_of_aemeasurable hg.aestronglyMeasurable.aemeasurable
    Metric.isOpen_ball.measurableSet]
  simp only [Metric.ball, dist_eq_norm, Set.preimage, Set.mem_ofPred_eq]

/-- A bounded measurable symbol takes values in its multiplication spectrum almost everywhere. -/
theorem ae_mem_spectrum_mulLp (ρ : Measure α) [SigmaFinite ρ] {g : α → ℂ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂ρ, g x ∈ spectrum ℂ (mulLp ρ hg hgC) := by
  rw [mulLp, spectrum_multiplicationOperator_eq_support_map]
  exact ae_of_ae_map hg.aemeasurable (ρ.map g).support_mem_ae

end TauCeti
