/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionCutoff
public import DavisKahan.Geometry.Polar.CanonicalStability

/-!
# Dimension-free data stability of the unique Schatten optimizer

In the closed canonical regime the actual global minimizer is a
Lipschitz function of the target projection, with the source fixed.
This includes the critical equality case, despite its quartic objective
flatness. The estimate is about varying data, not arbitrary inexact
minimizers of one fixed problem.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem sin_critical_lt_one (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Real.sin (criticalAngle p) < 1 := by
  have hc := criticalAngle_mem p hp1 hp2
  have h := Real.strictMonoOn_sin
    ⟨by linarith [hc.1, Real.pi_pos], hc.2.le⟩
    ⟨by linarith [Real.pi_pos], le_rfl⟩ hc.2
  simpa only [Real.sin_pi_div_two] using h

/-- Native Schatten data and the closed gap bound force every ambient
global optimizer to be canonical. Finite candidate cost and a separate
index-balance assumption are unnecessary. -/
theorem eq_canonicalPolarFactor_of_mem_schattenHilbertTransportMinimizers
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hgap : K.projectionGap L ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E)
    (hU : U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) :
    (U : E →L[ℂ] E) = spectraCanonicalPolarFactor K L := by
  rw [mem_schattenHilbertTransportMinimizers] at hU
  have hacute : IsUniformlyAcute K L := hgap.trans_lt (sin_critical_lt_one _ hp1 hp2)
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K L hacute
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K L hacute
  have hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L) := by rw [hz, hz']
  obtain ⟨V, hV, hVfinite, _, _⟩ :=
    exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top
      p hp hp1 hp2 K L hD hbalance
  have hfinite := ne_top_of_le_ne_top hVfinite (hU.2 V hV)
  exact eq_canonicalPolarFactor_of_schatten_minimal_of_gap_le_critical
    p hp hp1 hp2 K L U hU.1 hfinite hU.2 hgap

/-- A projection-error certificate for the actual unrestricted
Schatten optimizers in a closed subcritical gap ball. Both problems
may have infinite-rank data and arbitrary fixed ambient directions. -/
theorem norm_schatten_minimizers_sub_le_of_projectionGap_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    (hDL : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hDM : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - M.starProjection) ≠ ∞)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hcrit : gamma ≤ Real.sin (criticalAngle p.toReal))
    (hL : K.projectionGap L ≤ gamma) (hM : K.projectionGap M ≤ gamma)
    (U V : E ≃ₗᵢ[ℂ] E)
    (hU : U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L)
    (hV : V ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K M) :
    ‖(U : E →L[ℂ] E) - (V : E →L[ℂ] E)‖ ≤
      L.projectionGap M / Real.sqrt (1 - gamma ^ 2) := by
  rw [eq_canonicalPolarFactor_of_mem_schattenHilbertTransportMinimizers
      p hp hp1 hp2 K L hDL (hL.trans hcrit) U hU,
    eq_canonicalPolarFactor_of_mem_schattenHilbertTransportMinimizers
      p hp hp1 hp2 K M hDM (hM.trans hcrit) V hV]
  exact norm_canonicalPolarFactor_sub_le_of_projectionGap_le K L M gamma hgamma
    (hcrit.trans_lt (sin_critical_lt_one _ hp1 hp2)) hL hM

/-- Throughout the entire closed canonical regime, including critical
equality, the optimizer has the explicit data-Lipschitz constant
`p / (2-p)`. Quartic objective flatness does not obstruct this data bound. -/
theorem norm_schatten_minimizers_sub_le_at_closed_critical_gap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    (hDL : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hDM : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - M.starProjection) ≠ ∞)
    (hL : K.projectionGap L ≤ Real.sin (criticalAngle p.toReal))
    (hM : K.projectionGap M ≤ Real.sin (criticalAngle p.toReal))
    (U V : E ≃ₗᵢ[ℂ] E)
    (hU : U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L)
    (hV : V ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K M) :
    ‖(U : E →L[ℂ] E) - (V : E →L[ℂ] E)‖ ≤
      p.toReal / (2 - p.toReal) * L.projectionGap M := by
  rw [eq_canonicalPolarFactor_of_mem_schattenHilbertTransportMinimizers
      p hp hp1 hp2 K L hDL hL U hU,
    eq_canonicalPolarFactor_of_mem_schattenHilbertTransportMinimizers
      p hp hp1 hp2 K M hDM hM V hV]
  let theta := criticalAngle p.toReal
  have hcpos : 0 < Real.cos theta := by
    rw [show Real.cos theta = (2 - p.toReal) / p.toReal from cos_criticalAngle _ hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hL0 : 0 ≤ K.projectionGap L := by rw [Submodule.projectionGap_def]; positivity
  have hM0 : 0 ≤ K.projectionGap M := by rw [Submodule.projectionGap_def]; positivity
  have hLsq := mul_self_le_mul_self hL0 hL
  have hMsq := mul_self_le_mul_self hM0 hM
  have h := add_mul_norm_canonicalPolarFactor_sub_le_two_mul_projectionGap K L M _ _ hcpos hcpos
    (by nlinarith [Real.sin_sq_add_cos_sq theta] : Real.cos theta ^ 2 + K.projectionGap L ^ 2 ≤ 1)
    (by nlinarith [Real.sin_sq_add_cos_sq theta] : Real.cos theta ^ 2 + K.projectionGap M ^ 2 ≤ 1)
  have hcos : p.toReal * (Real.cos theta + Real.cos theta) = 2 * (2 - p.toReal) := by
    rw [show Real.cos theta = (2 - p.toReal) / p.toReal from cos_criticalAngle _ hp1 hp2]
    field_simp
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ p.toReal)
  rw [← mul_assoc, hcos] at hscaled
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 2 - p.toReal)).mpr
  nlinarith

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
