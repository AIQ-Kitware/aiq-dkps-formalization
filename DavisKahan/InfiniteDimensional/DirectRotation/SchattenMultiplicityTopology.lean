/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerTopology

/-!
# Independent multiplicity coordinates for all Hilbert Schatten optimizers

The full infinite-dimensional optimizer family has the operator-norm
topology of independent finite active multiplicity projection factors
and a finite crossed-defect unitary factor. Rank labels are locally
constant, and distinct rank labels have positive operator-norm separation
for each fixed pair and exponent. These are exact optimizer-set results,
not stability assertions for arbitrary near-minimizers or perturbed data.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Multiplicity coordinates transfer through any exact norm-preserving
homeomorphism from a finite optimizer space. The finite-cutoff theorem
provides this homeomorphism for every admissible Hilbert projection pair. -/
theorem exists_schatten_hilbert_multiplicity_coordinates_of_homeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [CompleteSpace F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (K₀ L₀ : Submodule ℂ F)
    (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀)
    (eH : schattenTransportMinimizers p K₀ L₀ ≃ₜ
      schattenHilbertTransportMinimizers p.toReal hp1.le K L)
    (hnorm : ∀ V W, ‖((eH V).val : E →L[ℂ] E) - ((eH W).val : E →L[ℂ] E)‖ =
      ‖(V.val : F →L[ℂ] F) - (W.val : F →L[ℂ] F)‖) :
    let R₀ : unitary (F →L[ℂ] F) :=
      ⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
        nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩
    let N := schattenRotationMultiplicitySpace p.toReal R₀
    ∃ e : ((∀ theta : schattenActiveRotationAngles p.toReal R₀,
        {Q : N theta →L[ℂ] N theta // IsStarProjection Q}) ×
          (halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀)) ≃ₜ
            schattenHilbertTransportMinimizers p.toReal hp1.le K L,
      (∀ theta, IsLocallyConstant (fun T =>
        Module.finrank ℂ (((e.symm T).1 theta).val.range))) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ data data' theta,
        Module.finrank ℂ ((data.1 theta).val.range) ≠
          Module.finrank ℂ ((data'.1 theta).val.range) →
        1 ≤ k * ‖((e data).val : E →L[ℂ] E) - ((e data').val : E →L[ℂ] E)‖ := by
  obtain ⟨eF, _, hlocal, k, hk, hsep⟩ :=
    exists_schatten_multiplicity_parameter_homeomorph p hp hp1 hp2 K₀ L₀ hKL
  let e := eF.trans eH
  refine ⟨e, ?_, k, hk, ?_⟩
  · intro theta
    exact (hlocal theta).comp_continuous eH.symm.continuous
  · intro data data' theta hrank
    have h := hsep data data' theta hrank
    rw [← hnorm (eF data) (eF data')] at h
    exact h

/-- The entire Hilbert-space optimizer family has independent finite
active multiplicity-projection and crossed-defect unitary coordinates,
with the actual operator-norm topology. -/
theorem exists_schatten_hilbert_multiplicity_parameter_homeomorph
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (K.starProjection - L.starProjection) hD) c hc).1
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    ∃ hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀,
      let R₀ : unitary (M →L[ℂ] M) :=
        ⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
          nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩
      let N := schattenRotationMultiplicitySpace p.toReal R₀
      Nonempty ( ((∀ theta : schattenActiveRotationAngles p.toReal R₀,
          {Q : N theta →L[ℂ] N theta // IsStarProjection Q}) ×
            (halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀)) ≃ₜ
              schattenHilbertTransportMinimizers p.toReal hp1.le K L) := by
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
      (K.starProjection - L.starProjection) hD) c hc).1
  obtain ⟨hKL, eH, _, _, hnorm⟩ := exists_schatten_finite_cutoff_optimizer_homeomorph
    p hp hp1 hp2 K L J hD c hc hc1 hcrit
  refine ⟨hKL, ?_⟩
  -- Preserve the dependent parameter types when composing the two homeomorphisms.
  obtain ⟨e, _, _⟩ := exists_schatten_hilbert_multiplicity_coordinates_of_homeomorph
    p hp hp1 hp2 K L (K.comap M.subtype) (L.comap M.subtype) hKL eH hnorm
  exact ⟨e⟩

/-- Simple active factors and zero right defect give exactly `2^s`
ambient Hilbert-space optimizers, each isolated in the operator-norm
optimizer topology. Infinite inactive multiplicities are unrestricted. -/
theorem schatten_hilbert_optimizer_count_and_discrete_of_simple_active_angles
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (K.starProjection - L.starProjection) hD) c hc).1
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    ∃ hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀,
      let R₀ : unitary (M →L[ℂ] M) :=
        ⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
          nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩
      Module.finrank ℂ (halmosSourceDefect K₀ L₀) = 0 →
      (∀ theta : schattenActiveRotationAngles p.toReal R₀,
        Module.finrank ℂ (schattenRotationMultiplicitySpace p.toReal R₀ theta) = 1) →
      Nat.card (schattenHilbertTransportMinimizers p.toReal hp1.le K L) =
          2 ^ Nat.card (schattenActiveRotationAngles p.toReal R₀) ∧
        DiscreteTopology (schattenHilbertTransportMinimizers p.toReal hp1.le K L) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
      (K.starProjection - L.starProjection) hD) c hc).1
  obtain ⟨hKL, eH, _, _, _⟩ := exists_schatten_finite_cutoff_optimizer_homeomorph
    p hp hp1 hp2 K L J hD c hc hc1 hcrit
  refine ⟨hKL, ?_⟩
  intro hdefect hsimple
  have hcard := natCard_schattenTransportMinimizers_of_simple_active_angles
    p hp hp1 hp2 (K.comap M.subtype) (L.comap M.subtype) hKL hdefect hsimple
  have hfullcard := (Nat.card_congr eH.toEquiv).symm.trans hcard
  refine ⟨hfullcard, ?_⟩
  let : Finite (schattenHilbertTransportMinimizers p.toReal hp1.le K L) :=
    Nat.finite_of_card_ne_zero (by rw [hfullcard]; exact pow_ne_zero _ (by norm_num))
  infer_instance

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
