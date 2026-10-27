/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerTopology
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenSignedOptimizers
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# The exact Hilbert Schatten uniqueness threshold

For a Schatten projection difference and balanced crossed defects, the
global minimizing ambient unitary is unique exactly when the projection
gap is at most the critical sine. The finite-cutoff homeomorphism transfers
finite uniqueness, and the actual reducing norm decomposition recovers
the full ambient gap, including the critical equality case.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A necessary and sufficient uniqueness test over all ambient unitary
transporters. The native extended objective imposes no finite-cost
assumption on competitors. All angle multiplicities and defect spaces
are included, and no separability assumption is needed. -/
theorem schattenHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) ↔
      K.projectionGap L ≤ Real.sin (criticalAngle p.toReal) := by
  let c := Real.sin (criticalAngle p.toReal) / 2
  have hcangle := criticalAngle_mem p.toReal hp1 hp2
  have hsin : 0 < Real.sin (criticalAngle p.toReal) :=
    Real.sin_pos_of_pos_of_lt_pi hcangle.1 (by linarith [hcangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (criticalAngle p.toReal)]
  have hcrit : c ≤ Real.sin (criticalAngle p.toReal) := by dsimp only [c]; linarith
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, hL, htail⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  obtain ⟨hdim, e, _⟩ := exists_schatten_finite_cutoff_optimizer_homeomorph
    p hp hp1 hp2 K L J hD c hc hc1 hcrit
  have hfinite :=
    schatten_transport_unique_minimizer_linearIsometryEquiv_iff_complex
      p hp hp1 hp2 (K.comap M.subtype) (L.comap M.subtype) hdim
  have htransfer := e.toEquiv.existsUnique_subtype_congr
  rw [← htransfer]
  simp_rw [mem_schattenTransportMinimizers]
  rw [hfinite,
    Submodule.finite_principalAngles_le_iff_directedProjectionGap_le _ _ _
      ⟨hcangle.1.le, hcangle.2.le⟩,
    ← Submodule.projectionGap_eq_directedProjectionGap_of_finrank_eq _ _ hdim]
  constructor
  · intro hhead
    have hred : M.IsReducing (K.starProjection - L.starProjection).toLinearMap := by
      apply (M.isReducing_iff _).mpr
      exact ⟨fun _ hx => M.sub_mem (hK.mem_invtSubmodule hx) (hL.mem_invtSubmodule hx),
        fun _ hx => Mᗮ.sub_mem (hK.orthogonal_mem_invtSubmodule hx)
          (hL.orthogonal_mem_invtSubmodule hx)⟩
    rw [Submodule.projectionGap_def,
      ContinuousLinearMap.norm_eq_max_compressions_of_isReducing _ M hred]
    apply max_le
    · rw [← Submodule.projection_sub_comap_subtype_eq_compression_of_invariant
        K L M hK.mem_invtSubmodule hL.mem_invtSubmodule]
      rwa [Submodule.projectionGap_def] at hhead
    · calc
        _ ≤ ‖Mᗮ.orthogonalProjectionOnto‖ *
            ‖(K.starProjection - L.starProjection) ∘L Mᗮ.subtypeL‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * c := mul_le_mul Mᗮ.orthogonalProjectionOnto_norm_le htail
          (norm_nonneg ((K.starProjection - L.starProjection) ∘L Mᗮ.subtypeL))
          (by norm_num)
        _ ≤ _ := by simpa only [one_mul] using hcrit
  · intro hgap
    exact (K.projectionGap_comap_subtype_le_of_invariant L M
      hK.mem_invtSubmodule hL.mem_invtSubmodule).trans hgap

/-- The same exact criterion in closed-form norm coordinates. -/
theorem schattenHilbertTransport_unique_minimizer_iff_critical_norm_of_defectEquiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) ↔
      K.projectionGap L ≤ 2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [schattenHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
      p hp hp1 hp2 K L J hD,
    sin_criticalAngle p.toReal hp1]

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
