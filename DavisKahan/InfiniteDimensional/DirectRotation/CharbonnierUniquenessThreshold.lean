/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerTopology
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerUniqueness
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# The exact Hilbert Charbonnier uniqueness threshold

For a Hilbert--Schmidt projection difference and balanced crossed defects, the
global minimizing ambient unitary is unique exactly when the projection
gap is at most the critical sine. The finite-cutoff homeomorphism transfers
finite uniqueness, and the actual reducing norm decomposition recovers
the full ambient gap, including the critical equality case.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A necessary and sufficient uniqueness test over all ambient unitary
transporters. The native extended objective imposes no finite-cost
assumption on competitors. All angle multiplicities and defect spaces
are included, and no separability assumption is needed. -/
theorem charbonnierHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ charbonnierHilbertTransportMinimizers tau K L) ↔
      K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau) := by
  let c := Real.sin (smoothedCriticalAngle tau) / 2
  have hcangle := smoothedCriticalAngle_mem tau hτ
  have hsin : 0 < Real.sin (smoothedCriticalAngle tau) :=
    Real.sin_pos_of_pos_of_lt_pi hcangle.1 (by linarith [hcangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (smoothedCriticalAngle tau)]
  have hcrit : c ≤ Real.sin (smoothedCriticalAngle tau) := by dsimp only [c]; linarith
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, hL, htail⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  obtain ⟨hdim, e, _⟩ := exists_charbonnier_finite_cutoff_optimizer_homeomorph
    tau hτ K L J hD c hc hc1 hcrit
  have hfinite :=
    smoothed_transport_unique_minimizer_iff
      tau hτ (K.comap M.subtype) (L.comap M.subtype) hdim
  have htransfer := e.toEquiv.existsUnique_subtype_congr
  rw [← htransfer]
  simp_rw [mem_smoothedTransportMinimizers]
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

/-- Exact uniqueness criterion with no compactness, membership or
index hypothesis on the pair. Uniqueness itself forces native finite
cost, hence Hilbert--Schmidt membership; the critical gap removes the
index obstruction. All ambient competitors retain extended costs. -/
theorem charbonnierHilbertTransport_unique_minimizer_iff
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃! U : E ≃ₗᵢ[ℂ] E, U ∈ charbonnierHilbertTransportMinimizers tau K L) ↔
      (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
          (K.starProjection - L.starProjection) ≠ ∞ ∧
        K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau) := by
  constructor
  · rintro ⟨U, hU, huni⟩
    have hU' := (mem_charbonnierHilbertTransportMinimizers tau K L U).mp hU
    have hfinite := charbonnierCost_displacement_ne_top_of_unique_transport tau hτ.le
      K L U hU'.1 hU'.2
        (fun T hT => huni T ((mem_charbonnierHilbertTransportMinimizers tau K L T).mpr hT))
    obtain ⟨hD, hbalance⟩ :=
      (charbonnier_transport_iff_schatten_two_and_defect_balance tau hτ K L).mp ⟨U, hU'.1, hfinite⟩
    have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
      2 (by norm_num) (K.starProjection - L.starProjection) hD
    obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
      K L hcompact hbalance
    exact ⟨hD, (charbonnierHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
      tau hτ K L J hD).mp ⟨U, hU, huni⟩⟩
  · rintro ⟨hD, hgap⟩
    have hangle := smoothedCriticalAngle_mem tau hτ
    have hs1 : Real.sin (smoothedCriticalAngle tau) < 1 := by
      have h := Real.strictMonoOn_sin
        ⟨by linarith [hangle.1, Real.pi_pos], hangle.2.le⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ hangle.2
      simpa only [Real.sin_pi_div_two] using h
    have hacute : IsUniformlyAcute K L := hgap.trans_lt hs1
    have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K L hacute
    have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K L hacute
    let J := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
    exact (charbonnierHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
      tau hτ K L J hD).mpr hgap

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
