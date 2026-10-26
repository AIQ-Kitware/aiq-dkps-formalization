/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenSpectralCutoff

/-!
# Finite reducing cutoffs for compact projection differences

The sine spectral sector above a positive threshold is finite, reduces
both projections and every completed direct rotation, and leaves a
tail whose projection gap is at most the threshold. A native Schatten
power gives an explicit dimension bound for this sector. This isolates
the finite sector where a positive-angle phase transition can occur;
it does not by itself prove infinite-rank optimizer attainment.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The strict sine spectral sector above a positive cutoff is a finite
common reducing block, and its complementary projection gap is at most
that cutoff. Both fields and arbitrary Hilbert dimensions are included. -/
theorem finite_sine_spectral_cutoff
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H))
    (c : ℝ) (hc : 0 < c) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    FiniteDimensional 𝕜 M ∧ M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧
      ‖(K.starProjection - L.starProjection) ∘L Mᗮ.subtypeL‖ ≤ c := by
  let S := K.sinAngleOperator L
  let M := eigenSpan S (Set.Ioi c)
  have hSc : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have heq : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      dsimp only [S]
      rw [Submodule.sinAngleOperator_def, ContinuousLinearMap.singularValue_modulus]
    rw [heq]
    exact hD.tendsto_singularValue
  have hSs : IsSelfAdjoint S := (K.isPositive_sinAngleOperator L).isSelfAdjoint
  have hM : FiniteDimensional 𝕜 M :=
    finiteDimensional_eigenSpan hSc hSs hc (fun _ hs => hs.le)
  have hK : M.IsReducing K.starProjection.toLinearMap := by
    apply (LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule
      K.starProjection_isSymmetric M).mpr
    exact eigenSpan_invariant_of_commute S K.starProjection
      (K.commute_starProjection_sinAngleOperator L) _
  have hL : M.IsReducing L.starProjection.toLinearMap := by
    apply (LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule
      L.starProjection_isSymmetric M).mpr
    apply eigenSpan_invariant_of_commute S L.starProjection _ _
    change Commute L.starProjection (K.sinAngleOperator L)
    rw [← Submodule.sinAngleOperator_comm K L]
    exact L.commute_starProjection_sinAngleOperator K
  refine ⟨hM, hK, hL, ?_⟩
  have htail : ‖S ∘L Mᗮ.subtypeL‖ ≤ c :=
    norm_comp_orthogonal_eigenSpan_le hSc hSs
      ((K.isPositive_sinAngleOperator L).re_inner_nonneg_left) hc.le (fun _ hs => hs)
  apply ContinuousLinearMap.opNorm_le_bound _ hc.le
  intro x
  calc
    _ = ‖S (x : H)‖ := (K.norm_sinAngleOperator_apply L (x : H)).symm
    _ ≤ ‖S ∘L Mᗮ.subtypeL‖ * ‖x‖ := (S ∘L Mᗮ.subtypeL).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (norm_nonneg x)

/-- Every completed direct rotation reduces each sine spectral cutoff,
including its critical and right-angle sectors. -/
theorem sine_spectral_cutoff_isReducing_nonacuteDirectRotation
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H))
    (c : ℝ) (hc : 0 < c) :
    (eigenSpan (K.sinAngleOperator L) (Set.Ioi c)).IsReducing
      (nonacuteDirectRotation K L J).toLinearMap := by
  let S := K.sinAngleOperator L
  let R := nonacuteDirectRotation K L J
  let : FiniteDimensional 𝕜 (eigenSpan S (Set.Ioi c)) :=
    (finite_sine_spectral_cutoff K L hD c hc).1
  have hRS : Commute R S := nonacuteDirectRotation_comm_sinAngleOperator K L J
  have hstar : Commute (star R) S := by
    have h := commute_star_star.mpr hRS
    rwa [(K.isPositive_sinAngleOperator L).isSelfAdjoint.star_eq] at h
  apply ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr
  exact ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (eigenSpan_invariant_of_commute S R hRS _),
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (eigenSpan_invariant_of_commute S (star R) hstar _)⟩

/-- The size of the finite sector above `c` is controlled explicitly
by the Schatten power of the projection difference. -/
theorem finrank_sine_spectral_cutoff_mul_rpow_le_schatten_projection_sub
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H))
    (c : ℝ) (hc : 0 < c) :
    (Module.finrank 𝕜 (eigenSpan (K.sinAngleOperator L) (Set.Ioi c)) : ℝ≥0∞) *
      ENNReal.ofReal c ^ p ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge
          (K.starProjection - L.starProjection) ^ p := by
  have hSc : IsCompactOperator (K.sinAngleOperator L) := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have heq : (K.sinAngleOperator L).singularValue =
        (K.starProjection - L.starProjection).singularValue := by
      funext n
      rw [Submodule.sinAngleOperator_def, ContinuousLinearMap.singularValue_modulus]
    rw [heq]
    exact hD.tendsto_singularValue
  have h := finrank_eigenSpan_mul_cutoff_rpow_le_schatten_rpow p hp
    (K.sinAngleOperator L) hSc (K.isPositive_sinAngleOperator L).isSelfAdjoint
    c hc (Set.Ioi c) (fun _ hs => hs.le)
  simpa only [OperatorIdealFamily.gauge_schatten, Submodule.sinAngleOperator_def,
    ContinuousLinearMap.singularValue_modulus] using h

end TauCeti.DavisKahan
