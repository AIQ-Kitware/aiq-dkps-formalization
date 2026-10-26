/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedAngleContinuity
public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierFinite
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence

/-!
# The unrestricted smoothed transport lower bound in Hilbert space

The exact finite-dimensional phase formula gives an intrinsic extended
principal-angle lower bound against every ambient complex unitary
transporter. Finite Charbonnier cost supplies Hilbert--Schmidt
compactness. Spectral truncations decrease every displacement singular
value, so they also decrease the literal smoothed objective.

No finite-rank reference, separability, defect balance or prescribed
competitor block form is assumed. This is a lower bound, not general
infinite-rank attainment.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Restrict a finite-rank competitor to its actual reducing support;
no prescribed principal-plane form is imposed. -/
theorem sine_smoothedPhaseMinimum_sum_le_finite_rank_transport
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (n : ℕ) (hU : (1 - U.toLinearMap).rank ≤ n) :
    (∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau := by
  obtain ⟨M, hM, _, V, _, hlocal, hK, hL, heq, hdisp⟩ :=
    K.exists_finite_transport_section L ⊥ U hmap n hU
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  have hdim := V.toLinearEquiv.finrank_map_eq K₀
  rw [hlocal] at hdim
  have hcost : (1 - (V : M →L[ℂ] M)).charbonnierCost tau =
      ENNReal.ofReal (smoothedDisplacementCost tau V.toLinearMap) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  rw [Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core K L M hK hL heq
    (fun t => ENNReal.ofReal (smoothedPhaseMinimum tau t))
    (by rw [smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero]),
    hdisp, ContinuousLinearMap.charbonnierCost_orthogonal_extension, hcost]
  change (∑ i : Fin (Module.finrank ℂ K₀),
    ENNReal.ofReal (smoothedPhaseMinimum tau (K₀.principalAngles L₀ i))) ≤ _
  have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
      0 ≤ smoothedPhaseMinimum tau (K₀.principalAngles L₀ i) :=
    smoothedPhaseMinimum_nonneg tau _ hτ
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨_, _, _, hmin⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau hτ K₀ L₀ hdim.symm
  exact hmin V hlocal

omit [CompleteSpace E] in
/-- Every individual smoothed angle penalty is norm-continuous,
including zero, critical and right angles. -/
theorem continuous_sine_smoothedPhaseMinimum_singularValue
    (tau : ℝ) (hτ : 0 < tau) (j : ℕ) :
    Continuous (fun A : E →L[ℂ] E => ENNReal.ofReal
      (smoothedPhaseMinimum tau (Real.arcsin (A.singularValue j : ℝ)))) := by
  have hangle : Continuous (fun A : E →L[ℂ] E => Real.arcsin (A.singularValue j : ℝ)) :=
    Real.continuous_arcsin.comp (NNReal.continuous_coe.comp
      (ContinuousLinearMap.continuous_singularValue j))
  have h := (continuousOn_smoothedPhaseMinimum_angle tau hτ).comp_continuous hangle
    (fun A => ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg (A.singularValue j)),
      Real.arcsin_le_pi_div_two _⟩)
  exact ENNReal.continuous_ofReal.comp h

/-- **The unrestricted Hilbert-space smoothed lower bound.** Every
complex unitary transport dominates the exact intrinsic angle sum.
The projection difference and displacement may have infinite rank,
and the objective and lower bound may be infinite. -/
theorem sine_smoothedPhaseMinimum_sum_le_transport
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau := by
  by_cases hU : (1 - (U : E →L[ℂ] E)).charbonnierCost tau = ∞
  · rw [hU]
    exact le_top
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hU
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2
    (by norm_num) (1 - (U : E →L[ℂ] E)) hSp
  have hcompact' : IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E) := by
    rw [← neg_sub 1 (U : E →L[ℂ] E)]
    exact hcompact.neg
  obtain ⟨V, N, hN, hlim, _, _, hdom, _⟩ :=
    exists_finite_unitary_approximation_sequence U hcompact'
  let S (A : E →L[ℂ] E) := (1 - A * K.starProjection * star A) * K.starProjection
  have hS : Continuous S := by dsimp only [S]; fun_prop
  have hsin (W : E ≃ₗᵢ[ℂ] E) : K.sinThetaMap (K.map W.toLinearMap) = S (W : E →L[ℂ] E) := by
    have hproj := (K.map_eq_iff_conjugate_starProjection (K.map W.toLinearMap) W).mp rfl
    rw [Submodule.sinThetaMap_def, Submodule.starProjection_orthogonal, ← hproj]
    rfl
  suffices (∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
      (Real.arcsin ((S (U : E →L[ℂ] E)).singularValue j : ℝ)))) ≤
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau by
    simpa only [← hsin, hmap] using this
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hterm (j : ℕ) :=
    (((continuous_sine_smoothedPhaseMinimum_singularValue tau hτ j).comp hS).tendsto
      (U : E →L[ℂ] E)).comp hlim
  have hsum := tendsto_finsetSum s (fun j _ => hterm j)
  apply le_of_tendsto' hsum
  intro n
  calc
    _ ≤ ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((S (V n : E →L[ℂ] E)).singularValue j : ℝ))) := ENNReal.sum_le_tsum s
    _ = ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K.sinThetaMap (K.map (V n).toLinearMap)).singularValue j : ℝ))) := by
      rw [← hsin]
    _ ≤ (1 - (V n : E →L[ℂ] E)).charbonnierCost tau :=
      sine_smoothedPhaseMinimum_sum_le_finite_rank_transport tau hτ K
        (K.map (V n).toLinearMap) (V n) rfl (N n) (hN n)
    _ ≤ (1 - (U : E →L[ℂ] E)).charbonnierCost tau :=
      ContinuousLinearMap.charbonnierCost_le_of_singularValue_le tau _ _ (hdom n)

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
