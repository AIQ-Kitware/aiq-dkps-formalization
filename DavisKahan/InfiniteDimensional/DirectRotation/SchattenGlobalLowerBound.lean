/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFiniteRank
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenAngleContinuity
public import ForTauCeti.Analysis.InnerProductSpace.SchattenUnitaryApproximation

/-!
# The unrestricted Schatten transport lower bound in Hilbert space

Truncate the competing unitary itself. The target projection varies,
but every fixed singular-value penalty converges in operator norm.
Nonnegativity passes finite partial-sum lower bounds to the full sum.
No finite-rank reference, separability or defect-balance hypothesis is
needed for this lower bound. Feasibility is expressed by the actual
ambient unitary transporter.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every fixed singular-value phase penalty is continuous in operator
norm, even at zero displacement and critical angles. -/
theorem continuous_sine_phaseMinimum_singularValue (p : ℝ) (hp : 0 ≤ p) (j : ℕ) :
    Continuous (fun A : E →L[ℂ] E => ENNReal.ofReal
      (phaseMinimum p (Real.arcsin (A.singularValue j : ℝ)))) := by
  have hangle : Continuous (fun A : E →L[ℂ] E => Real.arcsin (A.singularValue j : ℝ)) :=
    Real.continuous_arcsin.comp (NNReal.continuous_coe.comp
      (ContinuousLinearMap.continuous_singularValue j))
  have h := (continuousOn_phaseMinimum_angle p hp).comp_continuous hangle
    (fun A => Real.arcsin_nonneg.mpr (NNReal.coe_nonneg (A.singularValue j)))
  exact ENNReal.continuous_ofReal.comp h

/-- **The unrestricted Hilbert-space Schatten lower bound.** For
`1<=p<2`, every complex unitary transport dominates the intrinsic ambient
principal-angle phase sum. No rank, separability, compactness or
ideal-membership assumption is imposed on the subspaces or competitor. -/
theorem sine_phaseMinimum_sum_le_schatten_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 ≤ p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
  by_cases hU : Φ.gauge (1 - (U : E →L[ℂ] E)) = ∞
  · change _ ≤ Φ.gauge (1 - (U : E →L[ℂ] E)) ^ p.toReal
    rw [hU, ENNReal.top_rpow_of_pos hp0]
    exact le_top
  have hU' : Φ.gauge ((U : E →L[ℂ] E) - 1) ≠ ∞ := by
    rw [← neg_sub 1 (U : E →L[ℂ] E), Φ.gauge_neg]
    exact hU
  obtain ⟨V, N, hN, hlim, _, hcost, _⟩ :=
    exists_schatten_finite_unitary_approximation_sequence p.toReal hp1 U hU'
  let S (A : E →L[ℂ] E) := (1 - A * K.starProjection * star A) * K.starProjection
  have hS : Continuous S := by dsimp only [S]; fun_prop
  have hsin (W : E ≃ₗᵢ[ℂ] E) : K.sinThetaMap (K.map W.toLinearMap) = S (W : E →L[ℂ] E) := by
    have hproj := (K.map_eq_iff_conjugate_starProjection (K.map W.toLinearMap) W).mp rfl
    rw [Submodule.sinThetaMap_def, Submodule.starProjection_orthogonal, ← hproj]
    rfl
  suffices (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
      (Real.arcsin ((S (U : E →L[ℂ] E)).singularValue j : ℝ)))) ≤
        Φ.gauge (1 - (U : E →L[ℂ] E)) ^ p.toReal by
    simpa only [← hsin, hmap] using this
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hterm (j : ℕ) :=
    (((continuous_sine_phaseMinimum_singularValue p.toReal hp0.le j).comp hS).tendsto
      (U : E →L[ℂ] E)).comp hlim
  have hsum := tendsto_finsetSum s (fun j _ => hterm j)
  apply le_of_tendsto' hsum
  intro n
  calc
    _ ≤ ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
        (Real.arcsin ((S (V n : E →L[ℂ] E)).singularValue j : ℝ))) := ENNReal.sum_le_tsum s
    _ = ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
        (Real.arcsin ((K.sinThetaMap (K.map (V n).toLinearMap)).singularValue j : ℝ))) := by
      rw [← hsin]
    _ ≤ Φ.gauge (1 - (V n : E →L[ℂ] E)) ^ p.toReal :=
      sine_phaseMinimum_sum_le_schatten_finite_rank_transport p hp hp1 hp2 K
        (K.map (V n).toLinearMap) (V n) rfl (N n) (hN n)
    _ ≤ Φ.gauge (1 - (U : E →L[ℂ] E)) ^ p.toReal :=
      ENNReal.rpow_le_rpow (hcost n Φ) hp0.le

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
