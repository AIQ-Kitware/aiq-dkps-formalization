/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.Geometry.Polar.DirectRotationRank

/-!
# Exact transport minima for balanced finite-rank projection perturbations

The hypotheses concern the projection pair itself: finite-rank
projection difference and equality of the two finite crossed-defect
dimensions. No feasible near-identity reference has to be supplied.
Subspaces of infinite rank and corank and nonseparable ambient spaces
are included.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Exact minimum from conditions on the projection pair.** For
`1<=p<2`, finite-rank projection difference and balanced crossed defects
give a finite-rank optimizer against every ambient complex unitary. -/
theorem exists_unitary_minimizing_schatten_transport_of_finite_rank_projection_sub
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 ≤ p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal =
        (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge (1 - (T : E →L[ℂ] E)) := by
  obtain ⟨R, hRmap, hR⟩ :=
    exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
  exact exists_unitary_minimizing_schatten_transport_of_finite_rank_reference
    p hp hp1 hp2 K L R hRmap n hR

/-- The exact nuclear value for a balanced finite-rank projection pair
is twice the nuclear directed sine gauge, attained by a finite-rank
unitary and compared against every ambient competitor. -/
theorem exists_unitary_minimizing_nuclear_transport_of_finite_rank_projection_sub
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) =
        2 * (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (K.sinThetaMap L) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (T : E →L[ℂ] E)) := by
  obtain ⟨R, hRmap, hR⟩ :=
    exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
  exact exists_unitary_minimizing_nuclear_transport_of_finite_rank_reference K L R hRmap n hR

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
