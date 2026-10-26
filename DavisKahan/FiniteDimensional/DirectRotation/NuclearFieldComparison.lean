/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearFieldEquality
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNuclearEndpoint

/-!
# When real and complex nuclear transport have the same optimum

For finite real and complex pairs with the same accepted principal-angle
data, the complex optimum is a lower bound for the real optimum. Equality
holds exactly when every strictly acute positive angle has even real
multiplicity. The comparison includes every ambient transporter in both
fields and does not impose a determinant or block restriction.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set SchattenPhaseTransition
open scoped BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- For equal principal-angle data in the two fields, an actual complex
nuclear minimizer has cost at most the unrestricted real minimum. The
two minima agree precisely when every strictly acute positive angle has
even multiplicity. Common fixed directions may have different dimensions. -/
theorem exists_complex_nuclear_minimum_with_real_parity_criterion
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L)
    (U V : Submodule ℂ F) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hn : Module.finrank ℝ K = Module.finrank ℂ U)
    (hangles : ∀ i : Fin (Module.finrank ℝ K),
      K.principalAngles L i = U.principalAngles V (Fin.cast hn i)) :
    ∃ C : F ≃ₗᵢ[ℂ] F, U.map C.toLinearMap = V ∧
      (∀ T : F ≃ₗᵢ[ℂ] F, U.map T.toLinearMap = V →
        UnitarilyInvariantSeminorm.schatten ℂ F F 1 (LinearMap.id - C.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℂ F F 1 (LinearMap.id - T.toLinearMap)) ∧
      UnitarilyInvariantSeminorm.schatten ℂ F F 1 (LinearMap.id - C.toLinearMap) ≤
        realTransportPowerMinimum 1 K L ∧
      (realTransportPowerMinimum 1 K L =
          UnitarilyInvariantSeminorm.schatten ℂ F F 1 (LinearMap.id - C.toLinearMap) ↔
        ∀ t ∈ Ioo 0 (Real.pi/2),
          Even (Nat.card {i : Fin (Module.finrank ℝ K) // K.principalAngles L i = t})) := by
  classical
  obtain ⟨C, hC, hcost, hmin⟩ :=
    exists_unitary_minimizing_nuclear_transport_principalAngles_complex U V hUV
  have hsum : (∑ i : Fin (Module.finrank ℝ K), 2 * Real.sin (K.principalAngles L i)) =
      ∑ i : Fin (Module.finrank ℂ U), 2 * Real.sin (U.principalAngles V i) := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ K),
          2 * Real.sin (U.principalAngles V (Fin.cast hn i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hangles i]
      _ = _ := (finCongr hn).sum_comp (fun i => 2 * Real.sin (U.principalAngles V i))
  refine ⟨C, hC, fun T hT => hcost.trans_le (hmin T hT), ?_, ?_⟩
  · rw [hcost, ← hsum]
    let theta : Fin (Module.finrank ℝ K) → ℝ := fun i => K.principalAngles L i
    let J := {i : Fin (Module.finrank ℝ K) // 0 < theta i}
    have htheta (i) : theta i ∈ Icc 0 (Real.pi/2) :=
      ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
    have hzero (i : {i // ¬0 < theta i}) : 2 * Real.sin (theta i.val) = 0 := by
      have hi : theta i.val = 0 := le_antisymm (le_of_not_gt i.property) (htheta i.val).1
      simp [hi]
    have hpositive := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < theta i)
      (fun i => 2 * Real.sin (theta i))
    rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero] at hpositive
    rw [realTransportPowerMinimum_one_eq_nuclearMatching K L hKL, ← hpositive]
    obtain ⟨s, _, hvalue⟩ := exists_attains_realNuclearMatchingMinimum (fun i : J => theta i.val)
    exact (nuclear_sine_sum_le_matching (fun i : J => theta i.val)
      (fun i => htheta i.val) s).trans_eq hvalue
  · rw [hcost, ← hsum]
    exact realTransportPowerMinimum_one_eq_sine_sum_iff_even_multiplicities K L hKL

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
