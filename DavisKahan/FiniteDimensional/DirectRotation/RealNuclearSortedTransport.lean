/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearSortedMinimum
public import Mathlib.Data.Finset.Sort

/-!
# Exact unrestricted real nuclear transport by two sorted sums

Enumerate the original strictly positive principal-angle labels in their
inherited order. Their angles are decreasing, including all repetitions.
The unrestricted real nuclear transport minimum is the smaller of two
adjacent sums, and an actual ambient orthogonal transporter attains it.

The ambient minimal-distortion problem is prior art (Bolotnikov--Li--Rodman
2001, Problem 1.1), and finite matching exchanges are classical. The exact
transport matching solution and this sorting consequence are extensions whose
historical priority remains unresolved. See the maintained source-to-Lean map.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The decreasing sequence of strictly positive principal angles, with
one entry for each original positive label, including all multiplicities. -/
@[expose] def orderedPositivePrincipalAngles (K L : Submodule ℝ E) :
    Fin (Fintype.card {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}) → ℝ :=
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let e := Fintype.orderIsoFinOfCardEq J rfl
  fun i => K.principalAngles L (e i).val

/-- The ordered enumeration retains strictly positive physical angles. -/
theorem orderedPositivePrincipalAngles_mem (K L : Submodule ℝ E)
    (i : Fin (Fintype.card {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j})) :
    orderedPositivePrincipalAngles K L i ∈ Ioc 0 (Real.pi / 2) := by
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let e := Fintype.orderIsoFinOfCardEq J rfl
  exact ⟨(e i).property, K.principalAngles_le_pi_div_two L (e i).val⟩

/-- Enumeration of positive labels preserves the accepted decreasing
principal-angle order; no distinctness assumption is imposed. -/
theorem antitone_orderedPositivePrincipalAngles (K L : Submodule ℝ E) :
    Antitone (orderedPositivePrincipalAngles K L) := by
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let e := Fintype.orderIsoFinOfCardEq J rfl
  intro i j hij
  change K.principalAngles L (e j).val ≤ K.principalAngles L (e i).val
  apply K.principalAngles_antitone L
  exact e.monotone hij

/-- **Exact two-sorted-sums formula for the unrestricted real nuclear
transport value.** The empty angle list gives zero. Otherwise the costs are
adjacent pairing with a possible final canonical singleton, or reflection
of the largest angle followed by the same adjacent rule on the tail. -/
theorem realTransportPowerMinimum_one_eq_sorted
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    realTransportPowerMinimum 1 K L =
      nuclearSortedMinimum (orderedPositivePrincipalAngles K L) := by
  let J := {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j}
  let theta : J → ℝ := fun j => K.principalAngles L j.val
  let e := Fintype.orderIsoFinOfCardEq J rfl
  rw [realTransportPowerMinimum_one_eq_nuclearMatching K L hKL]
  change realNuclearMatchingMinimum theta = _
  calc
    realNuclearMatchingMinimum theta = realNuclearMatchingMinimum (theta ∘ e.toEquiv) :=
      (realNuclearMatchingMinimum_reindex theta e.toEquiv).symm
    _ = nuclearSortedMinimum (orderedPositivePrincipalAngles K L) :=
      realNuclearMatchingMinimum_eq_sorted _ (orderedPositivePrincipalAngles K L)
        (fun i => ⟨(orderedPositivePrincipalAngles_mem K L i).1.le,
          (orderedPositivePrincipalAngles_mem K L i).2⟩)
        (antitone_orderedPositivePrincipalAngles K L)

/-- The two-sum value is attained by an actual ambient orthogonal
transporter and bounds every ambient orthogonal competitor, in every finite
dimension. Zero/repeated/right angles and both determinant classes are included. -/
theorem exists_minimizing_real_nuclear_transport_sorted
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    ∃ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - T.toLinearMap) =
        nuclearSortedMinimum (orderedPositivePrincipalAngles K L) ∧
      ∀ V : E ≃ₗᵢ[ℝ] E, K.map V.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - T.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - V.toLinearMap) := by
  obtain ⟨T, hmap, hcost, hmin⟩ := exists_minimizing_real_nuclear_transport_matching K L hKL
  refine ⟨T, hmap, ?_, hmin⟩
  exact hcost.trans ((realTransportPowerMinimum_one_eq_nuclearMatching K L hKL).symm.trans
    (realTransportPowerMinimum_one_eq_sorted K L hKL))

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
