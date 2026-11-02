/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.FanDominance

/-!
# Mass budgets for finite unitary-orbit certificates

Fan dominance, the orbit-hull characterization, and unit-mass certificates are
provided by TauCeti. This donor retains the mass budget used by the Sylvester
estimates and its transport through a nonnegative scalar multiple.

## Provenance

The former rectangular majorization implementation is preserved at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Majorization.lean`
(Kitware, Apache-2.0). Its duplicated Fan-dominance engine is retired in favor
of TauCeti #14308; the bounded-factor inequalities are provided by #14662.
These accepted proofs are not asserted to descend from DKPS.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

open scoped BigOperators

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Restrict the scalar action through `ℝ → 𝕜` when forming real convex hulls of maps. -/
local instance realModuleLinearMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

/-- An orbit certificate with coefficient mass bounded by a prescribed budget. -/
@[expose]
def HasFiniteUnitaryOrbitCertificate (mass : ℝ) (X C : E →ₗ[𝕜] F) : Prop :=
  ∃ (n : ℕ) (cert : TauCeti.UnitaryOrbitCertificate (Fin n) C X), cert.mass ≤ mass

/-- A nonnegative scalar multiple of a point of the orbit hull has a certificate
with that scalar as its coefficient-mass budget. -/
theorem hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
    {m mass : ℝ} (hm : 0 ≤ m) (hmass : m ≤ mass)
    {X Y C : E →ₗ[𝕜] F}
    (hY : Y ∈ convexHull ℝ (LinearMap.twoSidedUnitaryOrbit C))
    (hX : X = ((m : 𝕜)) • Y) :
    HasFiniteUnitaryOrbitCertificate mass X C := by
  classical
  -- The compatible real action on the codomain induces the same scalar action
  -- on maps as `realModuleLinearMap`.
  let : Module ℝ F := Module.compHom F (algebraMap ℝ 𝕜)
  let : IsScalarTower ℝ 𝕜 F := IsScalarTower.of_compHom ℝ 𝕜 F
  have hHull : Y ∈ C.twoSidedUnitaryOrbitHull := by
    rwa [LinearMap.twoSidedUnitaryOrbitHull_eq_convexHull]
  obtain ⟨n, c, hc⟩ :=
    UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull hHull
  let cert : UnitaryOrbitCertificate (Fin n) C X := {
    coeff := fun i => (m : 𝕜) * c.coeff i
    left := c.left
    right := c.right
    sum_smul_comp_comp_eq := by
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, c.sum_smul_comp_comp_eq, ← hX]
  }
  refine ⟨n, cert, ?_⟩
  calc
    cert.mass = ‖(m : 𝕜)‖ * c.mass := by
      simp only [UnitaryOrbitCertificate.mass_def, cert, norm_mul, Finset.mul_sum]
    _ = m := by rw [RCLike.norm_ofReal, abs_of_nonneg hm, hc, mul_one]
    _ ≤ mass := hmass

end TauCeti.UnitarilyInvariantSeminorm
