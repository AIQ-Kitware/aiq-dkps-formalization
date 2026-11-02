/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T09.  Formalized by Claude Opus 5
(claude-opus-5[1m]).
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Self-adjointness of real infinite diagonal multipliers

Tau Ceti owns `lp.diagonalCLM`, its truncations, norm/rank estimates, compactness
and approximation-number formulas. The former `diagOpLp` and its proof engine
are retired. This donor retains only self-adjointness for star-fixed coefficients
on ℓ², a statement absent from the accepted diagonal modules.

Historical source: `e4637c3919ae` under this module path, authored in place at
`b24cd4145659ca6cc8784c53ec0fea30a09ae328`; Jon Crall / Claude Opus 5,
Kitware Inc., Apache-2.0. The coordinate inner-product proof below is adapted
from the original `TauCeti.isSelfAdjoint_diagOpLp`, on the native operator carrier.
-/

public section

namespace lp

open scoped ENNReal InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A bounded infinite diagonal multiplier on ℓ² is self-adjoint when each
coefficient is fixed by the scalar star operation. -/
theorem isSelfAdjoint_diagonalCLM (d : lp (fun _ : ℕ => 𝕜) ∞)
    (hreal : ∀ i, (starRingEnd 𝕜) (d i) = d i) :
    IsSelfAdjoint (diagonalCLM (p := 2) d) := by
  have hsymm : (diagonalCLM (p := 2) d).IsSymmetric := by
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    simp only [ContinuousLinearMap.coe_coe, diagonalCLM_apply, RCLike.inner_apply, map_mul,
      hreal i]
    ring
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr hsymm.clm_adjoint_eq

end lp
