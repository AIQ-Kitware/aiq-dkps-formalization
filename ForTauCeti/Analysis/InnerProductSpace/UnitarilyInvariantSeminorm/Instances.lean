/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Trace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Basic
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# DKPS extensions for rectangular unitarily invariant seminorms

Tau Ceti owns the standard operator, Frobenius, Ky Fan, nuclear, and Schatten seminorms and
their ideal inequalities. This file retains only DKPS-specific finite-dimensional facts that do
not appear in the accepted API.

## Provenance

The deleted standard seminorm constructors and their defining proofs duplicated the corresponding
Tau Ceti modules. The retained result relates the nuclear norm of a Gram operator to column energy.
-/

public section

open scoped InnerProductSpace BigOperators
open Module (finrank)

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The nuclear seminorm of a Gram operator is the sum of squared column norms in any
orthonormal basis. -/
theorem nuclear_adjoint_comp_self_eq_sum_sq_norm
    (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    nuclear 𝕜 E E (A.adjoint ∘ₗ A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  let G := A.adjoint ∘ₗ A
  have hG : G.IsPositive := LinearMap.isPositive_adjoint_comp_self A
  have hGabs : G.operatorAbs = G := by
    symm
    exact hG.eq_operatorAbs (by
      rw [hG.adjoint_eq])
  calc
    _ = RCLike.re (LinearMap.trace 𝕜 E G.operatorAbs) := G.re_trace_operatorAbs.symm
    _ = _ := by
      rw [hGabs]
      change RCLike.re (LinearMap.trace 𝕜 E (A.adjoint ∘ₗ A)) = _
      rw [A.trace_adjoint_comp_self_eq_sum_norm_apply_sq b]
      exact RCLike.ofReal_re _

end TauCeti.UnitarilyInvariantSeminorm
