/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockTrace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Basic

/-!
# Full Ky Fan sums are additive on positive operators

The trace norm is not additive on arbitrary operators.  It is additive on
positive endomorphisms, because their modulus equals the operator itself and
the trace of an endomorphism is linear.  This distinction is central in
assembling complex phase-corrected direct rotations without a principal-plane
enumeration.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The trace norm is additive on positive endomorphisms. -/
theorem kyFanSum_add_of_isPositive
    (A B : E →ₗ[𝕜] E) (hA : A.IsPositive) (hB : B.IsPositive) :
    (A + B).kyFanSum (finrank 𝕜 E) =
      A.kyFanSum (finrank 𝕜 E) + B.kyFanSum (finrank 𝕜 E) := by
  have htrace (C : E →ₗ[𝕜] E) (hC : C.IsPositive) :
      C.kyFanSum (finrank 𝕜 E) = RCLike.re (LinearMap.trace 𝕜 E C) := by
    rw [C.kyFanSum_eq_nuclear C.finrank_range_le, ← C.re_trace_operatorAbs,
      ← hC.eq_operatorAbs (by rw [hC.adjoint_eq])]
  rw [htrace (A + B) (hA.add hB), htrace A hA, htrace B hB, map_add, map_add]

end TauCeti
