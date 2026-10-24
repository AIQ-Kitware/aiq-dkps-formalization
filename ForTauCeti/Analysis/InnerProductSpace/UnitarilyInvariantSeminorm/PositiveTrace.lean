/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockTrace

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

/-- The operator modulus of a positive endomorphism is the endomorphism
itself. -/
theorem operatorAbs_eq_self_of_isPositive (A : E →ₗ[𝕜] E)
    (hA : A.IsPositive) : operatorAbs A = A := by
  symm
  exact (LinearMap.isPositive_adjoint_comp_self A).sqrt_unique hA (by
    rw [hA.adjoint_eq])

/-- Full Ky Fan sum of a positive endomorphism is its ordinary trace, in
any orthonormal basis. -/
theorem kyFanSum_positive_eq_basis_trace (A : E →ₗ[𝕜] E)
    (hA : A.IsPositive)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    kyFanSum (finrank 𝕜 E) A =
      ∑ i : Fin (finrank 𝕜 E), RCLike.re ⟪A (b i), b i⟫_𝕜 := by
  calc
    kyFanSum (finrank 𝕜 E) A =
        ∑ i : Fin (finrank 𝕜 E), A.singularValues i :=
      kyFanSum_eq_sum_fin _ A
    _ = ∑ i : Fin (finrank 𝕜 E),
        RCLike.re ⟪operatorAbs A (b i), b i⟫_𝕜 :=
      (sum_re_inner_abs_self_eq_sum_singularValues A rfl b).symm
    _ = ∑ i : Fin (finrank 𝕜 E), RCLike.re ⟪A (b i), b i⟫_𝕜 := by
      rw [operatorAbs_eq_self_of_isPositive A hA]

/-- The trace norm is additive on positive endomorphisms. -/
theorem kyFanSum_add_of_isPositive
    (A B : E →ₗ[𝕜] E) (hA : A.IsPositive) (hB : B.IsPositive) :
    kyFanSum (finrank 𝕜 E) (A + B) =
      kyFanSum (finrank 𝕜 E) A + kyFanSum (finrank 𝕜 E) B := by
  let b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
    stdOrthonormalBasis 𝕜 E
  rw [kyFanSum_positive_eq_basis_trace (A + B) (hA.add hB) b,
    kyFanSum_positive_eq_basis_trace A hA b,
    kyFanSum_positive_eq_basis_trace B hB b]
  simp only [LinearMap.add_apply, inner_add_left, map_add,
    Finset.sum_add_distrib]

end TauCeti
