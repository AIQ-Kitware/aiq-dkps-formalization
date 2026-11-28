/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Finite
public import ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Selected unitary factors and extra modulus identities

The modulus and canonical polar partial isometry are `LinearMap.operatorAbs`
and `LinearMap.polarFactor`, supplied by TauCeti. This module retains the selected
square unitary factor used by alignment consumers.
The singular-case choice comes from the accepted unitary-extension theorem;
its action on the kernel is not canonical.

## Provenance

Extracted from `ForMathlib.Analysis.InnerProductSpace.PolarDecomposition`,
introduced at DKPS commit `3676b55`. Original authors Jon Crall and Claude Opus 4.8,
Kitware copyright, Apache-2.0. The duplicate modulus and polar-factor engines were
retired in favor of the accepted rectangular RCLike APIs.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open LinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ### General square case: a kernel-completed unitary

Even for a singular `A`, the partial isometry `A.polarFactor` extends to a
genuine unitary `E ≃ₗᵢ[𝕜] E` — map the initial space `(ker A)ᗮ` by
`A.polarFactor` (isometrically onto `range A`) and complete `ker A`
isometrically onto `(range A)ᗮ` (equal dimensions by rank–nullity).  The
identity `A = U |A|` survives, and `U` is a true unitary; this is the factor the
orthogonal-Procrustes alignment argument needs.

**The completion is a choice, not a canonical construction.**  When `ker A ≠ ⊥`
*any* unitary from `ker A` onto `(range A)ᗮ` completes `A.polarFactor`, and
the accepted extension theorem selects one; only the restriction to `(ker A)ᗮ`
is determined by `A`.  Hence the name `choosePolarUnitary` rather than
`polarUnitary`: the invertible case, where the unitary factor really is unique,
is supplied by `(A.polarIsometry hinj).toLinearIsometryEquiv rfl`.

Users who need only *some* unitary factor should prefer
`LinearMap.exists_linearIsometryEquiv_comp_operatorAbs_eq`, which states the theorem without
committing to the selection. -/

/-- A selected unitary extension of the canonical polar factor.
The choice on the kernel is not canonical. -/
noncomputable def choosePolarUnitary (A : E →ₗ[𝕜] E) : E ≃ₗᵢ[𝕜] E :=
  (A.exists_linearIsometryEquiv_eqOn_polarFactor rfl).choose

/-- The chosen polar unitary satisfies the defining identity `U (|A| x) = A x`.  It is *a* choice --
see `choosePolarUnitary` -- but every choice satisfies this. -/
@[simp]
theorem choosePolarUnitary_apply_operatorAbs_apply (A : E →ₗ[𝕜] E) (x : E) :
    choosePolarUnitary A (A.operatorAbs x) = A x := by
  have hmem : A.operatorAbs x ∈ (ker A)ᗮ := by
    rw [← LinearMap.range_operatorAbs A]
    exact LinearMap.mem_range_self _ x
  exact ((A.exists_linearIsometryEquiv_eqOn_polarFactor rfl).choose_spec hmem).trans
    (A.polarFactor_operatorAbs_apply x)

/-- **Polar decomposition with a unitary factor** (general square case),
`A = U |A|` at the selected witness `U = choosePolarUnitary A`.

For the statement that does not name a witness, use
`LinearMap.exists_linearIsometryEquiv_comp_operatorAbs_eq`. -/
theorem polar_decomposition_choosePolarUnitary (A : E →ₗ[𝕜] E) :
    A = (choosePolarUnitary A : E →ₗ[𝕜] E) ∘ₗ A.operatorAbs := by
  ext x
  simp only [LinearMap.comp_apply]
  exact (choosePolarUnitary_apply_operatorAbs_apply A x).symm

end TauCeti
