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
and `LinearMap.polarFactor`, supplied by TauCeti. This module retains selected
square unitary factors used by alignment and direct-rotation consumers, and two
additional modulus identities.
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

section RectangularModulus

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **The modulus does not see a sign.**  `|-A| = |A|`, because the two Gram operators
`(-A)⋆(-A)` and `A⋆A` are literally the same operator and the positive square root of a
positive operator is unique. -/
theorem operatorAbs_neg (A : E →ₗ[𝕜] F) : LinearMap.operatorAbs (-A) = A.operatorAbs := by
  refine (LinearMap.IsPositive.eq_operatorAbs (A := -A)
    (A.isPositive_operatorAbs) ?_).symm
  rw [LinearMap.operatorAbs_sq, map_neg, LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]

end RectangularModulus

/-- **A normal operator and its adjoint have the same modulus.**  Normality says the two Gram
operators `A⋆A` and `AA⋆` agree, and `|A⋆|` is by definition the positive square root of the
second. -/
theorem operatorAbs_adjoint_of_normal {A : E →ₗ[𝕜] E}
    (hnormal : A.adjoint ∘ₗ A = A ∘ₗ A.adjoint) :
    LinearMap.operatorAbs (LinearMap.adjoint A) = A.operatorAbs := by
  refine (LinearMap.IsPositive.eq_operatorAbs (A := A.adjoint)
    (A.isPositive_operatorAbs) ?_).symm
  rw [LinearMap.operatorAbs_sq, LinearMap.adjoint_adjoint, hnormal]

/-! ### Invertible case: `U` is unitary -/

/-- When `A` is invertible, `|A|` is invertible and the polar factor is the unitary `U = A |A|⁻¹`,
packaged as a `LinearIsometryEquiv`. HJ 7.3.1(b) (`U` uniquely determined if `A` nonsingular). -/
@[expose]
noncomputable def polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) : E ≃ₗᵢ[𝕜] E :=
  have hinj : Function.Injective (A.polarFactor) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_polarFactor]
    exact (LinearMap.isUnit_iff_ker_eq_bot A).mp hA
  { LinearEquiv.ofBijective (A.polarFactor)
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩ with
    norm_map' := fun x => LinearMap.norm_polarFactor_apply A <| by
      rw [(LinearMap.isUnit_iff_ker_eq_bot A).mp hA, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top }

/-- The bundled polar unitary acts as the chosen one. -/
@[simp] theorem coe_polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    ((polarUnitaryEquiv hA : E →ₗ[𝕜] E)) = A.polarFactor :=
  rfl

/-- **Polar decomposition** for an operator with invertible modulus: `A = U |A|` with `U`
unitary. -/
theorem polar_decomposition_of_isUnit {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    A = (polarUnitaryEquiv hA : E →ₗ[𝕜] E) ∘ₗ A.operatorAbs := by
  rw [coe_polarUnitaryEquiv]
  exact A.polarFactor_comp_operatorAbs.symm

/-! ### General square case: a kernel-completed unitary

Even for a singular `A`, the partial isometry `A.polarFactor` extends to a
genuine unitary `E ≃ₗᵢ[𝕜] E` — map the initial space `(ker A)ᗮ` by
`A.polarFactor` (isometrically onto `range A`) and complete `ker A`
isometrically onto `(range A)ᗮ` (equal dimensions by rank–nullity).  The
identity `A = U |A|` survives, and `U` is a true unitary; this is the factor the
orthogonal-Procrustes alignment argument needs (`polarUnitaryEquiv` above
requires invertibility).

**The completion is a choice, not a canonical construction.**  When `ker A ≠ ⊥`
*any* unitary from `ker A` onto `(range A)ᗮ` completes `A.polarFactor`, and
the accepted extension theorem selects one; only the restriction to `(ker A)ᗮ`
is determined by `A`.  Hence the name `choosePolarUnitary` rather than
`polarUnitary`: the invertible case, where the unitary factor really is unique,
is `polarUnitaryEquiv` above.

Users who need only *some* unitary factor should prefer
`exists_polar_decomposition_unitary`, which states the theorem without
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
`exists_polar_decomposition_unitary`. -/
theorem polar_decomposition_choosePolarUnitary (A : E →ₗ[𝕜] E) :
    A = (choosePolarUnitary A : E →ₗ[𝕜] E) ∘ₗ A.operatorAbs := by
  ext x
  simp only [LinearMap.comp_apply]
  exact (choosePolarUnitary_apply_operatorAbs_apply A x).symm

/-- **Polar decomposition with a unitary factor**, existential form.

This is the honest general-case statement: every square operator on a
finite-dimensional space factors as a unitary times its modulus.  It says
nothing about *which* unitary, which is the point — for singular `A` the factor
is not unique.  `choosePolarUnitary` provides a witness when a concrete one is
needed. -/
theorem exists_polar_decomposition_unitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ A.operatorAbs :=
  ⟨choosePolarUnitary A, polar_decomposition_choosePolarUnitary A⟩

end TauCeti
