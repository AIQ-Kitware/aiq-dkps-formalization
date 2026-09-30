/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
public import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Modulus invariance for symmetric operator-ideal families

A symmetric operator-ideal gauge assigns the same value to a bounded operator
`T : E →L[K] F` and to its positive modulus `|T| : E →L[K] E`.

The proof uses only the two polar factorizations

* `T = W |T|`, and
* `|T| = W* T`,

where the polar partial isometry `W` and its adjoint are contractions.  The
statement is rectangular and scalar-generic over `RCLike`; no unitary extension
of `W` and no approximation-number argument is needed.
-/

public section

namespace TauCeti
namespace SymmetricOperatorIdealFamily

open scoped InnerProductSpace ENNReal

noncomputable section

universe u v

variable {K : Type u} [RCLike K]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]

/-- The polar partial isometry of a rectangular bounded operator is a contraction. -/
theorem norm_polarPartial_le_one_rectangular (T : E →L[K] F) :
    ‖T.polarPartial‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, T.polarPartial_apply, T.norm_polarInitialMap_apply]
  exact T.polarInitial.norm_orthogonalProjectionOnto_apply_le x

/-- The polar partial isometry and its adjoint are contractions in `enorm`. -/
theorem polarPartial_and_adjoint_enorm_le_one_rectangular (T : E →L[K] F) :
    ‖T.polarPartial‖ₑ ≤ 1 ∧ ‖T.polarPartial.adjoint‖ₑ ≤ 1 := by
  have hU : ‖T.polarPartial‖ ≤ 1 := norm_polarPartial_le_one_rectangular T
  have hUa : ‖T.polarPartial.adjoint‖ ≤ 1 := by
    calc
      ‖T.polarPartial.adjoint‖ = ‖T.polarPartial‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hU
  constructor <;> rw [← ofReal_norm, ← ENNReal.ofReal_one]
  · exact ENNReal.ofReal_le_ofReal hU
  · exact ENNReal.ofReal_le_ofReal hUa

/-- A symmetric operator-ideal gauge is invariant under the rectangular modulus. -/
theorem gauge_modulus_eq
    (N : SymmetricOperatorIdealFamily.{u, v} K) (T : E →L[K] F) :
    N.toOperatorIdealFamily.gauge T.modulus =
      N.toOperatorIdealFamily.gauge T := by
  let S := N.toOperatorIdealFamily
  have hnorms := polarPartial_and_adjoint_enorm_le_one_rectangular T
  apply le_antisymm
  · calc
      S.gauge T.modulus = S.gauge (T.polarPartial.adjoint ∘L T) := by
        rw [T.adjoint_polarPartial_comp_self]
      _ ≤ S.gauge T :=
        S.gauge_comp_left_le_of_norm_le_one hnorms.2 T
  · calc
      S.gauge T = S.gauge (T.polarPartial ∘L T.modulus) := by
        rw [T.polarPartial_comp_modulus]
      _ ≤ S.gauge T.modulus :=
        S.gauge_comp_left_le_of_norm_le_one hnorms.1 T.modulus

/-- An operator belongs to a symmetric ideal exactly when its modulus does. -/
theorem modulus_mem_iff
    (N : SymmetricOperatorIdealFamily.{u, v} K) (T : E →L[K] F) :
    T.modulus ∈ N.toOperatorIdealFamily.carrier ↔
      T ∈ N.toOperatorIdealFamily.carrier := by
  change N.toOperatorIdealFamily.gauge T.modulus ≠ ∞ ↔
    N.toOperatorIdealFamily.gauge T ≠ ∞
  rw [N.gauge_modulus_eq T]

end

end SymmetricOperatorIdealFamily
end TauCeti
