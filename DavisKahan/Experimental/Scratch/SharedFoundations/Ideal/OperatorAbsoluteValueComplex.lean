/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking

Portions of the proof route use the bounded polar decomposition from Spectra,
originally authored by Adam Bornemann.  The declaration-level mapping is
recorded in the accompanying provenance ledger.
-/
import DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import Spectra.QuantumMechanics.Channels.TraceClass.PartialIsometry

/-!
# Absolute-value transport for square symmetric ideals

The equality of ideal gauges between `T` and its positive modulus follows from
two contraction factorizations.  No unitary extension of the polar partial
isometry is needed.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open ExactSinTheta
open Spectra.QuantumMechanics.Channels

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Spectra's CFC absolute value agrees with the local square-root definition. -/
theorem spectra_absOp_eq_operatorAbs (T : E →L[ℂ] E) :
    absOp T = ContinuousLinearMap.modulus T := by
  apply ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq (T := T)
  · exact absOp_nonneg T
  · exact absOp_mul_absOp T

/-- The local absolute value has the Spectra polar factorization. -/
theorem polarIsometry_comp_operatorAbs (T : E →L[ℂ] E) :
    polarIsometry T ∘L ContinuousLinearMap.modulus T = T := by
  rw [← spectra_absOp_eq_operatorAbs]
  exact Spectra.QuantumMechanics.Channels.polar_decomposition T

/-- The adjoint polar factor recovers the local absolute value. -/
theorem polarIsometry_adjoint_comp_operator (T : E →L[ℂ] E) :
    (polarIsometry T).adjoint ∘L T = ContinuousLinearMap.modulus T := by
  rw [← spectra_absOp_eq_operatorAbs]
  exact Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp T

/-- The polar factor and its adjoint are contractions. -/
theorem polarIsometry_and_adjoint_norm_le_one (T : E →L[ℂ] E) :
    ‖polarIsometry T‖ ≤ 1 ∧ ‖(polarIsometry T).adjoint‖ ≤ 1 := by
  refine ⟨norm_polarIsometry_le_one T, ?_⟩
  calc
    ‖(polarIsometry T).adjoint‖ = ‖polarIsometry T‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := norm_polarIsometry_le_one T

/-- Every square symmetric ideal contains `|T|` exactly when it contains `T`,
and assigns them equal gauge. -/
theorem SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E))
    (T : E →L[ℂ] E) :
    (I.mem (ContinuousLinearMap.modulus T) ↔ I.mem T) ∧
      (I.mem T → I.gauge (ContinuousLinearMap.modulus T) = I.gauge T) := by
  let U : E →L[ℂ] E := polarIsometry T
  let J : E →L[ℂ] E := ContinuousLinearMap.id ℂ E
  have hTfactor : T = U ∘L ContinuousLinearMap.modulus T ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact (polarIsometry_comp_operatorAbs T).symm
  have hAbsfactor : ContinuousLinearMap.modulus T = U.adjoint ∘L T ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact (polarIsometry_adjoint_comp_operator T).symm
  have hU := (polarIsometry_and_adjoint_norm_le_one T).1
  have hUa := (polarIsometry_and_adjoint_norm_le_one T).2
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  constructor
  · constructor
    · intro hAbs
      exact SymmetricNormIdeal.mem_of_eq_comp_comp I hAbs hTfactor
    · intro hT
      exact SymmetricNormIdeal.mem_of_eq_comp_comp I hT hAbsfactor
  · intro hT
    have hAbs : I.mem (ContinuousLinearMap.modulus T) :=
      SymmetricNormIdeal.mem_of_eq_comp_comp I hT hAbsfactor
    apply le_antisymm
    · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hT hAbsfactor hUa hJ
    · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hAbs hTfactor hU hJ

/-- Direct form used by the `sin Θ` ideal layer. -/
theorem SymmetricNormIdeal.modulus_mem_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E))
    {T : E →L[ℂ] E} (hT : I.mem T) :
    I.mem (ContinuousLinearMap.modulus T) ∧
      I.gauge (ContinuousLinearMap.modulus T) = I.gauge T := by
  have h := SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq I T
  exact ⟨h.1.mpr hT, h.2 hT⟩

/-- Rectangular-family square specialization. -/
theorem RectangularSymmetricIdealFamily.modulus_mem_and_gauge_eq
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    {T : E →L[ℂ] E} (hT : N.Mem T) :
    N.Mem (ContinuousLinearMap.modulus T) ∧
      N.gauge (ContinuousLinearMap.modulus T) = N.gauge T := by
  let I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E) :=
    DavisKahanExt.SymmetricNormIdeal.ofRectangular N
  have h := SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq I T
  exact ⟨h.1.mpr hT, h.2 hT⟩

/-- The approximation-number proof and the polar-factor proof agree on the
current family abstraction. -/
theorem operatorAbs_family_transport_two_routes
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {T : E →L[ℂ] E}
    (hT : N.Mem T) :
    N.Mem (ContinuousLinearMap.modulus T) ∧
      N.gauge (ContinuousLinearMap.modulus T) =
        N.gauge T := by
  exact RectangularSymmetricIdealFamily.modulus_mem_and_gauge_eq
    N.toRectangularSymmetricIdealFamily hT

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end TauCeti