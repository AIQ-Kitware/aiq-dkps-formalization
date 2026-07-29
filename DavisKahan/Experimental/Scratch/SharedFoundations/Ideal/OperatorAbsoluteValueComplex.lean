/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import ForTauCeti.Analysis.InnerProductSpace.PolarPartialIsometry

/-!
# Absolute-value transport for square symmetric ideals

The equality of ideal gauges between `T` and its positive modulus follows from
two contraction factorizations.  No unitary extension of the polar partial
isometry is needed.

Until 2026-07-29 the polar factorization came from Spectra
(`QuantumMechanics.Channels.polar_decomposition`, originally authored by Adam
Bornemann).  `ForTauCeti`'s polar API supersedes it and is strictly more general
— it is stated for rectangular `E →L[ℂ] F` — so the three facts consumed here
(`polarPartial_comp_modulus`, the adjoint identity, and the contraction bound)
are read off it directly.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open ExactSinTheta

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The polar factorization `T = W |T|`. -/
theorem polarIsometry_comp_operatorAbs (T : E →L[ℂ] E) :
    T.polarPartial ∘L ContinuousLinearMap.modulus T = T :=
  T.polarPartial_comp_modulus

/-- The adjoint polar factor recovers the absolute value: `W⋆ T = |T|`.  On the
initial space `W⋆ W` is the identity, and `|T|` lands there. -/
theorem polarIsometry_adjoint_comp_operator (T : E →L[ℂ] E) :
    T.polarPartial.adjoint ∘L T = ContinuousLinearMap.modulus T := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hT : T x = T.polarPartial (ContinuousLinearMap.modulus T x) := by
    conv_lhs => rw [← T.polarPartial_comp_modulus]
    rfl
  rw [ContinuousLinearMap.comp_apply, hT,
    T.adjoint_polarPartial_polarPartial_apply_of_mem
      (T.modulus_apply_mem_polarInitial x)]

/-- The polar partial isometry is a contraction: it is isometric on its initial
space and kills the orthogonal complement. -/
theorem norm_polarPartial_le_one (T : E →L[ℂ] E) : ‖T.polarPartial‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := T.polarInitial) y
  have hinner : ⟪p, q⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hq p hp
  have hpyth : ‖p + q‖ * ‖p + q‖ = ‖p‖ * ‖p‖ + ‖q‖ * ‖q‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hinner
  rw [map_add, T.polarPartial_eq_zero_of_mem_orthogonal hq, add_zero,
    T.norm_polarPartial_apply_of_mem hp, one_mul]
  nlinarith [norm_nonneg p, norm_nonneg q, norm_nonneg (p + q)]

/-- The polar factor and its adjoint are contractions. -/
theorem polarIsometry_and_adjoint_norm_le_one (T : E →L[ℂ] E) :
    ‖T.polarPartial‖ ≤ 1 ∧ ‖T.polarPartial.adjoint‖ ≤ 1 := by
  refine ⟨norm_polarPartial_le_one T, ?_⟩
  calc
    ‖T.polarPartial.adjoint‖ = ‖T.polarPartial‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := norm_polarPartial_le_one T

/-- Every square symmetric ideal contains `|T|` exactly when it contains `T`,
and assigns them equal gauge. -/
theorem SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E))
    (T : E →L[ℂ] E) :
    (I.mem (ContinuousLinearMap.modulus T) ↔ I.mem T) ∧
      (I.mem T → I.gauge (ContinuousLinearMap.modulus T) = I.gauge T) := by
  let U : E →L[ℂ] E := T.polarPartial
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
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
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