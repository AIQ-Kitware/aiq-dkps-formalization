/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.SharedFoundations.Ideal.TwoWayFactorization
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import DavisKahan.InfiniteDimensional.DoubleAngle

/-!
# Ideal transport through subspace reflections

The full absolute projector difference and a one-sided angle block have
different singular-value multiplicities in general.  The stable ideal object
for the directed theorem is the one-sided block.  Reflection converts the
block for the mirror subspace exactly into the one-sided double-angle block
(`directedSinBlock_reflected_eq_reflection_comp_sinTwo`), and a reflection is a
self-inverse contraction, so it changes neither ideal membership nor the gauge.

The companion file `TwoWayFactorization` proves the general two-way contraction
principle these use; this one supplies the reflection instance of it and the
double-angle consequence.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Ideal

open scoped InnerProductSpace
open ExactSinTheta
open DavisKahanExt
open TauCeti.DavisKahan

universe u

-- `𝕜` must live in the same universe `u` as `E`; see the note in
-- `TwoWayFactorization` on why a family closed under adjoints cannot keep the
-- two space universes independent.
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Directed sine block from `U` toward `W`. -/
noncomputable def directedSinBlock
    (U W : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] : E →L[𝕜] E :=
  Wᗮ.starProjection ∘L U.starProjection

omit [CompleteSpace E] in
/-- Left reflection is an involutive contraction factorization. -/
theorem reflection_left_twoWay
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    (V.reflection : E →L[𝕜] E) ∘L ((V.reflection : E →L[𝕜] E) ∘L T) = T := by
  simp only [← ContinuousLinearMap.mul_def, ← mul_assoc, V.reflection_mul_self, one_mul]

omit [CompleteSpace E] in
/-- Right reflection is an involutive contraction factorization. -/
theorem reflection_right_twoWay
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    (T ∘L (V.reflection : E →L[𝕜] E)) ∘L (V.reflection : E →L[𝕜] E) = T := by
  simp only [← ContinuousLinearMap.mul_def, mul_assoc, V.reflection_mul_self, mul_one]

/-- Ideal membership is invariant under left reflection. -/
theorem SymmetricOperatorIdealFamily.mem_reflection_comp_iff
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    N.Mem ((V.reflection : E →L[𝕜] E) ∘L T) ↔ N.Mem T := by
  constructor
  · intro h
    rw [← reflection_left_twoWay V T]
    exact N.comp_left_mem ((V.reflection : E →L[𝕜] E)) h
  · intro h
    exact N.comp_left_mem ((V.reflection : E →L[𝕜] E)) h

/-- The ideal gauge is invariant under left reflection. -/
theorem SymmetricOperatorIdealFamily.gauge_reflection_comp
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {T : E →L[𝕜] E} (hT : N.Mem T) :
    N.gaugeReal ((V.reflection : E →L[𝕜] E) ∘L T) = N.gaugeReal T := by
  have hRT : N.Mem ((V.reflection : E →L[𝕜] E) ∘L T) :=
    N.comp_left_mem ((V.reflection : E →L[𝕜] E)) hT
  apply le_antisymm
  · exact N.gaugeReal_comp_left_le ((V.reflection : E →L[𝕜] E)) hT
      (V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le)
  · calc
      N.gaugeReal T =
          N.gaugeReal ((V.reflection : E →L[𝕜] E) ∘L ((V.reflection : E →L[𝕜] E) ∘L T)) :=
        congrArg (fun S : E →L[𝕜] E => N.gaugeReal S)
          (reflection_left_twoWay V T).symm
      _ ≤ N.gaugeReal ((V.reflection : E →L[𝕜] E) ∘L T) :=
        N.gaugeReal_comp_left_le ((V.reflection : E →L[𝕜] E)) hRT
          (V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le)

/-- Ideal membership is invariant under right reflection. -/
theorem SymmetricOperatorIdealFamily.mem_comp_reflection_iff
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    N.Mem (T ∘L (V.reflection : E →L[𝕜] E)) ↔ N.Mem T := by
  constructor
  · intro h
    rw [← reflection_right_twoWay V T]
    exact N.comp_right_mem ((V.reflection : E →L[𝕜] E)) h
  · intro h
    exact N.comp_right_mem ((V.reflection : E →L[𝕜] E)) h

/-- The ideal gauge is invariant under right reflection. -/
theorem SymmetricOperatorIdealFamily.gauge_comp_reflection
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {T : E →L[𝕜] E} (hT : N.Mem T) :
    N.gaugeReal (T ∘L (V.reflection : E →L[𝕜] E)) = N.gaugeReal T := by
  have hTR : N.Mem (T ∘L (V.reflection : E →L[𝕜] E)) :=
    N.comp_right_mem ((V.reflection : E →L[𝕜] E)) hT
  apply le_antisymm
  · exact N.gaugeReal_comp_right_le ((V.reflection : E →L[𝕜] E)) hT
      (V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le)
  · calc
      N.gaugeReal T =
          N.gaugeReal ((T ∘L (V.reflection : E →L[𝕜] E)) ∘L (V.reflection : E →L[𝕜] E)) :=
        congrArg (fun S : E →L[𝕜] E => N.gaugeReal S)
          (reflection_right_twoWay V T).symm
      _ ≤ N.gaugeReal (T ∘L (V.reflection : E →L[𝕜] E)) :=
        N.gaugeReal_comp_right_le ((V.reflection : E →L[𝕜] E)) hTR
          (V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le)

/-- Exact operator identity behind the directed ideal double-angle theorem. -/
theorem directedSinBlock_reflected_eq_reflection_comp_sinTwo
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSinBlock U (reflectedSubspace V U) =
      (V.reflection : E →L[𝕜] E) ∘L sinTwoAngleOperator U V := by
  unfold directedSinBlock
  rw [starProjection_orthogonal_reflectedSubspace]
  have hassoc :
      ((V.reflection : E →L[𝕜] E) ∘L Uᗮ.starProjection ∘L (V.reflection : E →L[𝕜] E)) ∘L
          U.starProjection =
        (V.reflection : E →L[𝕜] E) ∘L
          (Uᗮ.starProjection ∘L (V.reflection : E →L[𝕜] E) ∘L U.starProjection) := by
    ext x
    rfl
  rw [hassoc, complementary_comp_reflection_comp_projection]

/-- The directed mirror-angle block and the double-angle block have equivalent
membership and equal ideal gauge. -/
theorem SymmetricOperatorIdealFamily.directed_reflected_mem_iff_and_gauge_eq
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (N.Mem (directedSinBlock U (reflectedSubspace V U)) ↔
      N.Mem (sinTwoAngleOperator U V)) ∧
    (N.Mem (sinTwoAngleOperator U V) →
      N.gaugeReal (directedSinBlock U (reflectedSubspace V U)) =
        N.gaugeReal (sinTwoAngleOperator U V)) := by
  rw [directedSinBlock_reflected_eq_reflection_comp_sinTwo]
  constructor
  · exact SymmetricOperatorIdealFamily.mem_reflection_comp_iff N V
      (sinTwoAngleOperator U V)
  · intro h
    exact SymmetricOperatorIdealFamily.gauge_reflection_comp N V h

/-- Square-ideal version of the directed mirror-angle transport. -/
theorem DavisKahanExt.SymmetricNormIdeal.directed_reflected_mem_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hT : I.mem (sinTwoAngleOperator U V)) :
    I.mem (directedSinBlock U (reflectedSubspace V U)) ∧
      I.gauge (directedSinBlock U (reflectedSubspace V U)) =
        I.gauge (sinTwoAngleOperator U V) := by
  let J : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E
  let R : E →L[𝕜] E := (V.reflection : E →L[𝕜] E)
  have hforward : directedSinBlock U (reflectedSubspace V U) =
      R ∘L sinTwoAngleOperator U V ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact directedSinBlock_reflected_eq_reflection_comp_sinTwo U V
  have hback : sinTwoAngleOperator U V =
      R ∘L directedSinBlock U (reflectedSubspace V U) ∘L J := by
    rw [ContinuousLinearMap.comp_id,
      directedSinBlock_reflected_eq_reflection_comp_sinTwo]
    exact (reflection_left_twoWay V _).symm
  have hR : ‖R‖ ≤ 1 := V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact SymmetricNormIdeal.mem_iff_and_gauge_eq_of_twoWayContractions I
    hback hforward hR hJ hR hJ hT

end Ideal
end SharedFoundations
end DavisKahan
end TauCeti