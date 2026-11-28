/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import DavisKahan.BoundedOperator.Problem

/-! # Reflection defects for bounded operators -/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
@[expose]
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  (U.reflection : E →L[𝕜] E) ∘L A ∘L (U.reflection : E →L[𝕜] E) - A

omit [CompleteSpace E] in
/-- The reflection defect anti-commutes with the reflection that defines it:
`J (J A J - A) = -(J A J - A) J`. -/
theorem reflectionOperator_comp_reflectionDefect
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (U.reflection : E →L[𝕜] E) ∘L reflectionDefect U A =
      -(reflectionDefect U A ∘L (U.reflection : E →L[𝕜] E)) := by
  ext x
  have hinvol (y : E) :
      (U.reflection : E →L[𝕜] E) ((U.reflection : E →L[𝕜] E) y) = y :=
    U.reflection_reflection y
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    neg_apply, map_sub]
  rw [hinvol (A ((U.reflection : E →L[𝕜] E) x)), hinvol x]
  rw [neg_sub]

omit [CompleteSpace E] in
/-- The mirror defect vanishes when the subspace reduces the operator.
-/
theorem reflectionDefect_eq_zero_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Submodule.IsReducing U A) :
    reflectionDefect U A = 0 := by
  ext x
  have hcomm := congrArg (fun T : E →L[𝕜] E => T ((U.reflection : E →L[𝕜] E) x))
    (U.commute_reflection_iff.mpr (Submodule.isReducing_coe_iff_commute_starProjection.mp hU)).eq
  have hinvol : (U.reflection : E →L[𝕜] E) ((U.reflection : E →L[𝕜] E) x) = x :=
    U.reflection_reflection x
  simp only [mul_apply_eq_comp] at hcomm
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    zero_apply]
  rw [hcomm, hinvol, sub_self]

omit [CompleteSpace E] in
/-- Conjugating and subtracting a reducing comparison operator leaves only
its perturbation.
-/
theorem reflectionDefect_eq_perturbationDefect
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Submodule.IsReducing V B) :
    reflectionDefect V A =
      (V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E) - (A - B) := by
  have hB : reflectionDefect V B = 0 :=
    reflectionDefect_eq_zero_of_reduces B V hV
  unfold reflectionDefect at hB ⊢
  calc
    (V.reflection : E →L[𝕜] E) ∘L A ∘L (V.reflection : E →L[𝕜] E) - A =
        ((V.reflection : E →L[𝕜] E) ∘L A ∘L (V.reflection : E →L[𝕜] E) - A) -
          ((V.reflection : E →L[𝕜] E) ∘L B ∘L (V.reflection : E →L[𝕜] E) - B) := by
      rw [hB, sub_zero]
    _ = (V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E) - (A - B) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      abel

omit [CompleteSpace E] in
/-- The reflection defect is bounded by twice the perturbation norm.
-/
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Submodule.IsReducing V B) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
  rw [reflectionDefect_eq_perturbationDefect A B V hV]
  have hconj :
      ‖(V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E)‖ ≤
        ‖A - B‖ := by
    calc
      ‖(V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E)‖ ≤
          ‖(V.reflection : E →L[𝕜] E)‖ * ‖(A - B) ∘L (V.reflection : E →L[𝕜] E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(V.reflection : E →L[𝕜] E)‖ * (‖A - B‖ * ‖(V.reflection : E →L[𝕜] E)‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg ((V.reflection : E →L[𝕜] E)))
      _ ≤ 1 * (‖A - B‖ * ‖(V.reflection : E →L[𝕜] E)‖) :=
        mul_le_mul_of_nonneg_right V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le
          (by positivity)
      _ ≤ 1 * (‖A - B‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left V.reflection.toLinearIsometry.norm_toContinuousLinearMap_le
            (norm_nonneg (A - B)))
          zero_le_one
      _ = ‖A - B‖ := by ring
  calc
    ‖(V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E) - (A - B)‖ ≤
        ‖(V.reflection : E →L[𝕜] E) ∘L (A - B) ∘L (V.reflection : E →L[𝕜] E)‖ +
          ‖A - B‖ := norm_sub_le _ _
    _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hconj le_rfl
    _ = 2 * ‖A - B‖ := by ring


end DavisKahan
end TauCeti
