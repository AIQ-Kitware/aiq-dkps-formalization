/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# The absolute value of a Hilbert-space operator

For a bounded operator `T` on a complex Hilbert space, the absolute value
`|T| = (T⋆ T)^(1/2)` through the continuous-functional-calculus square root
on the C⋆-algebra of bounded operators, together with its defining laws:

* `operatorAbs_nonneg` — `0 ≤ |T|`;
* `operatorAbs_mul_self` — `|T| * |T| = T⋆ T`;
* `operatorAbs_unique` — the positive square root is unique;
* `norm_operatorAbs` — `‖|T|‖ = ‖T‖`;
* `norm_operatorAbs_apply` — the pointwise isometry `‖|T| x‖ = ‖T x‖`.

Complex scalars are required because Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`; the real case
is expected to follow by complexification transfer.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The absolute value `|T| = (T⋆ T)^(1/2)` of a bounded operator on a
complex Hilbert space, through the continuous-functional-calculus square
root. -/
noncomputable def operatorAbs (T : E →L[ℂ] E) : E →L[ℂ] E :=
  CFC.sqrt (star T * T)

/-- The absolute value is nonnegative in the C⋆-order. -/
theorem operatorAbs_nonneg (T : E →L[ℂ] E) : 0 ≤ operatorAbs T :=
  CFC.sqrt_nonneg _

/-- The absolute value is self-adjoint. -/
theorem isSelfAdjoint_operatorAbs (T : E →L[ℂ] E) :
    IsSelfAdjoint (operatorAbs T) :=
  IsSelfAdjoint.of_nonneg (operatorAbs_nonneg T)

/-- The defining identity `|T| * |T| = T⋆ T`. -/
theorem operatorAbs_mul_self (T : E →L[ℂ] E) :
    operatorAbs T * operatorAbs T = star T * T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

/-- The absolute value is the unique nonnegative square root of `T⋆ T`. -/
theorem operatorAbs_unique {T b : E →L[ℂ] E} (hb : 0 ≤ b)
    (h : b * b = star T * T) : b = operatorAbs T :=
  (CFC.sqrt_unique h hb).symm

/-- Absolute values of operators with commuting squares commute. -/
theorem operatorAbs_commute_operatorAbs {S T : E →L[ℂ] E}
    (h : Commute (star S * S) (star T * T)) :
    Commute (operatorAbs S) (operatorAbs T) := by
  have h1 : Commute (CFC.sqrt (star S * S)) (star T * T) :=
    h.cfcₙ_nnreal _
  have h2 : Commute (CFC.sqrt (star T * T)) (CFC.sqrt (star S * S)) :=
    h1.symm.cfcₙ_nnreal _
  exact h2.symm

/-- `‖|T|‖ = ‖T‖`. -/
theorem norm_operatorAbs (T : E →L[ℂ] E) :
    ‖operatorAbs T‖ = ‖T‖ := by
  rw [operatorAbs, CFC.norm_sqrt _ (star_mul_self_nonneg T),
    CStarRing.norm_star_mul_self]
  exact Real.sqrt_mul_self (norm_nonneg T)

/-- Left composition sees only the absolute value:
`‖|S| * D‖ = ‖S * D‖`, by the C⋆-identity applied to
`(|S| D)⋆ (|S| D) = D⋆ (S⋆ S) D = (S D)⋆ (S D)`. -/
theorem norm_operatorAbs_mul (S D : E →L[ℂ] E) :
    ‖operatorAbs S * D‖ = ‖S * D‖ := by
  have h : star (operatorAbs S * D) * (operatorAbs S * D) =
      star (S * D) * (S * D) := by
    calc star (operatorAbs S * D) * (operatorAbs S * D)
        = star D * (operatorAbs S * operatorAbs S) * D := by
          rw [star_mul, (isSelfAdjoint_operatorAbs S).star_eq]
          simp only [mul_assoc]
      _ = star D * (star S * S) * D := by rw [operatorAbs_mul_self]
      _ = star (S * D) * (S * D) := by
          rw [star_mul]
          simp only [mul_assoc]
  have hsq : ‖operatorAbs S * D‖ ^ 2 = ‖S * D‖ ^ 2 := by
    rw [sq, sq, ← CStarRing.norm_star_mul_self,
      ← CStarRing.norm_star_mul_self, h]
  have hs := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs

/-- Right composition sees the absolute value as the adjoint:
`‖D * |T|‖ = ‖D * T⋆‖`, by conjugating the left-composition identity. -/
theorem norm_mul_operatorAbs (D T : E →L[ℂ] E) :
    ‖D * operatorAbs T‖ = ‖D * star T‖ := by
  calc ‖D * operatorAbs T‖
      = ‖star (D * operatorAbs T)‖ := (norm_star _).symm
    _ = ‖operatorAbs T * star D‖ := by
        rw [star_mul, (isSelfAdjoint_operatorAbs T).star_eq]
    _ = ‖T * star D‖ := norm_operatorAbs_mul T (star D)
    _ = ‖star (T * star D)‖ := (norm_star _).symm
    _ = ‖D * star T‖ := by rw [star_mul, star_star]

/-- The pointwise isometry `‖|T| x‖ = ‖T x‖`. -/
theorem norm_operatorAbs_apply (T : E →L[ℂ] E) (x : E) :
    ‖operatorAbs T x‖ = ‖T x‖ := by
  have habs : (operatorAbs T).adjoint = operatorAbs T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_operatorAbs T).star_eq
  have h1 : (⟪operatorAbs T x, operatorAbs T x⟫_ℂ : ℂ) =
      ⟪x, (operatorAbs T * operatorAbs T) x⟫_ℂ := by
    calc (⟪operatorAbs T x, operatorAbs T x⟫_ℂ : ℂ)
        = ⟪(operatorAbs T).adjoint x, operatorAbs T x⟫_ℂ := by rw [habs]
      _ = ⟪x, operatorAbs T (operatorAbs T x)⟫_ℂ :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪x, (operatorAbs T * operatorAbs T) x⟫_ℂ := rfl
  have h2 : (⟪T x, T x⟫_ℂ : ℂ) = ⟪x, (star T * T) x⟫_ℂ := by
    calc (⟪T x, T x⟫_ℂ : ℂ)
        = ⟪x, T.adjoint (T x)⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪x, (star T * T) x⟫_ℂ := rfl
  have h3 : (⟪operatorAbs T x, operatorAbs T x⟫_ℂ : ℂ) =
      ⟪T x, T x⟫_ℂ := by
    rw [h1, h2, operatorAbs_mul_self]
  have h4 : (‖operatorAbs T x‖ : ℝ) ^ 2 = ‖T x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    exact_mod_cast h3
  have h5 := congrArg Real.sqrt h4
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h5

end ForMathlib
