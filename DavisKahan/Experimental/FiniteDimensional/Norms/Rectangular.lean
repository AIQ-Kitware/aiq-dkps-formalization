/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Rectangular unitarily invariant norms

A square UI norm family determines a rectangular norm by the standard zero
extension into the orthogonal sum of domain and codomain.  Schatten norms are
obtained by applying the `ℓᵖ` gauge to the singular-value vector.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

universe uE uF

variable {𝕜 : Type*} [RCLike 𝕜]

namespace RectangularUnitarilyInvariantNorm

/-- Extend a coherent square UI-norm family to rectangular maps by zero
extension on `E ⊕ F`. -/
noncomputable def ofSquareFamily
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (Ns : ∀ (H : Type (max uE uF)) [NormedAddCommGroup H]
      [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H],
      UnitarilyInvariantNorm 𝕜 H) :
    RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A := Ns (WithLp 2 (E × F)) (zeroExtension A)
  add_le' A B := by
    rw [zeroExtension_add]
    exact (Ns (WithLp 2 (E × F))).add_le _ _
  smul' a A := by
    rw [zeroExtension_smul]
    exact (Ns (WithLp 2 (E × F))).smul' a _
  invariant' U V A := by
    let UV : WithLp 2 (E × F) ≃ₗᵢ[𝕜] WithLp 2 (E × F) :=
      LinearIsometryEquiv.withLpProdCongr 2 V.symm U
    have hzero : zeroExtension
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) =
      UV.toLinearMap ∘ₗ zeroExtension A ∘ₗ UV.symm.toLinearMap := by
      ext z
      simp [UV]
    rw [hzero]
    exact (Ns (WithLp 2 (E × F))).invariant UV UV.symm _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Schatten `p` seminorm of a rectangular map, for `1 ≤ p`.

The triangle inequality is the Tomić--Weyl route: the singular values of a
sum are weakly majorized by the sum of singular values (Ky Fan), and the
`ℓᵖ` gauge is monotone under weak majorization of nonnegative decreasing
vectors, then finite-dimensional Minkowski applies.  The majorization
monotonicity lemma is not yet available in this development, so that field
is an open obligation. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A :=
    (∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
      (A.singularValues i) ^ p) ^ (1 / p)
  add_le' A B := sorry
  smul' a A := by
    have hp0 : p ≠ 0 := by linarith
    have hterm : ∀ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
        ((a • A).singularValues (i : ℕ)) ^ p =
          ‖a‖ ^ p * (A.singularValues (i : ℕ)) ^ p := by
      intro i
      rw [singularValues_smul_rect,
        Real.mul_rpow (norm_nonneg a) (A.singularValues_nonneg _)]
    have hsum : (0 : ℝ) ≤ ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
        (A.singularValues (i : ℕ)) ^ p :=
      Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (A.singularValues_nonneg _) p
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
      Real.mul_rpow (Real.rpow_nonneg (norm_nonneg a) p) hsum,
      ← Real.rpow_mul (norm_nonneg a), mul_one_div_cancel hp0,
      Real.rpow_one]
  invariant' U V A := by
    rw [singularValues_unitary_comp, singularValues_comp_unitary]

/-- Schatten values are nonnegative in finite dimensions. -/
theorem mem_schatten (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    0 ≤ schatten (𝕜 := 𝕜) (E := E) (F := F) p hp A :=
  (schatten (𝕜 := 𝕜) (E := E) (F := F) p hp).nonneg A

end RectangularUnitarilyInvariantNorm
end DavisKahanTheory
end ForMathlib
