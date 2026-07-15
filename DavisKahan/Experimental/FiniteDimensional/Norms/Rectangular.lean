/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

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

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

namespace RectangularUnitarilyInvariantNorm

/-- Extend a coherent square UI-norm family to rectangular maps by zero
extension on `E ⊕ F`. -/
noncomputable def ofSquareFamily
    (Ns : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [FiniteDimensional 𝕜 H], UnitarilyInvariantNorm 𝕜 H) :
    RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A := Ns (WithLp 2 (E × F)) (zeroExtension A)
  add_le' A B := by
    rw [zeroExtension_add]
    exact (Ns (WithLp 2 (E × F))).add_le _ _
  smul' a A := by
    rw [zeroExtension_smul]
    exact (Ns (WithLp 2 (E × F))).smul a _
  invariant' U V A := by
    let UV : WithLp 2 (E × F) ≃ₗᵢ[𝕜] WithLp 2 (E × F) :=
      LinearIsometryEquiv.prodCongr V U
    have hzero : zeroExtension
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) =
      UV.toLinearMap ∘ₗ zeroExtension A ∘ₗ UV.symm.toLinearMap := by
      ext x <;> simp [UV, zeroExtension]
    rw [hzero]
    exact (Ns (WithLp 2 (E × F))).invariant UV UV.symm _

/-- Schatten `p` seminorm of a rectangular map, for `1 ≤ p`. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A :=
    (∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
      (A.singularValues i) ^ p) ^ (1 / p)
  add_le' A B := by
    let sA := fun i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) =>
      A.singularValues i
    let sB := fun i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) =>
      B.singularValues i
    have hmaj := singularValues_add_weaklyMajorized A B
    exact lpGauge_triangle_of_weakMajorization hp hmaj
  smul' a A := by
    simp [LinearMap.singularValues_smul, Finset.mul_sum, Real.mul_rpow,
      hp.trans_lt one_lt_top]
  invariant' U V A := by
    simp [LinearMap.singularValues_unitary_comp,
      LinearMap.singularValues_comp_unitary]

/-- Schatten membership is automatic in finite dimensions. -/
theorem mem_schatten (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    0 ≤ schatten (𝕜 := 𝕜) (E := E) (F := F) p hp A :=
  (schatten (𝕜 := 𝕜) (E := E) (F := F) p hp).nonneg A

end RectangularUnitarilyInvariantNorm
end DavisKahanTheory
end ForMathlib
