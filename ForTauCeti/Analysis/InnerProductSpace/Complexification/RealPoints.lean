/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Isometric coordinates from the real points of a conjugation

The accepted `realPoints` and real/imaginary decomposition identify a complex
space with the complexification of its fixed real space. For an isometric
conjugation this identification preserves the given Hilbert norm. This file
supplies that normed comparison for the concrete Hilbert complexification.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- An isometric conjugate-linear map, viewed over the real scalars. -/
def conjugationRealIsometry (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K) :
    E →ₗᵢ[ℝ] E :=
  LinearMap.toLinearIsometry
    { toFun := K
      map_add' := map_add K
      map_smul' := fun r x => by
        rw [← Complex.coe_smul r, map_smulₛₗ, Complex.conj_ofReal]
        rfl } hK

/-- The real points are real orthogonal to their imaginary multiples. -/
theorem realPoints_inner_I_smul_eq_zero
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K) (x y : realPoints K) :
    ⟪(x : E), Complex.I • (y : E)⟫_ℝ = 0 := by
  have h := (conjugationRealIsometry K hK).inner_map_map
    (x : E) (Complex.I • (y : E))
  change ⟪K x, K (Complex.I • (y : E))⟫_ℝ = _ at h
  rw [map_smulₛₗ, Complex.conj_I, mem_realPoints.mp x.property,
    mem_realPoints.mp y.property, neg_smul,
    inner_neg_right] at h
  linarith

/-- Add the real and imaginary components in the ambient complex space.
The norm is preserved when the conjugation is isometric. -/
@[expose]
def realPointsComplexificationEmbedding
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K) :
    RealComplexification (realPoints K) →ₗᵢ[ℂ] E where
  toFun z := ((RealComplexification.re z : realPoints K) : E) +
    Complex.I • ((RealComplexification.im z : realPoints K) : E)
  map_add' z w := by simp [smul_add]; abel
  map_smul' c z := by
    simp only [RealComplexification.re_complex_smul, RealComplexification.im_complex_smul,
      Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul_of_tower,
      RingHom.id_apply]
    simp only [← Complex.coe_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    match_scalars <;> ring_nf
    simp
  norm_map' z := by
    change ‖((RealComplexification.re z : realPoints K) : E) +
      Complex.I • ((RealComplexification.im z : realPoints K) : E)‖ = ‖z‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      norm_add_sq (𝕜 := ℝ), realPoints_inner_I_smul_eq_zero K hK,
      RealComplexification.norm_sq]
    simp [norm_smul]

/-- The isometric comparison evaluates by adding the two fixed vectors. -/
@[simp]
theorem realPointsComplexificationEmbedding_apply
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K)
    (z : RealComplexification (realPoints K)) :
    realPointsComplexificationEmbedding K hK z =
      ((RealComplexification.re z : realPoints K) : E) +
        Complex.I • ((RealComplexification.im z : realPoints K) : E) := rfl

/-- The accepted decomposition into fixed real and imaginary parts proves
surjectivity of the Hilbert complexification comparison. -/
theorem realPointsComplexificationEmbedding_surjective
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K)
    (hinv : Function.Involutive K) :
    Function.Surjective (realPointsComplexificationEmbedding K hK) := by
  intro x
  refine ⟨RealComplexification.mk
    ⟨conjRealPart K x, conjRealPart_mem hinv x⟩
    ⟨conjImaginaryPart K x, conjImaginaryPart_mem hinv x⟩, ?_⟩
  exact conjRealPart_add_I_smul_conjImaginaryPart (K := K) x

/-- A complex Hilbert space with isometric conjugation is isometrically
the concrete complexification of the accepted fixed real subspace. -/
@[expose]
def realPointsComplexificationEquiv
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K)
    (hinv : Function.Involutive K) :
    RealComplexification (realPoints K) ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective (realPointsComplexificationEmbedding K hK)
    (realPointsComplexificationEmbedding_surjective K hK hinv)

/-- The isometric equivalence has the same fixed-component formula. -/
@[simp]
theorem realPointsComplexificationEquiv_apply
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K)
    (hinv : Function.Involutive K) (z : RealComplexification (realPoints K)) :
    realPointsComplexificationEquiv K hK hinv z =
      ((RealComplexification.re z : realPoints K) : E) +
        Complex.I • ((RealComplexification.im z : realPoints K) : E) := rfl

/-- In fixed real coordinates the original conjugation is the concrete
coordinate conjugation. -/
theorem realPointsComplexificationEquiv_conjugation
    (K : E →ₛₗ[starRingEnd ℂ] E) (hK : Isometry K)
    (hinv : Function.Involutive K) (z : RealComplexification (realPoints K)) :
    K (realPointsComplexificationEquiv K hK hinv z) =
      realPointsComplexificationEquiv K hK hinv (RealComplexification.conjugation z) := by
  simp only [realPointsComplexificationEquiv_apply, map_add, map_smulₛₗ,
    Complex.conj_I, mem_realPoints.mp (RealComplexification.re z).property,
    mem_realPoints.mp (RealComplexification.im z).property]
  simp

end TauCeti
