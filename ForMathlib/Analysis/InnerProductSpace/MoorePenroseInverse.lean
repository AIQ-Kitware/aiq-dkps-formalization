/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import ForMathlib.Analysis.InnerProductSpace.SingularSystem

/-!
# Moore--Penrose inverse in finite-dimensional inner-product spaces

The pseudoinverse of a rectangular map is reconstructed from its intrinsic
right singular basis.  On a right singular vector `vᵢ`, the Gram operator
`A†A` acts by `σᵢ²`; the pseudoinverse therefore uses the coefficient
`(σᵢ²)⁻¹` in front of the rank-one map `y ↦ ⟪A vᵢ, y⟫ vᵢ`.

Zero singular values contribute zero through total field inversion.
-/

namespace FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The finite-dimensional Moore--Penrose inverse, reconstructed from the
right singular basis and the Gram eigenvalues. -/
noncomputable def moorePenroseInverse (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    (((((A.singularValues i) ^ 2 : ℝ) : 𝕜))⁻¹) •
      (InnerProductSpace.rankOne 𝕜
        (ForMathlib.rightSingularBasis A i)
        (A (ForMathlib.rightSingularBasis A i))).toLinearMap

/-- A hypothesis-carrying inverse on the range.  The total map is the
Moore--Penrose inverse; injectivity identifies its initial projection with the
identity on the domain. -/
noncomputable def inverseOnRange (A : E →ₗ[𝕜] F) (_hA : Function.Injective A) :
    F →ₗ[𝕜] E :=
  moorePenroseInverse A

/-- Gram orthogonality of the images of the right singular basis. -/
theorem inner_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i j : Fin (finrank 𝕜 E)) :
    inner 𝕜 (A (ForMathlib.rightSingularBasis A i))
        (A (ForMathlib.rightSingularBasis A j)) =
      (((A.singularValues j) ^ 2 : ℝ) : 𝕜) *
        inner 𝕜 (ForMathlib.rightSingularBasis A i)
          (ForMathlib.rightSingularBasis A j) := by
  rw [← LinearMap.adjoint_inner_right,
    show A.adjoint (A (ForMathlib.rightSingularBasis A j)) =
      (A.adjoint.comp A) (ForMathlib.rightSingularBasis A j) from rfl,
    ForMathlib.adjointCompSelf_apply_rightSingularBasis,
    inner_smul_right]

/-- The pseudoinverse followed by the original map fixes each right singular
vector with nonzero singular value. -/
theorem moorePenroseInverse_apply_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) {k : Fin (finrank 𝕜 E)}
    (hk : A.singularValues k ≠ 0) :
    moorePenroseInverse A (A (ForMathlib.rightSingularBasis A k)) =
      ForMathlib.rightSingularBasis A k := by
  classical
  unfold moorePenroseInverse
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (ForMathlib.rightSingularBasis A i)
        (ForMathlib.rightSingularBasis A k) = 0 := by
      simpa [orthonormal_iff_ite.mp
        (ForMathlib.rightSingularBasis A).orthonormal i k, if_neg hik]
    rw [hinner, mul_zero, zero_smul, smul_zero]
  · intro hkmem
    exact absurd (Finset.mem_univ k) hkmem
  · rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (ForMathlib.rightSingularBasis A k)
        (ForMathlib.rightSingularBasis A k) = 1 := by
      simpa using
        orthonormal_iff_ite.mp
          (ForMathlib.rightSingularBasis A).orthonormal k k
    rw [hinner, mul_one, smul_smul]
    have hσ : ((((A.singularValues k) ^ 2 : ℝ) : 𝕜)) ≠ 0 := by
      exact RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 hk)
    rw [inv_mul_cancel₀ hσ, one_smul]

/-- The first Penrose identity `A A⁺ A = A`. -/
theorem comp_moorePenroseInverse_comp (A : E →ₗ[𝕜] F) :
    A ∘ₗ moorePenroseInverse A ∘ₗ A = A := by
  apply (ForMathlib.rightSingularBasis A).toBasis.ext
  intro i
  by_cases hi : A.singularValues i = 0
  · -- on a zero singular direction both sides vanish; the composite has to be
    -- unfolded before the vanishing rewrite reaches the inner occurrence
    rw [OrthonormalBasis.coe_toBasis]
    simp [ForMathlib.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi]
  · rw [OrthonormalBasis.coe_toBasis]
    change A (moorePenroseInverse A (A (ForMathlib.rightSingularBasis A i))) =
      A (ForMathlib.rightSingularBasis A i)
    rw [moorePenroseInverse_apply_apply_rightSingularBasis A hi]

/-- If `A` is injective, the pseudoinverse is a left inverse. -/
theorem moorePenroseInverse_comp_eq_id_of_injective
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    moorePenroseInverse A ∘ₗ A = LinearMap.id := by
  apply (ForMathlib.rightSingularBasis A).toBasis.ext
  intro i
  -- injectivity rules out a zero singular direction: a right singular vector is
  -- a unit vector, so `A v = 0 = A 0` would force `v = 0`
  have hi : A.singularValues i ≠ 0 := by
    intro hi
    have hz := ForMathlib.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi
    have he : ForMathlib.rightSingularBasis A i = 0 := hA (by rw [hz, map_zero])
    have hne : ForMathlib.rightSingularBasis A i ≠ 0 := by
      simpa using (ForMathlib.rightSingularBasis A).toBasis.ne_zero i
    exact hne he
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    moorePenroseInverse_apply_apply_rightSingularBasis A hi,
    LinearMap.id_apply]

/-- The hypothesis-carrying inverse is definitionally the pseudoinverse. -/
@[simp] theorem inverseOnRange_eq_moorePenroseInverse
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    inverseOnRange A hA = moorePenroseInverse A :=
  rfl

/-- An inverse on the range is a left inverse of an injective map. -/
theorem inverseOnRange_comp_eq_id
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    inverseOnRange A hA ∘ₗ A = LinearMap.id := by
  simpa [inverseOnRange] using moorePenroseInverse_comp_eq_id_of_injective A hA

/-- Compatibility name used by tangent-coordinate developments. -/
theorem moorePenroseInverse_eq_inverseOnRange
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    moorePenroseInverse A = inverseOnRange A hA :=
  rfl

end FiniteDimensional
