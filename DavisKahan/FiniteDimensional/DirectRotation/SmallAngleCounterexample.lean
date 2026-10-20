/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 Astra Pro
-/
import DavisKahan.FiniteDimensional.DirectRotation.ShortRotationCounterexample

/-!
# Failure of full-displacement minimality at arbitrarily small angles

For every `0 < theta < pi / 2`, we construct an orthogonal map on `Real^4`
carrying `U = span{e0,e1}` to a subspace with both principal angles `theta`.
Its displacement has singular values `(2 sin theta, 2 sin theta, 0, 0)`.
The canonical direct rotation has four displacement singular values equal to
`sqrt (2 - 2 cos theta) = 2 sin (theta / 2)`. Consequently its trace norm is
strictly larger. In particular, no positive principal-angle threshold repairs
Davis--Kahan Proposition 4.4 for all unitarily invariant norms.

The construction is the parameterized version of `ShortRotationCounterexample`.
It fixes the anti-diagonal two-plane and rotates the diagonal two-plane by
`2 * theta`. The proof below identifies the actual canonical direct rotation
through the modulus of the canonical intertwiner; the norm comparison is not
merely a comparison between two arbitrarily chosen orthogonal maps.

## References

* C. Davis and W. M. Kahan, *The Rotation of Eigenvectors by a Perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), Proposition 4.4.
* V. Bolotnikov, C.-K. Li, and L. Rodman, *Minimal distortion problems for classes
  of unitary matrices*, Electron. J. Linear Algebra 8 (2001), 26--46.
  Q-norm minimality and related failures outside that norm class precede this
  explicit short-angle refutation; no priority claim for that phenomenon is made.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SmallAngleCounterexample

open scoped InnerProductSpace
open Module (finrank)
open ShortRotationCounterexample
  (E4 sv U4 mem_U4 coord_eq_zero_of_mem_U4 projection_U4_coord mbasis mbasis_coe mv)

noncomputable section

private theorem circle (theta : Real) :
    Real.cos theta ^ 2 + Real.sin theta ^ 2 = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The competitor rotates the diagonal two-plane by `2 * theta` and fixes its
orthogonal complement. At `theta = pi / 4` this is the existing sign-matrix witness. -/
def Wmat (theta : Real) : Matrix (Fin 4) (Fin 4) Real :=
  !![Real.cos theta ^ 2, -(Real.sin theta * Real.cos theta), -(Real.sin theta ^ 2),
       -(Real.sin theta * Real.cos theta);
     Real.sin theta * Real.cos theta, Real.cos theta ^ 2,
       Real.sin theta * Real.cos theta, -(Real.sin theta ^ 2);
     -(Real.sin theta ^ 2), -(Real.sin theta * Real.cos theta), Real.cos theta ^ 2,
       -(Real.sin theta * Real.cos theta);
     Real.sin theta * Real.cos theta, -(Real.sin theta ^ 2),
       Real.sin theta * Real.cos theta, Real.cos theta ^ 2]

/-- The competitor as a linear map. -/
def Wlin (theta : Real) : E4 →ₗ[ℝ] E4 := Matrix.toEuclideanLin (Wmat theta)

/-- The transpose of the competitor. -/
def Wlin' (theta : Real) : E4 →ₗ[ℝ] E4 :=
  Matrix.toEuclideanLin (Wmat theta).transpose

private theorem Wlin_apply (theta : Real) (x : E4) (i : Fin 4) :
    Wlin theta x i = ∑ j, Wmat theta i j * x j := by
  simp [Wlin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

private theorem Wlin'_apply (theta : Real) (x : E4) (i : Fin 4) :
    Wlin' theta x i = ∑ j, Wmat theta j i * x j := by
  simp [Wlin', Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

private theorem Wlin'_comp_Wlin (theta : Real) :
    Wlin' theta ∘ₗ Wlin theta = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [Wlin'_apply]
  simp only [Wlin_apply]
  have hcircle := circle theta
  fin_cases i
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 0 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 1 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 3 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle

private theorem Wlin_comp_Wlin' (theta : Real) :
    Wlin theta ∘ₗ Wlin' theta = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [Wlin_apply]
  simp only [Wlin'_apply]
  have hcircle := circle theta
  fin_cases i
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 0 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 1 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (x 3 * (Real.cos theta ^ 2 + Real.sin theta ^ 2 + 1)) * hcircle

private theorem inner_Wlin_left (theta : Real) (x y : E4) :
    ⟪Wlin theta x, y⟫_ℝ = ⟪x, Wlin' theta y⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Wlin_apply, Wlin'_apply, Fin.sum_univ_four]
  simp [Wmat]; ring

private theorem inner_Wlin_Wlin (theta : Real) (x y : E4) :
    ⟪Wlin theta x, Wlin theta y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [inner_Wlin_left]
  have h := LinearMap.congr_fun (Wlin'_comp_Wlin theta) y
  change Wlin' theta (Wlin theta y) = y at h
  rw [h]

/-- The orthogonal competitor. -/
def Wequiv (theta : Real) : E4 ≃ₗᵢ[ℝ] E4 :=
  (LinearEquiv.ofLinearMap (Wlin theta) (Wlin' theta)
    (Wlin_comp_Wlin' theta) (Wlin'_comp_Wlin theta)).isometryOfInner
      (inner_Wlin_Wlin theta)

private theorem Wequiv_apply (theta : Real) (x : E4) :
    Wequiv theta x = Wlin theta x := rfl

private theorem Wequiv_symm_apply (theta : Real) (x : E4) :
    (Wequiv theta).symm x = Wlin' theta x := rfl

private theorem Wequiv_toLinearMap (theta : Real) :
    (Wequiv theta).toLinearMap = Wlin theta := rfl

private theorem Wlin_adjoint (theta : Real) :
    LinearMap.adjoint (Wlin theta) = Wlin' theta :=
  (Wequiv theta).adjoint_toLinearMap_eq_symm

/-- The target subspace. -/
def V4 (theta : Real) : Submodule Real E4 := U4.map (Wequiv theta).toLinearMap

private theorem projection_V4_apply (theta : Real) (x : E4) :
    projection (V4 theta) x =
      Wequiv theta (projection U4 ((Wequiv theta).symm x)) := by
  have h := projection_intertwines_of_map_eq U4 (V4 theta) (Wequiv theta) rfl
  have hx := LinearMap.congr_fun h ((Wequiv theta).symm x)
  simp only [LinearMap.comp_apply] at hx
  have hWW : (Wequiv theta).toLinearMap ((Wequiv theta).symm x) = x :=
    (Wequiv theta).apply_symm_apply x
  rw [hWW] at hx
  exact hx.symm

/-- Coordinates of the target projection. -/
theorem projection_V4_coord (theta : Real) (x : E4) (i : Fin 4) :
    projection (V4 theta) x i =
      if i = 0 then Real.cos theta ^ 2 * x 0 + Real.sin theta * Real.cos theta * x 3
      else if i = 1 then Real.cos theta ^ 2 * x 1 - Real.sin theta * Real.cos theta * x 2
      else if i = 2 then Real.sin theta ^ 2 * x 2 - Real.sin theta * Real.cos theta * x 1
      else Real.sin theta ^ 2 * x 3 + Real.sin theta * Real.cos theta * x 0 := by
  rw [projection_V4_apply, Wequiv_apply, Wequiv_symm_apply, Wlin_apply]
  simp only [projection_U4_coord, Wlin'_apply]
  have hcircle := circle theta
  fin_cases i
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (Real.cos theta ^ 2 * x 0 + Real.sin theta * Real.cos theta * x 3) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (Real.cos theta ^ 2 * x 1 - Real.sin theta * Real.cos theta * x 2) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (Real.sin theta ^ 2 * x 2 - Real.sin theta * Real.cos theta * x 1) * hcircle
  · simp [Wmat, Fin.sum_univ_four]; linear_combination
      (Real.sin theta ^ 2 * x 3 + Real.sin theta * Real.cos theta * x 0) * hcircle

/-- The subspace pair is acute whenever its cosine is positive. -/
theorem acute (theta : Real) (hc : 0 < Real.cos theta) : IsAcute U4 (V4 theta) := by
  have hc2 : Real.cos theta ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  constructor
  · intro x hxU hzero
    obtain ⟨hx2, hx3⟩ := coord_eq_zero_of_mem_U4 hxU
    have h0 := congrArg (fun z : E4 => z 0) hzero
    have h1 := congrArg (fun z : E4 => z 1) hzero
    change projection (V4 theta) x 0 = 0 at h0
    change projection (V4 theta) x 1 = 0 at h1
    have hcx0 : Real.cos theta ^ 2 * x 0 = 0 := by
      simpa [projection_V4_coord, hx2, hx3] using h0
    have hcx1 : Real.cos theta ^ 2 * x 1 = 0 := by
      simpa [projection_V4_coord, hx2, hx3] using h1
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hcx0).resolve_left hc2
    have hx1 : x 1 = 0 := (mul_eq_zero.mp hcx1).resolve_left hc2
    rw [mem_U4 hxU, hx0, hx1]
    simp
  · intro y hyV hzero
    obtain ⟨z, hzU, rfl⟩ := hyV
    obtain ⟨hz2, hz3⟩ := coord_eq_zero_of_mem_U4 hzU
    have h0 := congrArg (fun x : E4 => x 0) hzero
    have h1 := congrArg (fun x : E4 => x 1) hzero
    change projection U4 (Wlin theta z) 0 = 0 at h0
    change projection U4 (Wlin theta z) 1 = 0 at h1
    have hz0eq : Real.cos theta ^ 2 * z 0 -
        Real.sin theta * Real.cos theta * z 1 = 0 := by
      simpa [projection_U4_coord, Wlin_apply, Wmat, Fin.sum_univ_four,
        hz2, hz3, sub_eq_add_neg] using h0
    have hz1eq : Real.sin theta * Real.cos theta * z 0 +
        Real.cos theta ^ 2 * z 1 = 0 := by
      simpa [projection_U4_coord, Wlin_apply, Wmat, Fin.sum_univ_four,
        hz2, hz3, sub_eq_add_neg] using h1
    have hcircle := circle theta
    have hcz0 : Real.cos theta ^ 2 * z 0 = 0 := by
      linear_combination Real.cos theta ^ 2 * hz0eq +
        Real.sin theta * Real.cos theta * hz1eq -
        (Real.cos theta ^ 2 * z 0) * hcircle
    have hcz1 : Real.cos theta ^ 2 * z 1 = 0 := by
      linear_combination Real.cos theta ^ 2 * hz1eq -
        Real.sin theta * Real.cos theta * hz0eq -
        (Real.cos theta ^ 2 * z 1) * hcircle
    have hz0 : z 0 = 0 := (mul_eq_zero.mp hcz0).resolve_left hc2
    have hz1 : z 1 = 0 := (mul_eq_zero.mp hcz1).resolve_left hc2
    rw [show z = 0 from by rw [mem_U4 hzU, hz0, hz1]; simp]
    simp

/-- The Gram operator of the canonical intertwiner is `cos(theta)^2 I`. -/
theorem gram_canonicalIntertwiner (theta : Real) :
    (canonicalIntertwiner U4 (V4 theta)).adjoint ∘ₗ
      canonicalIntertwiner U4 (V4 theta) =
        Real.cos theta ^ 2 • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
  rw [canonicalIntertwiner_adjoint_comp_self]
  apply LinearMap.ext
  intro x
  ext i
  have hcU : ∀ y : E4, complementaryProjection U4 y = y - projection U4 y :=
    fun y => Submodule.starProjection_orthogonal_val y
  have hcV : ∀ y : E4,
      complementaryProjection (V4 theta) y = y - projection (V4 theta) y :=
    fun y => Submodule.starProjection_orthogonal_val y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, hcU, hcV, map_sub]
  have hcircle := circle theta
  fin_cases i
  · simp [projection_U4_coord, projection_V4_coord]
  · simp [projection_U4_coord, projection_V4_coord]
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 2) * hcircle
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 3) * hcircle

/-- Identifying the modulus ties the calculation to the canonical direct rotation. -/
theorem abs_canonicalIntertwiner_eq (theta : Real) (hc : 0 < Real.cos theta) :
    TauCeti.operatorAbs (canonicalIntertwiner U4 (V4 theta)) =
      Real.cos theta • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
  have hpos : (Real.cos theta • (LinearMap.id : E4 →ₗ[ℝ] E4)).IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [real_inner_smul_left, real_inner_smul_right]
    · simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [real_inner_smul_left]
      simpa using mul_nonneg hc.le (real_inner_self_nonneg (x := x))
  have hsq : (Real.cos theta • (LinearMap.id : E4 →ₗ[ℝ] E4)) ∘ₗ
      (Real.cos theta • LinearMap.id) =
        (canonicalIntertwiner U4 (V4 theta)).adjoint ∘ₗ
          canonicalIntertwiner U4 (V4 theta) := by
    rw [gram_canonicalIntertwiner]
    apply LinearMap.ext
    intro x
    simp [LinearMap.comp_apply, smul_smul, pow_two]
  exact ((LinearMap.isPositive_adjoint_comp_self _).sqrt_unique hpos hsq).symm

/-- The direct displacement has scalar Gram operator `(2 - 2 cos(theta)) I`. -/
theorem gram_displacement_R (theta : Real) (hc : 0 < Real.cos theta) :
    LinearMap.adjoint (LinearMap.id - (directRotation U4 (V4 theta) (acute theta hc)).toLinearMap)
      ∘ₗ (LinearMap.id - (directRotation U4 (V4 theta) (acute theta hc)).toLinearMap) =
        (2 - 2 * Real.cos theta) • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
  rw [← displacementSquare_eq_adjoint_comp, displacementSquare_directRotation,
    abs_canonicalIntertwiner_eq theta hc]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    smul_sub, smul_smul]
  match_scalars
  ring

/-- All four singular values of the direct displacement coincide. -/
theorem singularValues_displacement_R (theta : Real) (hc : 0 < Real.cos theta) (j : Fin 4) :
    (LinearMap.id - (directRotation U4 (V4 theta) (acute theta hc)).toLinearMap).singularValues
        (j : Nat) = Real.sqrt (2 - 2 * Real.cos theta) := by
  let D := LinearMap.id - (directRotation U4 (V4 theta) (acute theta hc)).toLinearMap
  have hfr : finrank Real E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    D.isSymmetric_adjoint_comp_self hfr (EuclideanSpace.basisFun (Fin 4) Real)
    (μ := fun _ => 2 - 2 * Real.cos theta) (fun _ _ _ => le_rfl)
    (fun i => by
      rw [show LinearMap.adjoint D ∘ₗ D =
        (2 - 2 * Real.cos theta) • LinearMap.id from gram_displacement_R theta hc]
      simp)
  rw [D.singularValues_of_lt hfr j.isLt, congrFun heig ⟨(j : Nat), j.isLt⟩]

/-- The trace norm of the canonical direct displacement. -/
theorem kyFanSum_displacement_R (theta : Real) (hc : 0 < Real.cos theta) :
    kyFanSum 4 (LinearMap.id - (directRotation U4 (V4 theta) (acute theta hc)).toLinearMap) =
      4 * Real.sqrt (2 - 2 * Real.cos theta) := by
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_four]
  rw [singularValues_displacement_R theta hc 0, singularValues_displacement_R theta hc 1,
    singularValues_displacement_R theta hc 2, singularValues_displacement_R theta hc 3]
  ring

private theorem gram_displacement_W_coord (theta : Real) (x : E4) (i : Fin 4) :
    (((LinearMap.adjoint (LinearMap.id - Wlin theta) ∘ₗ
        (LinearMap.id - Wlin theta)) x : E4) i) =
      if i = 0 then 2 * Real.sin theta ^ 2 * (x 0 + x 2)
      else if i = 1 then 2 * Real.sin theta ^ 2 * (x 1 + x 3)
      else if i = 2 then 2 * Real.sin theta ^ 2 * (x 0 + x 2)
      else 2 * Real.sin theta ^ 2 * (x 1 + x 3) := by
  rw [map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  have hinv : Wlin' theta (Wlin theta x) = x :=
    LinearMap.congr_fun (Wlin'_comp_Wlin theta) x
  rw [hinv]
  have hcircle := circle theta
  fin_cases i
  · simp [Wlin_apply, Wlin'_apply, Wmat, Fin.sum_univ_four] <;>
      linear_combination (-2 * x 0) * hcircle
  · simp [Wlin_apply, Wlin'_apply, Wmat, Fin.sum_univ_four] <;>
      linear_combination (-2 * x 1) * hcircle
  · simp [Wlin_apply, Wlin'_apply, Wmat, Fin.sum_univ_four] <;>
      linear_combination (-2 * x 2) * hcircle
  · simp [Wlin_apply, Wlin'_apply, Wmat, Fin.sum_univ_four] <;>
      linear_combination (-2 * x 3) * hcircle

private theorem gram_displacement_W_basis (theta : Real) (i : Fin 4) :
    (LinearMap.adjoint (LinearMap.id - Wlin theta) ∘ₗ (LinearMap.id - Wlin theta))
        (mbasis i) =
      ((![4 * Real.sin theta ^ 2, 4 * Real.sin theta ^ 2, 0, 0] : Fin 4 -> Real) i)
        • mbasis i := by
  ext k
  rw [gram_displacement_W_coord]
  fin_cases i <;> fin_cases k <;> simp [mbasis_coe, mv, sv] <;> ring

private theorem antitone_pair (a : Real) (ha : 0 ≤ a) :
    Antitone (![a, a, 0, 0] : Fin 4 -> Real) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Singular values of the competitor displacement, computed in its fixed rotation basis. -/
theorem singularValues_displacement_W (theta : Real) (j : Fin 4) :
    (LinearMap.id - Wlin theta).singularValues (j : Nat) =
      Real.sqrt ((![4 * Real.sin theta ^ 2, 4 * Real.sin theta ^ 2, 0, 0] : Fin 4 -> Real) j) := by
  let D := LinearMap.id - Wlin theta
  have hfr : finrank Real E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    D.isSymmetric_adjoint_comp_self hfr mbasis
    (μ := ![4 * Real.sin theta ^ 2, 4 * Real.sin theta ^ 2, 0, 0])
    (antitone_pair _ (by positivity)) (gram_displacement_W_basis theta)
  rw [D.singularValues_of_lt hfr j.isLt, congrFun heig ⟨(j : Nat), j.isLt⟩]

/-- The trace norm of the competitor is `4 sin(theta)` for nonnegative sine. -/
theorem kyFanSum_displacement_W (theta : Real) (hs : 0 ≤ Real.sin theta) :
    kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) = 4 * Real.sin theta := by
  have hsqrt : Real.sqrt (4 * Real.sin theta ^ 2) = 2 * Real.sin theta := by
    have hsq := Real.sq_sqrt (by positivity : (0 : Real) ≤ 4 * Real.sin theta ^ 2)
    have hn := Real.sqrt_nonneg (4 * Real.sin theta ^ 2)
    nlinarith
  rw [Wequiv_toLinearMap, kyFanSum_eq_sum_fin, Fin.sum_univ_four]
  simp only [singularValues_displacement_W theta 0, singularValues_displacement_W theta 1,
    singularValues_displacement_W theta 2, singularValues_displacement_W theta 3]
  change Real.sqrt (4 * Real.sin theta ^ 2) + Real.sqrt (4 * Real.sin theta ^ 2) +
    Real.sqrt 0 + Real.sqrt 0 = 4 * Real.sin theta
  rw [Real.sqrt_zero, hsqrt]
  ring

private theorem gram_sinThetaMap (theta : Real) :
    (sinThetaMap U4 (V4 theta)).adjoint ∘ₗ sinThetaMap U4 (V4 theta) =
      projection U4 - projection U4 ∘ₗ projection (V4 theta) ∘ₗ projection U4 := by
  have hAadj : (sinThetaMap U4 (V4 theta)).adjoint =
      projection U4 ∘ₗ complementaryProjection (V4 theta) := by
    rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint]
    congr 1
    simp [complementaryProjection]
  have hUidem : ∀ y : E4, projection U4 (projection U4 y) = projection U4 y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U4.starProjection_apply_mem y)
  have hcVidem : ∀ y : E4,
      complementaryProjection (V4 theta) (complementaryProjection (V4 theta) y) =
        complementaryProjection (V4 theta) y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr ((V4 theta)ᗮ.starProjection_apply_mem y)
  have hcV : ∀ y : E4,
      complementaryProjection (V4 theta) y = y - projection (V4 theta) y :=
    fun y => Submodule.starProjection_orthogonal_val y
  rw [hAadj, sinThetaMap]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply]
  rw [hcVidem (projection U4 x), hcV (projection U4 x), map_sub, hUidem x]

private theorem gram_sinThetaMap_coord (theta : Real) (x : E4) (i : Fin 4) :
    (((sinThetaMap U4 (V4 theta)).adjoint ∘ₗ sinThetaMap U4 (V4 theta)) x) i =
      if i = 0 then Real.sin theta ^ 2 * x 0
      else if i = 1 then Real.sin theta ^ 2 * x 1 else 0 := by
  rw [gram_sinThetaMap]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  have hcircle := circle theta
  fin_cases i
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 0) * hcircle
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 1) * hcircle
  · simp [projection_U4_coord]
  · simp [projection_U4_coord]

private theorem gram_sinThetaMap_basis (theta : Real) (i : Fin 4) :
    ((sinThetaMap U4 (V4 theta)).adjoint ∘ₗ sinThetaMap U4 (V4 theta))
        (EuclideanSpace.basisFun (Fin 4) Real i) =
      ((![Real.sin theta ^ 2, Real.sin theta ^ 2, 0, 0] : Fin 4 -> Real) i)
        • EuclideanSpace.basisFun (Fin 4) Real i := by
  ext k
  rw [gram_sinThetaMap_coord]
  fin_cases i <;> fin_cases k <;> simp [EuclideanSpace.basisFun_apply]

/-- The first two principal sines are `sin(theta)`. -/
theorem principalSines_eq (theta : Real) (hs : 0 ≤ Real.sin theta)
    (j : Fin 4) (hj : (j : Nat) < 2) :
    principalSines U4 (V4 theta) (j : Nat) = Real.sin theta := by
  have hfr : finrank Real E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    (sinThetaMap U4 (V4 theta)).isSymmetric_adjoint_comp_self hfr
    (EuclideanSpace.basisFun (Fin 4) Real)
    (μ := ![Real.sin theta ^ 2, Real.sin theta ^ 2, 0, 0])
    (antitone_pair _ (sq_nonneg _)) (gram_sinThetaMap_basis theta)
  rw [principalSines,
    (sinThetaMap U4 (V4 theta)).singularValues_of_lt hfr j.isLt,
    congrFun heig ⟨(j : Nat), j.isLt⟩]
  fin_cases j <;> simp_all

/-- Both principal angles are exactly the parameter; no angle bound is assumed of the pair. -/
theorem principalAngles_eq (theta : Real) (h0 : 0 < theta) (h1 : theta < Real.pi / 2)
    (j : Fin 4) (hj : (j : Nat) < 2) :
    principalAngles U4 (V4 theta) (j : Nat) = theta := by
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [principalAngles, Finsupp.mapRange_apply, principalSines_eq theta hs.le j hj]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) h1.le

/-- Cosine is positive on the parameter interval used by the counterexample. -/
theorem cos_pos (theta : Real) (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    0 < Real.cos theta :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

/-- The strict trace-norm comparison, for every acute positive angle. -/
theorem kyFanSum_lt (theta : Real) (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) <
      kyFanSum 4 (LinearMap.id -
        (directRotation U4 (V4 theta) (acute theta (cos_pos theta h0 h1))).toLinearMap) := by
  have hc : 0 < Real.cos theta := cos_pos theta h0 h1
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  rw [kyFanSum_displacement_W theta hs.le, kyFanSum_displacement_R theta hc]
  have hcircle := circle theta
  have hc1 : Real.cos theta < 1 := by nlinarith [sq_pos_of_pos hs]
  have hchord : 0 ≤ 2 - 2 * Real.cos theta := by linarith
  have hsq := Real.sq_sqrt hchord
  have hn := Real.sqrt_nonneg (2 - 2 * Real.cos theta)
  have hpositive := sq_pos_of_pos (sub_pos.mpr hc1)
  have hsquares :
      (4 * Real.sin theta) ^ 2 < (4 * Real.sqrt (2 - 2 * Real.cos theta)) ^ 2 := by
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsquares

/-- Recovering the sign-matrix competitor at the original angle. -/
theorem Wmat_pi_div_four : Wmat (Real.pi / 4) = ShortRotationCounterexample.Wmat := by
  have hroot := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wmat, ShortRotationCounterexample.Wmat, Real.sin_pi_div_four,
      Real.cos_pi_div_four, Matrix.smul_apply] <;> nlinarith

end
end SmallAngleCounterexample

/-- **No positive angle threshold repairs Proposition 4.4.** For every positive
`epsilon`, an acute pair of subspaces of a real four-dimensional space has a strictly
positive largest principal angle below both `epsilon` and the printed `pi/3`
threshold, yet an orthogonal competitor beats its canonical direct rotation in
trace norm. This strengthening is separate from the source-result inventory. -/
theorem arbitrarilySmall_fullDisplacement_refuted (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (U V : Submodule Real (EuclideanSpace Real (Fin 4)))
      (hacute : IsAcute U V)
      (W : EuclideanSpace Real (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace Real (Fin 4)),
      U.map W.toLinearMap = V ∧
      0 < principalAngles U V 0 ∧
      principalAngles U V 0 < epsilon ∧
      principalAngles U V 0 ≤ Real.pi / 3 ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) <
        kyFanSum 4 (LinearMap.id - (directRotation U V hacute).toLinearMap) := by
  let theta := min (epsilon / 2) (Real.pi / 4)
  have h0 : 0 < theta := lt_min (by linarith) (by linarith [Real.pi_pos])
  have heps : theta < epsilon :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hquarter : theta ≤ Real.pi / 4 := min_le_right _ _
  have h1 : theta < Real.pi / 2 := by linarith [Real.pi_pos]
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hangle :
      principalAngles ShortRotationCounterexample.U4 (SmallAngleCounterexample.V4 theta) 0 =
        theta := by
    simpa using (SmallAngleCounterexample.principalAngles_eq theta h0 h1
      (0 : Fin 4) (by norm_num))
  refine ⟨ShortRotationCounterexample.U4, SmallAngleCounterexample.V4 theta,
    SmallAngleCounterexample.acute theta hc, SmallAngleCounterexample.Wequiv theta,
    rfl, ?_, ?_, ?_, SmallAngleCounterexample.kyFanSum_lt theta h0 h1⟩
  · rw [hangle]
    exact h0
  · rw [hangle]
    exact heps
  · rw [hangle]
    linarith [Real.pi_pos]

end DavisKahan.FiniteDimensional
end TauCeti
