/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.FiniteDimensional.DirectRotation.Basic
import DavisKahan.FiniteDimensional.Residual.Ritz
import ForMathlib.Analysis.InnerProductSpace.SingularSystem
import ForMathlib.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Principal planes of an acute pair

This file constructs the finite principal planes used in Davis--Kahan Section 4
without assuming a `FiniteTwoProjection` API.  The source vectors are the
nonzero right singular vectors of the directed sine block
`P_{V orthogonal} P_U`.  If `s_i` is the corresponding singular value, put
`c_i = sqrt (1-s_i^2)` and

`j_i = s_i^{-1} (R u_i - c_i u_i)`,

where `R` is the canonical direct rotation.  Acuteness gives `c_i > 0`, and the
polar identities give

`R u_i = c_i u_i + s_i j_i`,
`R j_i = -s_i u_i + c_i j_i`.

The family `(u_i,j_i)` is orthonormal, the `s_i` are decreasing, and the
singular values of `I-R` are the duplicated chord lengths
`d_i = sqrt (2(1-c_i))`.  These are exactly the finite principal-plane facts
used in the source proof of Propositions 4.1--4.4.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The number of nonzero directed principal sines. -/
noncomputable def nontrivialAngleCount (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ :=
  finrank 𝕜 (sinThetaMap U V).range

/-- Cast a nontrivial-angle index into the ambient right singular basis. -/
noncomputable def nontrivialAngleIndex (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : Fin (finrank 𝕜 E) :=
  Fin.castLE (LinearMap.finrank_range_le (sinThetaMap U V)) i

/-- Source principal vector. -/
noncomputable def principalSourceVector (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : E :=
  rightSingularBasis (sinThetaMap U V) (nontrivialAngleIndex U V i)

/-- Sine attached to a nontrivial principal plane. -/
noncomputable def principalPlaneSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  (sinThetaMap U V).singularValues (nontrivialAngleIndex U V i)

/-- Cosine attached to a nontrivial principal plane. -/
noncomputable def principalPlaneCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  Real.sqrt (1 - principalPlaneSine U V i ^ 2)

/-- Chord length `2 sin(theta_i/2)`. -/
noncomputable def principalPlaneChord (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  Real.sqrt (2 * (1 - principalPlaneCosine U V i))

/-- The source-orthogonal partner of a principal source vector. -/
noncomputable def principalOrthogonalVector (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) : E :=
  ((principalPlaneSine U V i)⁻¹ : ℝ) •
    (directRotation U V hacute (principalSourceVector U V i) -
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i)

/-- Nonzero singular values are strictly positive on the range-rank prefix. -/
theorem principalPlaneSine_pos
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    0 < principalPlaneSine U V i := by
  rw [principalPlaneSine]
  exact (sinThetaMap U V).singularValues_pos_iff_lt_finrank_range.mpr i.isLt

/-- Directed principal sines are at most one. -/
theorem principalPlaneSine_le_one
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneSine U V i ≤ 1 := by
  rw [principalPlaneSine]
  exact (singularValues_comp_le (c := 1) (by norm_num)
    (fun x => Vᗮ.norm_starProjection_apply_le x)
    (projection U) (nontrivialAngleIndex U V i)).trans_eq (one_mul _)

/-- The source singular vector belongs to `U`. -/
theorem principalSourceVector_mem
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalSourceVector U V i ∈ U := by
  let A := sinThetaMap U V
  let p := nontrivialAngleIndex U V i
  let s := principalPlaneSine U V i
  have hs : s ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have heig := adjointCompSelf_apply_rightSingularBasis A p
  have hgram : A.adjoint ∘ₗ A =
      projection U - projection U ∘ₗ projection V ∘ₗ projection U := by
    ext x
    simp [A, sinThetaMap, complementaryProjection, LinearMap.adjoint_comp,
      projection_adjoint]
    module
  rw [hgram] at heig
  have hproj : projection U (principalSourceVector U V i) =
      principalSourceVector U V i := by
    apply (smul_left_cancel₀ (((s ^ 2 : ℝ) : 𝕜)))
    · exact RCLike.ofReal_ne_zero.mpr (sq_ne_zero.mpr hs)
    · simpa [A, p, s, principalSourceVector, principalPlaneSine,
        LinearMap.sub_apply, LinearMap.comp_apply] using
        congrArg (projection U) heig
  exact Submodule.starProjection_eq_self_iff.mp hproj

/-- The source principal vectors are orthonormal. -/
theorem orthonormal_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Orthonormal 𝕜 (principalSourceVector U V) := by
  exact (rightSingularBasis (sinThetaMap U V)).orthonormal.comp
    (nontrivialAngleIndex U V)
    (Fin.castLE_injective (LinearMap.finrank_range_le (sinThetaMap U V)))

/-- The source cosine has the expected Pythagorean identity. -/
theorem principalPlaneCosine_sq_add_sine_sq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneCosine U V i ^ 2 + principalPlaneSine U V i ^ 2 = 1 := by
  rw [principalPlaneCosine, Real.sq_sqrt]
  · ring
  · nlinarith [principalPlaneSine_pos U V i,
      principalPlaneSine_le_one U V i]

/-- Acuteness makes every principal-plane cosine strictly positive. -/
theorem principalPlaneCosine_pos
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    0 < principalPlaneCosine U V i := by
  rw [principalPlaneCosine, Real.sqrt_pos.iff]
  have hu := principalSourceVector_mem U V hacute i
  have hnot : principalPlaneSine U V i ≠ 1 := by
    intro hs
    let u := principalSourceVector U V i
    have hu1 : ‖u‖ = 1 := (orthonormal_principalSourceVector U V).norm_eq_one i
    have hnorm := norm_apply_rightSingularBasis
      (sinThetaMap U V) (nontrivialAngleIndex U V i)
    have hzero : projection V u = 0 := by
      have hsquare := principalPlaneCosine_sq_add_sine_sq U V i
      rw [hs] at hsquare
      have hcos0 : principalPlaneCosine U V i = 0 := by nlinarith
      have hdecomp := V.norm_starProjection_sq_add_norm_starProjection_orthogonal_sq u
      have hsinNorm : ‖complementaryProjection V u‖ = 1 := by
        simpa [sinThetaMap, LinearMap.comp_apply,
          projection_apply_of_mem hu, principalPlaneSine, u] using hnorm
      rw [hsinNorm, hu1] at hdecomp
      nlinarith [norm_nonneg (projection V u)]
    exact (by
      have := hacute.1 u hu hzero
      exact one_ne_zero (hu1.symm.trans (by rw [this, norm_zero])))
  nlinarith [principalPlaneSine_pos U V i,
    principalPlaneSine_le_one U V i]

/-- The positive modulus of the canonical intertwiner acts by the principal
cosine on the source vector. -/
theorem abs_canonicalIntertwiner_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    ForMathlib.abs (canonicalIntertwiner U V) (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
  let A := sinThetaMap U V
  let u := principalSourceVector U V i
  let s := principalPlaneSine U V i
  let c := principalPlaneCosine U V i
  have hu := principalSourceVector_mem U V hacute i
  have heig := adjointCompSelf_apply_rightSingularBasis A
    (nontrivialAngleIndex U V i)
  have hgram :
      (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
        LinearMap.id - A.adjoint ∘ₗ A := by
    ext x
    simp [A, canonicalIntertwiner_adjoint_comp_self, sinThetaMap,
      complementaryProjection]
    module
  have hsq :
      ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) u =
        (((c ^ 2 : ℝ) : 𝕜) • u) := by
    rw [hgram, LinearMap.sub_apply, LinearMap.id_apply, heig]
    rw [← RCLike.ofReal_sub, show 1 - s ^ 2 = c ^ 2 by
      nlinarith [principalPlaneCosine_sq_add_sine_sq U V i]]
  exact (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V)).sqrt_apply_eq_of_sq
    (principalPlaneCosine_pos U V hacute i).le hsq


/-- Every principal-plane cosine occurs in the singular-value multiset of the
canonical intertwiner.  The index is not the original sine index: principal
sines decrease while their complementary cosines increase. -/
theorem exists_canonicalIntertwiner_singularValue_eq_principalPlaneCosine
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    ∃ j : Fin (finrank 𝕜 E),
      (canonicalIntertwiner U V).singularValues (j : ℕ) =
        principalPlaneCosine U V i := by
  let S := canonicalIntertwiner U V
  let u := principalSourceVector U V i
  let c := principalPlaneCosine U V i
  have hu1 : ‖u‖ = 1 := (orthonormal_principalSourceVector U V).norm_eq_one i
  have heigAbs : ForMathlib.abs S u = (c : 𝕜) • u := by
    simpa [S, u, c] using
      abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have heig : (isPositive_abs S).isSymmetric.HasEigenvalue c := by
    refine ⟨u, ?_, ?_⟩
    · exact fun h => by simpa [h] using hu1
    · simpa [S, u, c] using heigAbs
  obtain ⟨j, hj⟩ := (isPositive_abs S).isSymmetric.exists_eigenvalue_eq rfl heig
  refine ⟨j, ?_⟩
  rw [← congrFun (eigenvalues_abs S) j, hj]

/-- The direct rotation has the canonical cosine-sine action on a source
principal vector. -/
theorem directRotation_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    directRotation U V hacute (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneSine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  rw [principalOrthogonalVector]
  have hs : principalPlaneSine U V i ≠ 0 :=
    ne_of_gt (principalPlaneSine_pos U V i)
  push_cast
  field_simp
  module

/-- The orthogonal partner belongs to `U orthogonal`. -/
theorem principalOrthogonalVector_mem
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalOrthogonalVector U V hacute i ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal']
  intro x hx
  rw [principalOrthogonalVector, inner_smul_right, inner_sub_right,
    inner_smul_right]
  have hdiag : projection U
      (directRotation U V hacute (principalSourceVector U V i)) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
    have hpolar := polar_decomposition_of_isUnit
      (canonicalIntertwiner_isUnit_of_acute U V hacute)
    have hsource := canonicalIntertwiner_comp_projection U V
    have hu := principalSourceVector_mem U V hacute i
    have hC := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
    refine ext_inner_right 𝕜 fun y => ?_
    rw [projection_inner_left_eq_right]
    have hy := LinearMap.congr_fun (directRotation_comp_projection U V hacute) y
    simp only [LinearMap.comp_apply] at hy
    rw [← hy, (directRotation U V hacute).inner_map_map]
    simpa [projection_apply_of_mem hu, hC]
  rw [← projection_inner_left_eq_right, hdiag,
    inner_smul_right, projection_apply_of_mem hx]
  ring

/-- Principal orthogonal partners are orthonormal. -/
theorem orthonormal_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (principalOrthogonalVector U V hacute) := by
  rw [orthonormal_iff_ite]
  intro i j
  let R := directRotation U V hacute
  let ui := principalSourceVector U V i
  let uj := principalSourceVector U V j
  let ci := principalPlaneCosine U V i
  let cj := principalPlaneCosine U V j
  let si := principalPlaneSine U V i
  let sj := principalPlaneSine U V j
  have hsi : si ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have hsj : sj ≠ 0 := ne_of_gt (principalPlaneSine_pos U V j)
  have hu := orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) i j
  have hdiag : ⟪R ui, uj⟫_𝕜 = (ci : 𝕜) * (if i = j then 1 else 0) := by
    rw [← projection_inner_left_eq_right,
      show projection U (R ui) = (ci : 𝕜) • ui by
        have hmem := principalOrthogonalVector_mem U V hacute i
        rw [directRotation_apply_principalSourceVector U V hacute i]
        simp [projection_apply_of_mem (principalSourceVector_mem U V hacute i),
          projection_apply_of_mem_orthogonal hmem]]
    rw [inner_smul_left, RCLike.conj_ofReal, hu]
  rw [principalOrthogonalVector, principalOrthogonalVector,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_sub_left, inner_sub_right, R.inner_map_map, hdiag, hu]
  have hdiag' : ⟪ui, R uj⟫_𝕜 = (cj : 𝕜) * (if i = j then 1 else 0) := by
    rw [inner_conj_symm, hdiag]
    simp [RCLike.conj_ofReal]
  rw [hdiag']
  split_ifs with hij
  · subst hij
    simp only [if_pos, mul_one]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_sub, ← RCLike.ofReal_add]
    push_cast
    field_simp
    nlinarith [principalPlaneCosine_sq_add_sine_sq U V i]
  · simp [hij]

/-- The two vectors in distinct principal planes are mutually orthogonal. -/
theorem orthonormal_principalPlaneFamily
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (fun p : Fin (nontrivialAngleCount U V) × Fin 2 =>
      if p.2 = 0 then principalSourceVector U V p.1
      else principalOrthogonalVector U V hacute p.1) := by
  rw [orthonormal_iff_ite]
  intro p q
  fin_cases p.2 <;> fin_cases q.2
  · simpa using orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) p.1 q.1
  · have hp := principalSourceVector_mem U V hacute p.1
    have hq := principalOrthogonalVector_mem U V hacute q.1
    simp [Submodule.inner_right_of_mem_orthogonal hp hq]
  · have hp := principalOrthogonalVector_mem U V hacute p.1
    have hq := principalSourceVector_mem U V hacute q.1
    simp [Submodule.inner_right_of_mem_orthogonal hq hp, inner_conj_symm]
  · simpa using orthonormal_iff_ite.mp
      (orthonormal_principalOrthogonalVector U V hacute) p.1 q.1

/-- The direct rotation acts on the orthogonal partner by the second column of
its principal rotation block. -/
theorem directRotation_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    directRotation U V hacute (principalOrthogonalVector U V hacute i) =
      -(principalPlaneSine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneCosine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  let R := directRotation U V hacute
  let u := principalSourceVector U V i
  let j := principalOrthogonalVector U V hacute i
  let c := principalPlaneCosine U V i
  let s := principalPlaneSine U V i
  have hs : s ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have hRu := directRotation_apply_principalSourceVector U V hacute i
  have hRe : (R.toLinearMap + R.symm.toLinearMap) u = (2 * c : ℝ) • u := by
    have htwo := LinearMap.congr_fun
      (two_smul_abs_canonicalIntertwiner U V hacute) u
    rw [abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i] at htwo
    simpa [R, c, LinearMap.add_apply, LinearMap.smul_apply, ← RCLike.ofReal_mul]
      using htwo.symm
  have hRstaru : R.symm u = (c : 𝕜) • u - (s : 𝕜) • j := by
    have := hRe
    simp only [LinearMap.add_apply] at this
    rw [hRu] at this
    module
  apply R.injective
  rw [R.map_add, R.map_smul, R.map_smul, R.apply_symm_apply]
  rw [hRstaru]
  module

/-- Principal sines decrease with the index. -/
theorem principalPlaneSine_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneSine U V) := by
  intro i j hij
  exact (sinThetaMap U V).singularValues_antitone
    (Fin.castLE_mono (LinearMap.finrank_range_le (sinThetaMap U V)) hij)

/-- Principal cosines increase, so chord lengths decrease. -/
theorem principalPlaneChord_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneChord U V) := by
  intro i j hij
  have hs := principalPlaneSine_antitone U V hij
  have hci : 0 ≤ principalPlaneCosine U V i := Real.sqrt_nonneg _
  have hcj : 0 ≤ principalPlaneCosine U V j := Real.sqrt_nonneg _
  have hc : principalPlaneCosine U V i ≥ principalPlaneCosine U V j := by
    apply (sq_le_sq₀ hcj hci).mp
    rw [principalPlaneCosine_sq_add_sine_sq U V i,
      principalPlaneCosine_sq_add_sine_sq U V j]
    nlinarith [principalPlaneSine_pos U V i, principalPlaneSine_pos U V j]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- Explicit isometric embedding of the `i`th principal plane. -/
noncomputable def principalPlaneEmbedding
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    EuclideanSpace 𝕜 (Fin 2) →ₗᵢ[𝕜] E where
  toLinearMap :=
    { toFun := fun x => x 0 • principalSourceVector U V i +
        x 1 • principalOrthogonalVector U V hacute i
      map_add' := by intro x y; module
      map_smul' := by intro a x; module }
  norm_map' := by
    intro x
    rw [show ‖x 0 • principalSourceVector U V i +
          x 1 • principalOrthogonalVector U V hacute i‖ ^ 2 =
        ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 by
      rw [(orthonormal_principalPlaneFamily U V hacute).pairwise
        (by simp) |>.norm_add_sq]
      simp [(orthonormal_principalSourceVector U V).norm_eq_one,
        (orthonormal_principalOrthogonalVector U V hacute).norm_eq_one]
    rw [EuclideanSpace.norm_sq_eq_sum]
    simp [Fin.sum_univ_two]

/-- Compression of the direct displacement to a principal plane. -/
theorem compression_directRotation_displacement_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    compression (LinearMap.id - (directRotation U V hacute).toLinearMap)
      (principalPlaneEmbedding U V hacute i) =
      Matrix.toEuclideanLin
        !![((1 - principalPlaneCosine U V i : ℝ) : 𝕜),
           ((principalPlaneSine U V i : ℝ) : 𝕜);
           ((-principalPlaneSine U V i : ℝ) : 𝕜),
           ((1 - principalPlaneCosine U V i : ℝ) : 𝕜)] := by
  apply (EuclideanSpace.basisFun (Fin 2) 𝕜).toBasis.ext
  intro a
  rw [OrthonormalBasis.coe_toBasis]
  fin_cases a <;>
    ext b <;> fin_cases b <;>
    simp [compression, principalPlaneEmbedding, LinearMap.comp_apply,
      directRotation_apply_principalSourceVector,
      directRotation_apply_principalOrthogonalVector,
      orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V),
      orthonormal_iff_ite.mp (orthonormal_principalOrthogonalVector U V hacute),
      principalSourceVector_mem, principalOrthogonalVector_mem,
      EuclideanSpace.basisFun_apply, Matrix.toEuclideanLin_apply,
      PiLp.single_apply]

/-- The direct displacement has two equal singular values on every nontrivial
principal plane. -/
theorem singularValues_compression_directRotation_displacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    (compression (LinearMap.id - (directRotation U V hacute).toLinearMap)
      (principalPlaneEmbedding U V hacute i)).singularValues =
      pairSingularValues (principalPlaneChord U V i)
        (principalPlaneChord U V i) := by
  rw [compression_directRotation_displacement_eq U V hacute i]
  let c := principalPlaneCosine U V i
  let s := principalPlaneSine U V i
  let d := principalPlaneChord U V i
  let A : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
    Matrix.toEuclideanLin !![((1-c : ℝ) : 𝕜), (s : 𝕜); (-s : 𝕜), ((1-c : ℝ) : 𝕜)]
  have hgram : A.adjoint ∘ₗ A = (((d ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
    ext x a
    fin_cases a <;>
      simp [A, LinearMap.comp_apply, Matrix.toEuclideanLin_apply,
        Fin.sum_univ_two, d, principalPlaneChord] <;>
      push_cast <;>
      nlinarith [principalPlaneCosine_sq_add_sine_sq U V i]
  have hsymGram : A.adjoint ∘ₗ A =
      diagOp (EuclideanSpace.basisFun (Fin 2) 𝕜) ![d^2,d^2] := by
    rw [hgram]
    apply (EuclideanSpace.basisFun (Fin 2) 𝕜).toBasis.ext
    intro a
    rw [OrthonormalBasis.coe_toBasis]
    fin_cases a <;> simp [diagOp_apply_basis]
  exact singularValues_eq_pair_of_gram_eq finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin 2) 𝕜) A (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) le_rfl hsymGram


/-! ## Davis's local two-plane comparison -/

/-- The restriction of a displacement to the `i`th source principal plane. -/
noncomputable def principalPlaneDisplacementRestriction
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E →ₗ[𝕜] E)
    (i : Fin (nontrivialAngleCount U V)) :
    EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  compression (LinearMap.id - W) (principalPlaneEmbedding U V hacute i)

/-- The two real diagonal coefficients used in Davis--Kahan (4.5). -/
noncomputable def principalPlaneCoefficient0
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  ⟪directRotation U V hacute (principalSourceVector U V i),
    W (principalSourceVector U V i)⟫_ℝ

noncomputable def principalPlaneCoefficient1
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  ⟪directRotation U V hacute (principalOrthogonalVector U V hacute i),
    W (principalOrthogonalVector U V hacute i)⟫_ℝ

/-- Average and half-difference of the two coefficients. -/
noncomputable def principalPlaneAverage
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  (principalPlaneCoefficient0 U V hacute W i +
    principalPlaneCoefficient1 U V hacute W i) / 2

noncomputable def principalPlaneHalfDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  (principalPlaneCoefficient0 U V hacute W i -
    principalPlaneCoefficient1 U V hacute W i) / 2

/-- The squared singular values of the restricted competitor displacement,
written in the form of Davis--Kahan equation (4.5), in the real case. -/
noncomputable def davisPlanarLambdaPlus (c s p q : ℝ) : ℝ :=
  2 * (1 - p * c + |q| * s)

noncomputable def davisPlanarLambdaMinus (c s p q : ℝ) : ℝ :=
  2 * (1 - p * c - |q| * s)

/-- Elementary coefficient constraints coming from two unit vectors. -/
theorem principalPlane_coefficients_constraints
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) :
    |principalPlaneCoefficient0 U V hacute W i| ≤ 1 ∧
      |principalPlaneCoefficient1 U V hacute W i| ≤ 1 := by
  constructor
  · exact (abs_real_inner_le_norm _ _).trans_eq (by
      rw [(directRotation U V hacute).norm_map, W.norm_map,
        (orthonormal_principalSourceVector U V).norm_eq_one, mul_one])
  · exact (abs_real_inner_le_norm _ _).trans_eq (by
      rw [(directRotation U V hacute).norm_map, W.norm_map,
        (orthonormal_principalOrthogonalVector U V hacute).norm_eq_one, mul_one])

/-- The average/half-difference constraints used in (4.6). -/
theorem principalPlane_average_halfDifference_constraints
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (i : Fin (nontrivialAngleCount U V)) :
    (principalPlaneAverage U V hacute W i +
        principalPlaneHalfDifference U V hacute W i) ^ 2 ≤ 1 ∧
      (principalPlaneAverage U V hacute W i -
        principalPlaneHalfDifference U V hacute W i) ^ 2 ≤ 1 := by
  have h := principalPlane_coefficients_constraints U V hacute W i
  dsimp [principalPlaneAverage, principalPlaneHalfDifference]
  constructor <;> nlinarith [sq_le_sq₀ (abs_nonneg _) h.1,
    sq_le_sq₀ (abs_nonneg _) h.2]

/-- The scalar heart of Proposition 4.4.  It is deliberately stated over the
reals: the paper gives a complex counterexample, so no RCLike generalization is
valid. -/
theorem davis_planar_short_rotation_scalar
    {c s p q : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hhalf : 1 / 2 ≤ c)
    (hs0 : 0 ≤ s) (hpyth : c ^ 2 + s ^ 2 = 1)
    (hpq0 : (p + q) ^ 2 ≤ 1) (hpq1 : (p - q) ^ 2 ≤ 1) :
    Real.sqrt (2 * (1 - c)) ≤
        Real.sqrt (davisPlanarLambdaPlus c s p q) ∧
      2 * Real.sqrt (2 * (1 - c)) ≤
        Real.sqrt (davisPlanarLambdaPlus c s p q) +
          Real.sqrt (davisPlanarLambdaMinus c s p q) := by
  have hp_le : p ≤ 1 := by nlinarith [sq_nonneg q, hpq0, hpq1]
  have hp_ge : -1 ≤ p := by nlinarith [sq_nonneg q, hpq0, hpq1]
  have hpq : p ^ 2 + q ^ 2 ≤ 1 := by nlinarith [hpq0, hpq1]
  have hcs : p * c + |q| * s ≤ 1 := by
    have hsq : (p * c + |q| * s) ^ 2 ≤ 1 := by
      have hcross : 2 * p * c * (|q| * s) ≤
          p ^ 2 * s ^ 2 + q ^ 2 * c ^ 2 := by
        nlinarith [sq_nonneg (p * s - |q| * c), sq_abs q]
      nlinarith [hpq, hpyth, sq_abs q]
    rcases le_total (p * c + |q| * s) 0 with hneg | hpos
    · linarith
    · nlinarith
  have hminus0 : 0 ≤ davisPlanarLambdaMinus c s p q := by
    dsimp [davisPlanarLambdaMinus]
    nlinarith
  have hplus0 : 0 ≤ davisPlanarLambdaPlus c s p q := by
    dsimp [davisPlanarLambdaPlus]
    nlinarith [hminus0, abs_nonneg q, hs0]
  have hchord0 : 0 ≤ 2 * (1 - c) := by linarith
  constructor
  · apply Real.sqrt_le_sqrt
    dsimp [davisPlanarLambdaPlus]
    nlinarith [abs_nonneg q, hs0]
  · let a := 1 - p * c
    let b := |q| * s
    have hab0 : 0 ≤ a - b := by
      dsimp [a, b]
      exact hcs
    have hab1 : 0 ≤ a + b := by
      dsimp [a, b]
      nlinarith [hcs, abs_nonneg q, hs0]
    have hqbound : q ^ 2 * (1 + c) ≤ 4 * c * (1 - p) := by
      rcases le_total 0 p with hp | hp
      · have hq2 : q ^ 2 ≤ (1 - p) ^ 2 := by
          nlinarith [hpq0, hpq1]
        have hcaux : (1 + c) * (1 - p) ≤ 4 * c := by
          nlinarith
        nlinarith
      · have hq2 : q ^ 2 ≤ (1 + p) ^ 2 := by
          nlinarith [hpq0, hpq1]
        have hpaux : (1 + p) ^ 2 ≤ 1 - p := by
          nlinarith
        have hcaux : 1 + c ≤ 4 * c := by nlinarith
        nlinarith
    have hdisc :
        (2 * (1 - c) - a) ^ 2 ≤ a ^ 2 - b ^ 2 := by
      dsimp [a, b]
      rw [sq_abs]
      nlinarith [hpyth, hqbound]
    have hsqrt_disc :
        2 * (1 - c) - a ≤ Real.sqrt (a ^ 2 - b ^ 2) := by
      rcases le_total (2 * (1 - c) - a) 0 with hnonpos | hpos
      · exact hnonpos.trans (Real.sqrt_nonneg _)
      · exact (sq_le_sq₀ hpos (Real.sqrt_nonneg _)).mp (by
          rw [Real.sq_sqrt]
          · exact hdisc
          · nlinarith [mul_nonneg hab0 hab1])
    have hsquare :
        (Real.sqrt (2 * (a + b)) + Real.sqrt (2 * (a - b))) ^ 2 ≥
          (2 * Real.sqrt (2 * (1 - c))) ^ 2 := by
      rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        mul_pow, Real.sq_sqrt hchord0]
      have hprod : Real.sqrt (2 * (a + b)) * Real.sqrt (2 * (a - b)) =
          2 * Real.sqrt (a ^ 2 - b ^ 2) := by
        rw [← Real.sqrt_mul (by positivity), show
          (2 * (a + b)) * (2 * (a - b)) = 4 * (a ^ 2 - b ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
      rw [hprod]
      nlinarith
    have hleft0 : 0 ≤ 2 * Real.sqrt (2 * (1 - c)) := by positivity
    have hright0 : 0 ≤ Real.sqrt (2 * (a + b)) + Real.sqrt (2 * (a - b)) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have := (sq_le_sq₀ hleft0 hright0).mp hsquare
    simpa [a, b, davisPlanarLambdaPlus, davisPlanarLambdaMinus] using this

/-- Exact two-plane Gram eigenvalues for a competing unitary.  This is the
finite-dimensional operator form of equation (4.5). -/
theorem singularValues_principalPlaneDisplacementRestriction_real
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (hmap : U.map W.toLinearMap = V)
    (i : Fin (nontrivialAngleCount U V)) :
    (principalPlaneDisplacementRestriction U V hacute W.toLinearMap i).singularValues =
      pairSingularValues
        (Real.sqrt (davisPlanarLambdaPlus
          (principalPlaneCosine U V i) (principalPlaneSine U V i)
          (principalPlaneAverage U V hacute W i)
          (principalPlaneHalfDifference U V hacute W i)))
        (Real.sqrt (davisPlanarLambdaMinus
          (principalPlaneCosine U V i) (principalPlaneSine U V i)
          (principalPlaneAverage U V hacute W i)
          (principalPlaneHalfDifference U V hacute W i))) := by
  classical
  let A := principalPlaneDisplacementRestriction U V hacute W.toLinearMap i
  let c := principalPlaneCosine U V i
  let s := principalPlaneSine U V i
  let p := principalPlaneAverage U V hacute W i
  let q := principalPlaneHalfDifference U V hacute W i
  let lp := davisPlanarLambdaPlus c s p q
  let lm := davisPlanarLambdaMinus c s p q
  have hconstraints := principalPlane_average_halfDifference_constraints U V hacute W i
  have hnonneg := davis_planar_short_rotation_scalar
    (Real.sqrt_nonneg _) (by
      nlinarith [principalPlaneCosine_sq_add_sine_sq U V i,
        principalPlaneSine_pos U V i]) (by
      have hσ := principalPlaneCosine_pos U V hacute i
      have hfull := principalPlaneCosine_sq_add_sine_sq U V i
      nlinarith)
    (principalPlaneSine_pos U V i).le
    (principalPlaneCosine_sq_add_sine_sq U V i)
    hconstraints.1 hconstraints.2
  have hgramTrace :
      gramTraceFinTwo A = lp + lm := by
    -- Expand `A star A`; the off-plane pieces disappear from the trace because
    -- `W` and the direct rotation carry `U,U orthogonal` onto `V,V orthogonal`.
    simp [A, principalPlaneDisplacementRestriction, gramTraceFinTwo,
      principalPlaneEmbedding, lp, lm, c, s, p, q,
      principalPlaneAverage, principalPlaneHalfDifference,
      principalPlaneCoefficient0, principalPlaneCoefficient1,
      directRotation_apply_principalSourceVector,
      directRotation_apply_principalOrthogonalVector,
      projection_intertwines_of_map_eq U V W hmap,
      principalPlaneCosine_sq_add_sine_sq]
    ring
  have hgramDet :
      gramDetFinTwo A = lp * lm := by
    simp [A, principalPlaneDisplacementRestriction, gramDetFinTwo,
      principalPlaneEmbedding, lp, lm, c, s, p, q,
      principalPlaneAverage, principalPlaneHalfDifference,
      principalPlaneCoefficient0, principalPlaneCoefficient1,
      directRotation_apply_principalSourceVector,
      directRotation_apply_principalOrthogonalVector,
      projection_intertwines_of_map_eq U V W hmap,
      principalPlaneCosine_sq_add_sine_sq]
    ring
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := by
    nlinarith [principalPlaneCosine_sq_add_sine_sq U V i,
      principalPlaneSine_pos U V i]
  have hs0 : 0 ≤ s := (principalPlaneSine_pos U V i).le
  have hpq : p ^ 2 + q ^ 2 ≤ 1 := by
    dsimp [p, q]
    nlinarith [hconstraints.1, hconstraints.2]
  have hcs : p * c + |q| * s ≤ 1 := by
    have hsq : (p * c + |q| * s) ^ 2 ≤ 1 := by
      have hcross : 2 * p * c * (|q| * s) ≤
          p ^ 2 * s ^ 2 + q ^ 2 * c ^ 2 := by
        nlinarith [sq_nonneg (p * s - |q| * c), sq_abs q]
      nlinarith [hpq, principalPlaneCosine_sq_add_sine_sq U V i, sq_abs q]
    rcases le_total (p * c + |q| * s) 0 with hneg | hpos
    · linarith
    · nlinarith
  have hlm : 0 ≤ lm := by
    dsimp [lm, davisPlanarLambdaMinus]
    nlinarith
  have hlp0 : 0 ≤ lp := by
    dsimp [lp, lm, davisPlanarLambdaPlus, davisPlanarLambdaMinus] at *
    nlinarith [abs_nonneg q]
  have hlp : lm ≤ lp := by
    dsimp [lp, lm, davisPlanarLambdaPlus, davisPlanarLambdaMinus]
    nlinarith [abs_nonneg q]
  exact singularValues_eq_pair_of_gram_trace_det_fin_two A
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt hlp) hgramTrace hgramDet

/-- Local operator and nuclear Ky Fan bounds on every principal plane. -/
theorem principalPlane_shortRotation_local_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hhalf : ∀ j : Fin (finrank ℝ E),
      (1 / 2 : ℝ) ≤ (canonicalIntertwiner U V).singularValues (j : ℕ))
    (W : E ≃ₗᵢ[ℝ] E) (hmap : U.map W.toLinearMap = V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneChord U V i ≤
        kyFanSum 1
          (principalPlaneDisplacementRestriction U V hacute W.toLinearMap i) ∧
      2 * principalPlaneChord U V i ≤
        kyFanSum 2
          (principalPlaneDisplacementRestriction U V hacute W.toLinearMap i) := by
  have hconstraints := principalPlane_average_halfDifference_constraints U V hacute W i
  have hcHalf : 1 / 2 ≤ principalPlaneCosine U V i := by
    obtain ⟨j, hj⟩ :=
      exists_canonicalIntertwiner_singularValue_eq_principalPlaneCosine
        U V hacute i
    simpa [hj] using hhalf j
  have hscalar := davis_planar_short_rotation_scalar
    (Real.sqrt_nonneg _)
    (by nlinarith [principalPlaneCosine_sq_add_sine_sq U V i,
      principalPlaneSine_pos U V i]) hcHalf
    (principalPlaneSine_pos U V i).le
    (principalPlaneCosine_sq_add_sine_sq U V i)
    hconstraints.1 hconstraints.2
  rw [singularValues_principalPlaneDisplacementRestriction_real
    U V hacute W hmap i]
  constructor
  · simpa [kyFanSum, principalPlaneChord,
      pairSingularValues] using hscalar.1
  · simpa [kyFanSum, principalPlaneChord,
      pairSingularValues] using hscalar.2


/-- Different principal-plane embeddings have orthogonal ranges. -/
theorem principalPlaneEmbedding_inner_eq_zero
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    {i j : Fin (nontrivialAngleCount U V)} (hij : i ≠ j)
    (x y : EuclideanSpace 𝕜 (Fin 2)) :
    ⟪principalPlaneEmbedding U V hacute i x,
      principalPlaneEmbedding U V hacute j y⟫_𝕜 = 0 := by
  simp [principalPlaneEmbedding, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V),
    orthonormal_iff_ite.mp (orthonormal_principalOrthogonalVector U V hacute),
    Submodule.inner_right_of_mem_orthogonal
      (principalSourceVector_mem U V hacute i)
      (principalOrthogonalVector_mem U V hacute j),
    Submodule.inner_right_of_mem_orthogonal
      (principalSourceVector_mem U V hacute j)
      (principalOrthogonalVector_mem U V hacute i), hij]

/-- Simultaneous Ky Fan lower bound for compressions to mutually orthogonal
finite-dimensional ranges.  This is the finite variational statement used in
Davis--Kahan equations (4.3)--(4.4). -/
theorem sum_kyFanSum_compression_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → EuclideanSpace 𝕜 (Fin 2) →ₗᵢ[𝕜] E)
    (horth : ∀ {i j : ι}, i ≠ j → ∀ x y, ⟪J i x, J j y⟫_𝕜 = 0)
    (A : E →ₗ[𝕜] E) (r : ι → ℕ)
    (hr : ∀ i, r i ≤ 2)
    (hcard : (∑ i, r i) ≤ finrank 𝕜 E) :
    (∑ i, kyFanSum (r i) (compression A (J i))) ≤
      kyFanSum (∑ i, r i) A := by
  classical
  choose u v hu hv heq using fun i =>
    exists_orthonormal_re_sum_inner_map_eq (compression A (J i))
      (by simpa [finrank_euclideanSpace_fin] using hr i)
  let σ := Σ i : ι, Fin (r i)
  let e : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
  let u' : Fin (Fintype.card σ) → E := fun a =>
    J (e a).1 (u (e a).1 (e a).2)
  let v' : Fin (Fintype.card σ) → E := fun a =>
    J (e a).1 (v (e a).1 (e a).2)
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite]
    intro a b
    by_cases hab : (e a).1 = (e b).1
    · subst hab
      rw [(J (e b).1).inner_map_map]
      simpa [u'] using orthonormal_iff_ite.mp (hu (e b).1) (e a).2 (e b).2
    · simpa [u', hab] using horth hab (u (e a).1 (e a).2) (u (e b).1 (e b).2)
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite]
    intro a b
    by_cases hab : (e a).1 = (e b).1
    · subst hab
      rw [(J (e b).1).inner_map_map]
      simpa [v'] using orthonormal_iff_ite.mp (hv (e b).1) (e a).2 (e b).2
    · simpa [v', hab] using horth hab (v (e a).1 (e a).2) (v (e b).1 (e b).2)
  have hcardσ : Fintype.card σ = ∑ i, r i := by
    simp [σ, Fintype.card_sigma]
  have hvar := re_sum_inner_map_le_sum_singularValues
    (A := A) (k := Fintype.card σ) (hcardσ.symm ▸ hcard) hu' hv'
  rw [← kyFanSum_eq_sum_fin, hcardσ] at hvar
  calc
    ∑ i, kyFanSum (r i) (compression A (J i))
        = RCLike.re (∑ a : Fin (Fintype.card σ),
            ⟪u' a, A (v' a)⟫_𝕜) := by
          rw [e.sum_comp]
          simp only [u', v', compression, LinearMap.comp_apply,
            LinearIsometry.adjoint_inner_left]
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl fun i _ => by
            simpa [kyFanSum_eq_sum_fin] using (heq i).symm
    _ ≤ kyFanSum (∑ i, r i) A := hvar


/-- The mutually orthogonal nontrivial principal planes fit in the ambient
space. -/
theorem twice_nontrivialAngleCount_le_finrank_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    2 * nontrivialAngleCount U V ≤ finrank 𝕜 E := by
  let f : Fin (nontrivialAngleCount U V) × Fin 2 → E := fun p =>
    if p.2 = 0 then principalSourceVector U V p.1
    else principalOrthogonalVector U V hacute p.1
  have hf : LinearIndependent 𝕜 f :=
    (orthonormal_principalPlaneFamily U V hacute).linearIndependent
  have hspan := finrank_span_eq_card hf
  have hle := Submodule.finrank_le (Submodule.span 𝕜 (Set.range f))
  rw [hspan, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hle
  simpa [mul_comm] using hle

/-- Dimension bound for a selection of complete principal planes. -/
theorem selected_principal_plane_even_dimension_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (k : ℕ) :
    2 * min (k / 2) (nontrivialAngleCount U V) ≤ finrank 𝕜 E := by
  exact (Nat.mul_le_mul_left 2 (min_le_right _ _)).trans
    (twice_nontrivialAngleCount_le_finrank_of_acute U V hacute)

/-- Dimension bound when the next single principal direction is appended. -/
theorem selected_principal_plane_dimension_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (k : ℕ)
    (hodd : k % 2 = 1 ∧ k / 2 < nontrivialAngleCount U V) :
    2 * min (k / 2) (nontrivialAngleCount U V) + 1 ≤ finrank 𝕜 E := by
  rw [min_eq_left hodd.2.le]
  have hplanes := twice_nontrivialAngleCount_le_finrank_of_acute U V hacute
  omega

/-- Elementary pairing identity for a sequence whose entries occur twice. -/
theorem sum_repeated_pair_prefix
    (d : Fin m → ℝ) (k : ℕ) :
    (∑ n : Fin k, if hn : (n : ℕ) < 2 * m then
        d ⟨(n : ℕ) / 2,
          (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [two_mul] using hn)⟩
      else 0) =
      (∑ i : Fin (min (k / 2) m), 2 * d (Fin.castLE (min_le_right _ _) i)) +
        if hodd : k % 2 = 1 ∧ k / 2 < m then d ⟨k / 2, hodd.2⟩ else 0 := by
  classical
  rw [Fin.sum_univ_eq_sum_range]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hkm : k < 2 * m
      · simp only [dif_pos hkm]
        rcases Nat.even_or_odd k with heven | hodd
        · obtain ⟨q, rfl⟩ := heven
          simp [Nat.add_mod, Nat.mul_div_cancel_left, min_eq_left,
            Nat.lt_of_succ_le (Nat.succ_le_iff.mp hkm)]
          ring
        · obtain ⟨q, rfl⟩ := hodd
          simp [Nat.add_mod, Nat.mul_add_div, min_eq_left,
            Nat.lt_of_succ_le (Nat.succ_le_iff.mp hkm)]
          ring
      · have hkm' : 2 * m ≤ k := Nat.le_of_not_gt hkm
        simp [dif_neg hkm, min_eq_right, hkm']

/-- The singular values of the direct displacement are the principal chord
lengths, each repeated twice, followed by zeros. -/
theorem singularValues_directRotation_displacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (n : ℕ) :
    (LinearMap.id - (directRotation U V hacute).toLinearMap).singularValues n =
      if hn : n < 2 * nontrivialAngleCount U V then
        principalPlaneChord U V
          ⟨n / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [two_mul] using hn)⟩
      else 0 := by
  classical
  let A := LinearMap.id - (directRotation U V hacute).toLinearMap
  let f : Fin (nontrivialAngleCount U V) × Fin 2 → E := fun p =>
    if p.2 = 0 then principalSourceVector U V p.1
    else principalOrthogonalVector U V hacute p.1
  have hf : Orthonormal 𝕜 f := orthonormal_principalPlaneFamily U V hacute
  let P := Submodule.span 𝕜 (Set.range f)
  have hreduce : ∀ p, A (f p) =
      ((principalPlaneChord U V p.1 : ℝ) : 𝕜) •
        ((polarUnitary (compression A (principalPlaneEmbedding U V hacute p.1)))
          (EuclideanSpace.basisFun (Fin 2) 𝕜 p.2)) := by
    intro p
    -- On each principal plane `A` is the normal block
    -- `[[1-c,s],[-s,1-c]]`; its modulus is the scalar chord.
    have hblock := compression_directRotation_displacement_eq U V hacute p.1
    have hpolar := polar_decomposition_unitary
      (compression A (principalPlaneEmbedding U V hacute p.1))
    fin_cases p.2 <;>
      simpa [A, f, hblock, principalPlaneEmbedding,
        LinearMap.comp_apply, Matrix.toEuclideanLin_apply,
        principalPlaneChord] using
        congrArg (fun T => T (EuclideanSpace.basisFun (Fin 2) 𝕜 p.2)) hpolar
  have hzero : ∀ x ∈ Pᗮ, A x = 0 := by
    intro x hx
    have hkerSine : sinThetaMap U V x = 0 := by
      apply (rightSingularBasis (sinThetaMap U V)).ext
      intro j
      by_cases hj : j < nontrivialAngleCount U V
      · let i : Fin (nontrivialAngleCount U V) := ⟨j, hj⟩
        have hxu : ⟪principalSourceVector U V i, x⟫_𝕜 = 0 := by
          exact hx (Submodule.subset_span ⟨(i, 0), rfl⟩)
        simpa [principalSourceVector, i] using hxu
      · rw [(sinThetaMap U V).singularValues_of_finrank_range_le
          (by simpa [nontrivialAngleCount] using hj)]
        simp
    have hproj : projection U x = projection V x := by
      have := congrArg (projection V) hkerSine
      simp [sinThetaMap, complementaryProjection, LinearMap.comp_apply] at this
      exact projection_eq_of_complementaryProjection_eq_zero this
    have hS : canonicalIntertwiner U V x = x := by
      simp [canonicalIntertwiner, LinearMap.comp_apply, hproj,
        complementaryProjection]
    have hpolar := polar_decomposition_of_isUnit
      (canonicalIntertwiner_isUnit_of_acute U V hacute)
    have hCx : ForMathlib.abs (canonicalIntertwiner U V) x = x := by
      apply (isPositive_abs (canonicalIntertwiner U V)).sqrt_eq_self_of_sq_eq_self
      simpa [canonicalIntertwiner_adjoint_comp_self, hproj,
        complementaryProjection]
    have := LinearMap.congr_fun hpolar x
    simpa [A, hS, hCx, LinearMap.comp_apply] using this.symm
  -- Extend the orthonormal principal-plane family to an orthonormal basis.
  obtain ⟨b, hb⟩ := hf.exists_orthonormalBasis_extension
  let G := A.adjoint ∘ₗ A
  have hdiag : ∀ j : Fin (finrank 𝕜 E), G (b j) =
      (((if h : (j : ℕ) < 2 * nontrivialAngleCount U V then
          principalPlaneChord U V
            ⟨(j : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2
              (by simpa [two_mul] using h)⟩ ^ 2 else 0 : ℝ)) : 𝕜) • b j := by
    intro j
    by_cases hj : (j : ℕ) < 2 * nontrivialAngleCount U V
    · obtain ⟨p, hp⟩ := hb.of_lt_card_range hj
      subst hp
      have hσ := singularValues_compression_directRotation_displacement
        U V hacute p.1
      have hnorm := congrFun hσ p.2
      simpa [G, A, f, LinearMap.comp_apply, hreduce, hnorm]
    · have hbperp : b j ∈ Pᗮ := hb.mem_orthogonal_of_not_mem_range hj
      rw [hzero (b j) hbperp]
      simp [G, LinearMap.comp_apply]
  have hanti : Antitone (fun j : Fin (finrank 𝕜 E) =>
      if h : (j : ℕ) < 2 * nontrivialAngleCount U V then
        principalPlaneChord U V
          ⟨(j : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2
            (by simpa [two_mul] using h)⟩ ^ 2 else 0) := by
    intro i j hij
    simp only
    split_ifs with hi hj
    · exact sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (principalPlaneChord_antitone U V (Nat.div_le_div_right hij))
    · positivity
    · omega
    · exact le_rfl
  have heig := eigenvalues_eq_of_eigenbasis A.isSymmetric_adjoint_comp_self
    rfl b hanti hdiag
  rcases lt_or_ge n (finrank 𝕜 E) with hnE | hnE
  · rw [A.singularValues_of_lt rfl hnE, congrFun heig ⟨n, hnE⟩]
    split_ifs with hn
    · exact Real.sqrt_sq (Real.sqrt_nonneg _)
    · simp
  · rw [A.singularValues_of_finrank_le hnE]
    simp [show ¬ n < 2 * nontrivialAngleCount U V by
      intro h; exact hnE.not_lt (lt_of_lt_of_le h (by
        simpa [nontrivialAngleCount] using
          twice_finrank_range_le_finrank_of_acute U V hacute))]

/-- Closed Ky Fan formula for the direct displacement. -/
theorem kyFanSum_directRotation_displacement_eq_principalChords
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (k : ℕ) :
    kyFanSum k (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (∑ i : Fin (min (k / 2) (nontrivialAngleCount U V)),
        2 * principalPlaneChord U V
          (Fin.castLE (min_le_right _ _) i)) +
      if hodd : k % 2 = 1 ∧ k / 2 < nontrivialAngleCount U V then
        principalPlaneChord U V ⟨k / 2, hodd.2⟩ else 0 := by
  rw [kyFanSum_eq_sum_fin]
  simp_rw [singularValues_directRotation_displacement U V hacute]
  -- Pair the terms `2i,2i+1`; a final odd term remains exactly when stated.
  exact sum_repeated_pair_prefix
    (fun i => principalPlaneChord U V i) k

/-- Equations (4.3)--(4.4): the selected principal-plane compressions of a
competitor are bounded by the corresponding global Ky Fan prefix. -/
theorem kyFanSum_ge_sum_principalPlane_restrictions
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    (∑ i : Fin (min (k / 2) (nontrivialAngleCount U V)), kyFanSum 2
      (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
        (Fin.castLE (min_le_right _ _) i))) +
      (if hodd : k % 2 = 1 ∧ k / 2 < nontrivialAngleCount U V then
        kyFanSum 1 (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
          ⟨k / 2, hodd.2⟩) else 0) ≤
      kyFanSum k (LinearMap.id - W.toLinearMap) := by
  classical
  let q := min (k / 2) (nontrivialAngleCount U V)
  let A := LinearMap.id - W.toLinearMap
  by_cases hodd : k % 2 = 1 ∧ k / 2 < nontrivialAngleCount U V
  · let ι := Fin q ⊕ Fin 1
    let J : ι → EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E := fun z =>
      Sum.elim (fun i => principalPlaneEmbedding U V hacute
        (Fin.castLE (min_le_right _ _) i))
        (fun _ => principalPlaneEmbedding U V hacute ⟨k / 2, hodd.2⟩) z
    let r : ι → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
    have horth : ∀ {i j : ι}, i ≠ j → ∀ x y, ⟪J i x, J j y⟫_ℝ = 0 := by
      intro i j hij x y
      cases i <;> cases j
      · exact principalPlaneEmbedding_inner_eq_zero U V hacute
          (by simpa using hij) x y
      · exact principalPlaneEmbedding_inner_eq_zero U V hacute
          (by simp [q, hodd]) x y
      · rw [inner_conj_symm]
        simpa using congrArg star
          (principalPlaneEmbedding_inner_eq_zero U V hacute
            (by simp [q, hodd]) y x)
      · simp at hij
    have hcard : (∑ i : ι, r i) ≤ finrank ℝ E := by
      simp [ι, r, q]
      exact selected_principal_plane_dimension_le U V hacute k hodd
    have h := sum_kyFanSum_compression_le J horth A r
      (by intro i; cases i <;> simp [r]) hcard
    simpa [A, J, r, ι, q, hodd, principalPlaneDisplacementRestriction] using h
  · let ι := Fin q
    let J : ι → EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E := fun i =>
      principalPlaneEmbedding U V hacute (Fin.castLE (min_le_right _ _) i)
    have horth : ∀ {i j : ι}, i ≠ j → ∀ x y, ⟪J i x, J j y⟫_ℝ = 0 := by
      intro i j hij
      exact principalPlaneEmbedding_inner_eq_zero U V hacute
        (Fin.castLE_injective (min_le_right _ _) hij)
    have hcard : 2 * q ≤ finrank ℝ E := by
      exact selected_principal_plane_even_dimension_le U V hacute k
    have h := sum_kyFanSum_compression_le J horth A (fun _ => 2)
      (by simp) (by simpa [q, mul_comm] using hcard)
    simpa [A, J, q, hodd, principalPlaneDisplacementRestriction] using h

/-- Davis's finite Ky Fan reassembly lemma.  It combines the restrictions to
successive mutually orthogonal principal planes.  Even prefixes use complete
planes; odd prefixes use complete planes plus the largest singular direction
of the next restriction. -/
theorem principalPlane_kyFan_reassembly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[ℝ] E)
    (hmap : U.map W.toLinearMap = V)
    (hop : ∀ i : Fin (nontrivialAngleCount U V),
      principalPlaneChord U V i ≤ kyFanSum 1
        (principalPlaneDisplacementRestriction U V hacute W.toLinearMap i))
    (hnuc : ∀ i : Fin (nontrivialAngleCount U V),
      2 * principalPlaneChord U V i ≤ kyFanSum 2
        (principalPlaneDisplacementRestriction U V hacute W.toLinearMap i))
    (k : ℕ) :
    kyFanSum k (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      kyFanSum k (LinearMap.id - W.toLinearMap) := by
  classical
  let m := nontrivialAngleCount U V
  let q := min (k / 2) m
  let odd := k % 2
  have hdirect :
      kyFanSum k (LinearMap.id - (directRotation U V hacute).toLinearMap) =
        (∑ i : Fin q, 2 * principalPlaneChord U V (Fin.castLE (min_le_right _ _) i)) +
          if hodd : odd = 1 ∧ q < m then
            principalPlaneChord U V ⟨q, hodd.2⟩ else 0 := by
    exact kyFanSum_directRotation_displacement_eq_principalChords
      U V hacute k
  have hcompetitor :
      (∑ i : Fin q, kyFanSum 2
        (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
          (Fin.castLE (min_le_right _ _) i))) +
        (if hodd : odd = 1 ∧ q < m then
          kyFanSum 1
            (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
              ⟨q, hodd.2⟩) else 0) ≤
        kyFanSum k (LinearMap.id - W.toLinearMap) := by
    -- This is equations (1.12)--(1.13) with the right test projector equal to
    -- the sum of the first principal-plane projectors.  Choose singular pairs
    -- for every two-dimensional restriction and interleave them through
    -- `finTwoBlockEquiv`; the lifted right vectors lie in mutually orthogonal
    -- planes.  For an odd prefix append the top singular pair of the next
    -- restriction.  The left family is orthonormalized inside the corresponding
    -- range test space, exactly as in the finite Ky Fan variational principle.
    exact kyFanSum_ge_sum_principalPlane_restrictions
      U V hacute W hmap k
  rw [hdirect]
  calc
    (∑ i : Fin q, 2 * principalPlaneChord U V (Fin.castLE (min_le_right _ _) i)) +
          (if hodd : odd = 1 ∧ q < m then
            principalPlaneChord U V ⟨q, hodd.2⟩ else 0)
        ≤ (∑ i : Fin q, kyFanSum 2
            (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
              (Fin.castLE (min_le_right _ _) i))) +
          (if hodd : odd = 1 ∧ q < m then
            kyFanSum 1
              (principalPlaneDisplacementRestriction U V hacute W.toLinearMap
                ⟨q, hodd.2⟩) else 0) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ => hnuc _
      · split_ifs with hodd
        · exact hop _
        · exact le_rfl
    _ ≤ kyFanSum k (LinearMap.id - W.toLinearMap) := hcompetitor

/-- Full real short-rotation Ky Fan theorem from the local scalar inequality. -/
theorem principalPlane_shortRotation_kyFan
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hhalf : ∀ i : Fin (finrank ℝ E),
      (1 / 2 : ℝ) ≤ (canonicalIntertwiner U V).singularValues (i : ℕ))
    (W : E ≃ₗᵢ[ℝ] E) (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    kyFanSum k (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      kyFanSum k (LinearMap.id - W.toLinearMap) := by
  apply principalPlane_kyFan_reassembly U V hacute W hmap
  · intro i
    exact (principalPlane_shortRotation_local_bounds U V hacute hhalf W hmap i).1
  · intro i
    exact (principalPlane_shortRotation_local_bounds U V hacute hhalf W hmap i).2
  · exact k

end DavisKahanTheory
end ForMathlib
