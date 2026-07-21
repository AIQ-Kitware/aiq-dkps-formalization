/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Fable 5
-/
import DavisKahan.FiniteDimensional.DirectRotation.Basic
import ForMathlib.Analysis.InnerProductSpace.SingularSystem
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.KyFan
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

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
`d_i = sqrt (2(1-c_i))`.

## The sound Section 4 package

* `singularValues_directRotation_displacement`: the singular values of `I - R`
  are the principal chords, each occurring twice
  (`sigma_k (I-R) = 2 sin (theta_{k/2} / 2)`).
* `kyFanSum_directRotation_displacement_eq_principalChords`: closed Ky Fan
  formula for `I - R`.
* `principalPlaneChord_le_singularValues_restrictedDisplacement` (Davis 1958
  Theorem 7.2 / Davis--Kahan Proposition 4.1): for every unitary `W` carrying
  `U` onto `V`, the `k`-th singular value of the restricted displacement
  `(I - W) P_U` is at least the `k`-th principal chord.  Combined with the
  closed form `singularValues_restrictedDisplacement_directRotation`, the
  direct rotation minimizes every singular value of the restricted
  displacement pointwise — with no angle restriction and over any `RCLike`
  field.
* `kyFanSum_restrictedDisplacement_le` and
  `uiNorm_restrictedDisplacement_le` (Davis--Kahan Corollary 4.1): Ky Fan and
  unitarily-invariant-norm minimality of the restricted displacement.

## What is deliberately absent

The historical candidate for Proposition 4.4 — "if the largest principal angle
is at most `pi/3`, the direct rotation minimizes every UI norm of the full
displacement `I - W` over real scalars" — is **false**: rotating by `2 theta`
in a single plane spanned across two equal principal angles `theta` carries
`U` onto `V` with a strictly smaller trace norm than the direct rotation, for
every `theta` in `(0, pi/2)`.  See
`DavisKahan.FiniteDimensional.DirectRotation.ShortRotationCounterexample`.
The per-plane compression route sketched in the source-derived draft is
likewise unsound: a competitor may leak mass out of a principal plane, so the
compression of `I - W` to a principal plane need not dominate the chord.  Only
the restricted-displacement statements above survive, and they need no angle
hypothesis at all.
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
  (((principalPlaneSine U V i)⁻¹ : ℝ) : 𝕜) •
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
  refine singularValues_le_one_of_contraction ?_ rfl (nontrivialAngleIndex U V i)
  intro x
  have h1 : ‖sinThetaMap U V x‖ ≤ ‖projection U x‖ :=
    Vᗮ.norm_starProjection_apply_le (projection U x)
  exact h1.trans (U.norm_starProjection_apply_le x)

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
  have hUidem : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hcVidem : ∀ y : E, complementaryProjection V (complementaryProjection V y)
      = complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hcV : ∀ y : E, complementaryProjection V y = y - projection V y := fun y =>
    Submodule.starProjection_orthogonal_val y
  have hgram : A.adjoint ∘ₗ A =
      projection U - projection U ∘ₗ projection V ∘ₗ projection U := by
    have hAadj : A.adjoint = projection U ∘ₗ complementaryProjection V := by
      show (complementaryProjection V ∘ₗ projection U).adjoint
          = projection U ∘ₗ complementaryProjection V
      rw [LinearMap.adjoint_comp, projection_adjoint]
      congr 1
      simpa [complementaryProjection] using projection_adjoint (𝕜 := 𝕜) Vᗮ
    rw [hAadj]
    show (projection U ∘ₗ complementaryProjection V) ∘ₗ
        (complementaryProjection V ∘ₗ projection U) =
        projection U - projection U ∘ₗ projection V ∘ₗ projection U
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [hcVidem (projection U x), hcV (projection U x), map_sub, hUidem x]
  rw [hgram] at heig
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at heig
  have hproj : projection U (principalSourceVector U V i) =
      principalSourceVector U V i := by
    have hc : ((s ^ 2 : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 hs)
    have key := congrArg (projection U) heig
    simp only [map_sub, map_smul, hUidem] at key
    rw [heig] at key
    exact (smul_right_injective E hc key).symm
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

/-- Principal cosines are at most one. -/
theorem principalPlaneCosine_le_one
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneCosine U V i ≤ 1 := by
  nlinarith [principalPlaneCosine_sq_add_sine_sq U V i,
    principalPlaneSine_pos U V i, Real.sqrt_nonneg (1 - principalPlaneSine U V i ^ 2),
    principalPlaneCosine, sq_nonneg (principalPlaneCosine U V i - 1),
    sq_nonneg (principalPlaneCosine U V i + 1)]

/-- Acuteness makes every principal-plane cosine strictly positive. -/
theorem principalPlaneCosine_pos
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    0 < principalPlaneCosine U V i := by
  rw [principalPlaneCosine, Real.sqrt_pos]
  have hu := principalSourceVector_mem U V hacute i
  have hnot : principalPlaneSine U V i ≠ 1 := by
    intro hs
    let u := principalSourceVector U V i
    have hu1 : ‖u‖ = 1 := (orthonormal_principalSourceVector U V).norm_eq_one i
    have hnorm := norm_apply_rightSingularBasis
      (sinThetaMap U V) (nontrivialAngleIndex U V i)
    have hzero : projection V u = 0 := by
      have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection u V
      have hsinNorm : ‖Vᗮ.starProjection u‖ = 1 := by
        have h : ‖sinThetaMap U V u‖ = principalPlaneSine U V i := hnorm
        rw [hs] at h
        rwa [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hu] at h
      rw [hu1, hsinNorm] at hdecomp
      have hVsq : ‖V.starProjection u‖ ^ 2 = 0 := by nlinarith
      show V.starProjection u = 0
      exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hVsq)
    exact (by
      have := hacute.1 u hu hzero
      exact one_ne_zero (hu1.symm.trans (by rw [this, norm_zero])))
  have hlt : principalPlaneSine U V i < 1 :=
    lt_of_le_of_ne (principalPlaneSine_le_one U V i) hnot
  nlinarith [principalPlaneSine_pos U V i, hlt]

/-- The positive modulus of the canonical intertwiner acts by the principal
cosine on the source vector. -/
theorem abs_canonicalIntertwiner_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    ForMathlib.abs (canonicalIntertwiner U V) (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
  have hu := principalSourceVector_mem U V hacute i
  have heig := adjointCompSelf_apply_rightSingularBasis (sinThetaMap U V)
    (nontrivialAngleIndex U V i)
  have hProjUu : projection U (principalSourceVector U V i) =
      principalSourceVector U V i := Submodule.starProjection_eq_self_iff.mpr hu
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hUidem : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hcVidem : ∀ y : E, complementaryProjection V (complementaryProjection V y)
      = complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hcV : ∀ y : E, complementaryProjection V y = y - projection V y := fun y =>
    Submodule.starProjection_orthogonal_val y
  have hAgram : (sinThetaMap U V).adjoint ∘ₗ sinThetaMap U V =
      projection U - projection U ∘ₗ projection V ∘ₗ projection U := by
    have hAadj : (sinThetaMap U V).adjoint = projection U ∘ₗ complementaryProjection V := by
      rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint]
      congr 1
      simpa [complementaryProjection] using projection_adjoint (𝕜 := 𝕜) Vᗮ
    rw [hAadj, sinThetaMap]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [hcVidem (projection U x), hcV (projection U x), map_sub, hUidem x]
  have hSu : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
        (principalSourceVector U V i) =
      projection U (projection V (principalSourceVector U V i)) := by
    rw [canonicalIntertwiner_adjoint_comp_self]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hProjUu, hcompUu,
      map_zero, add_zero]
  have hAu : ((sinThetaMap U V).adjoint ∘ₗ sinThetaMap U V)
        (principalSourceVector U V i) =
      principalSourceVector U V i -
        projection U (projection V (principalSourceVector U V i)) := by
    rw [hAgram]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hProjUu]
  rw [show rightSingularBasis (sinThetaMap U V) (nontrivialAngleIndex U V i) =
    principalSourceVector U V i from rfl, hAu] at heig
  have hc0 : (0 : ℝ) ≤ principalPlaneCosine U V i := Real.sqrt_nonneg _
  have hsq : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
        (principalSourceVector U V i) =
      ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
    rw [hSu]
    have hcossq : (principalPlaneCosine U V i ^ 2 : ℝ) =
        1 - (sinThetaMap U V).singularValues (nontrivialAngleIndex U V i : ℕ) ^ 2 := by
      have hp := principalPlaneCosine_sq_add_sine_sq U V i
      simp only [principalPlaneSine] at hp
      linarith
    rw [hcossq, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul, ← heig]
    abel
  have hpos := LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V)
  have hfc := FiniteDimensional.selfAdjointFunctionalCalculus_apply_of_apply_eq_smul
    hpos.isSymmetric Real.sqrt hsq
  rw [FiniteDimensional.selfAdjointFunctionalCalculus_sqrt hpos,
    Real.sqrt_sq hc0] at hfc
  exact hfc

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
  have hu1 : ‖principalSourceVector U V i‖ = 1 :=
    (orthonormal_principalSourceVector U V).norm_eq_one i
  have heigAbs := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hev : Module.End.HasEigenvalue (ForMathlib.abs (canonicalIntertwiner U V))
      ((principalPlaneCosine U V i : ℝ) : 𝕜) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := principalSourceVector U V i)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; exact heigAbs
    · exact fun h => by simp [h] at hu1
  obtain ⟨j, hj⟩ :=
    (isPositive_abs (canonicalIntertwiner U V)).isSymmetric.exists_eigenvalues_eq rfl hev
  refine ⟨j, ?_⟩
  have hj' : (isPositive_abs (canonicalIntertwiner U V)).isSymmetric.eigenvalues rfl j
      = principalPlaneCosine U V i := by exact_mod_cast hj
  rw [← congrFun (eigenvalues_abs (canonicalIntertwiner U V)) j]
  exact hj'

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
  rw [principalOrthogonalVector, smul_smul, ← RCLike.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt (principalPlaneSine_pos U V i)),
    RCLike.ofReal_one, one_smul]
  abel

/-- The orthogonal partner belongs to `U orthogonal`. -/
theorem principalOrthogonalVector_mem
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalOrthogonalVector U V hacute i ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal']
  intro x hx
  have hu := principalSourceVector_mem U V hacute i
  have hcpos := principalPlaneCosine_pos U V hacute i
  have hcne : (principalPlaneCosine U V i : 𝕜) ≠ 0 := by exact_mod_cast ne_of_gt hcpos
  have hC := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hSpsv : canonicalIntertwiner U V (principalSourceVector U V i) =
      projection V (principalSourceVector U V i) := by
    simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
      projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
  have hprojUprojV : projection U (projection V (principalSourceVector U V i)) =
      ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
    have h1 : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
          (principalSourceVector U V i) =
        projection U (projection V (principalSourceVector U V i)) := by
      rw [canonicalIntertwiner_adjoint_comp_self]
      simp only [LinearMap.add_apply, LinearMap.comp_apply,
        projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
    have h2 : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
          (principalSourceVector U V i) =
        ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
      rw [← abs_mul_self, LinearMap.comp_apply, hC, map_smul, hC, smul_smul,
        ← RCLike.ofReal_mul, ← sq]
    rw [← h1, h2]
  have hpolar : canonicalIntertwiner U V =
      (directRotation U V hacute).toLinearMap ∘ₗ
        ForMathlib.abs (canonicalIntertwiner U V) := by
    rw [directRotation_toLinearMap]; exact polar_decomposition (canonicalIntertwiner U V)
  have hWpsv : projection V (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) •
        directRotation U V hacute (principalSourceVector U V i) := by
    have h := LinearMap.congr_fun hpolar (principalSourceVector U V i)
    simp only [LinearMap.comp_apply] at h
    rw [hC, map_smul, hSpsv] at h
    exact h
  have hdiag : projection U
      (directRotation U V hacute (principalSourceVector U V i)) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
    have key := congrArg (projection U) hWpsv
    rw [map_smul, hprojUprojV] at key
    have key2 : (principalPlaneCosine U V i : 𝕜) •
          projection U (directRotation U V hacute (principalSourceVector U V i)) =
        (principalPlaneCosine U V i : 𝕜) •
          ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i) := by
      rw [← key, smul_smul, ← RCLike.ofReal_mul, ← sq]
    exact smul_right_injective E hcne key2
  rw [principalOrthogonalVector, inner_smul_left, inner_sub_left, inner_smul_left,
    RCLike.conj_ofReal, RCLike.conj_ofReal]
  have hkey : ⟪directRotation U V hacute (principalSourceVector U V i), x⟫_𝕜 =
      (principalPlaneCosine U V i : 𝕜) * ⟪principalSourceVector U V i, x⟫_𝕜 := by
    have hx' : projection U x = x := projection_apply_of_mem hx
    calc ⟪directRotation U V hacute (principalSourceVector U V i), x⟫_𝕜
        = ⟪directRotation U V hacute (principalSourceVector U V i),
            projection U x⟫_𝕜 := by rw [hx']
      _ = ⟪projection U (directRotation U V hacute (principalSourceVector U V i)),
            x⟫_𝕜 := (projection_inner_left_eq_right U _ x).symm
      _ = ⟪(principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i, x⟫_𝕜 := by
            rw [hdiag]
      _ = (principalPlaneCosine U V i : 𝕜) * ⟪principalSourceVector U V i, x⟫_𝕜 := by
            rw [inner_smul_left, RCLike.conj_ofReal]
  rw [hkey]; ring

/-- The `V`-projection of a principal source vector is the cosine multiple of
its direct-rotation image. -/
theorem projection_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    projection V (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) •
        directRotation U V hacute (principalSourceVector U V i) := by
  have hu := principalSourceVector_mem U V hacute i
  have hC := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hSpsv : canonicalIntertwiner U V (principalSourceVector U V i) =
      projection V (principalSourceVector U V i) := by
    simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
      projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
  have hpolar : canonicalIntertwiner U V =
      (directRotation U V hacute).toLinearMap ∘ₗ
        ForMathlib.abs (canonicalIntertwiner U V) := by
    rw [directRotation_toLinearMap]; exact polar_decomposition (canonicalIntertwiner U V)
  have h := LinearMap.congr_fun hpolar (principalSourceVector U V i)
  simp only [LinearMap.comp_apply] at h
  rw [hC, map_smul, hSpsv] at h
  exact h

/-- The `U`-projection of the rotated source vector. -/
theorem projection_apply_directRotation_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    projection U (directRotation U V hacute (principalSourceVector U V i)) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
  rw [directRotation_apply_principalSourceVector U V hacute i, map_add, map_smul, map_smul,
    projection_apply_of_mem (principalSourceVector_mem U V hacute i),
    projection_apply_of_mem_orthogonal (principalOrthogonalVector_mem U V hacute i),
    smul_zero, add_zero]

/-- Principal orthogonal partners are orthonormal. -/
theorem orthonormal_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (principalOrthogonalVector U V hacute) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hu := orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) i j
  have hsi : principalPlaneSine U V i ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have hsj : principalPlaneSine U V j ≠ 0 := ne_of_gt (principalPlaneSine_pos U V j)
  -- `⟪R uₐ, u_b⟫ = cₐ ⟪uₐ, u_b⟫` because the `U`-component of `R uₐ` is `cₐ uₐ`.
  have hdiag : ∀ a b : Fin (nontrivialAngleCount U V),
      ⟪directRotation U V hacute (principalSourceVector U V a),
        principalSourceVector U V b⟫_𝕜 =
      (principalPlaneCosine U V a : 𝕜) *
        ⟪principalSourceVector U V a, principalSourceVector U V b⟫_𝕜 := by
    intro a b
    calc ⟪directRotation U V hacute (principalSourceVector U V a),
          principalSourceVector U V b⟫_𝕜
        = ⟪directRotation U V hacute (principalSourceVector U V a),
            projection U (principalSourceVector U V b)⟫_𝕜 := by
          rw [projection_apply_of_mem (principalSourceVector_mem U V hacute b)]
      _ = ⟪projection U (directRotation U V hacute (principalSourceVector U V a)),
            principalSourceVector U V b⟫_𝕜 :=
          (projection_inner_left_eq_right U _ _).symm
      _ = _ := by
          rw [projection_apply_directRotation_principalSourceVector U V hacute a,
            inner_smul_left, RCLike.conj_ofReal]
  have hdiag' : ∀ a b : Fin (nontrivialAngleCount U V),
      ⟪principalSourceVector U V a,
        directRotation U V hacute (principalSourceVector U V b)⟫_𝕜 =
      (principalPlaneCosine U V b : 𝕜) *
        ⟪principalSourceVector U V a, principalSourceVector U V b⟫_𝕜 := by
    intro a b
    rw [← inner_conj_symm, hdiag b a, map_mul, RCLike.conj_ofReal, inner_conj_symm,
      ← inner_conj_symm (principalSourceVector U V b), hu]
    rw [← inner_conj_symm (principalSourceVector U V a), hu]
    split_ifs with hab
    · subst hab; simp
    · have : ¬ b = a := fun hba => hab hba.symm
      simp [this, hab]
  have hRR : ⟪directRotation U V hacute (principalSourceVector U V i),
      directRotation U V hacute (principalSourceVector U V j)⟫_𝕜 =
      ⟪principalSourceVector U V i, principalSourceVector U V j⟫_𝕜 :=
    (directRotation U V hacute).inner_map_map _ _
  rw [principalOrthogonalVector, principalOrthogonalVector, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, inner_sub_left, inner_sub_right,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.conj_ofReal, hRR, hdiag i j,
    hdiag' i j, hu]
  split_ifs with hij
  · rw [mul_one, mul_one, mul_one]
    subst hij
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
    have hpyth := principalPlaneCosine_sq_add_sine_sq U V i
    have : ((principalPlaneSine U V i)⁻¹ : ℝ) * ((principalPlaneSine U V i)⁻¹ : ℝ) *
        (1 - principalPlaneCosine U V i * principalPlaneCosine U V i -
          (principalPlaneCosine U V i * principalPlaneCosine U V i -
            principalPlaneCosine U V i * (principalPlaneCosine U V i * 1))) = 1 := by
      field_simp
      nlinarith [hpyth]
    push_cast
    rw [show ((1 : ℝ) : 𝕜) = (1 : 𝕜) from rfl] at *
    push_cast [← this]
    ring
  · simp [mul_comm]

/-- The two vectors in distinct principal planes are mutually orthogonal. -/
theorem orthonormal_principalPlaneFamily
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (fun p : Fin (nontrivialAngleCount U V) × Fin 2 =>
      if p.2 = 0 then principalSourceVector U V p.1
      else principalOrthogonalVector U V hacute p.1) := by
  rw [orthonormal_iff_ite]
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p2 <;> fin_cases q2
  · simpa [Prod.ext_iff] using
      orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) p1 q1
  · have hp := principalSourceVector_mem U V hacute p1
    have hq := principalOrthogonalVector_mem U V hacute q1
    simp [Submodule.inner_right_of_mem_orthogonal hp hq, Prod.ext_iff]
  · have hp := principalOrthogonalVector_mem U V hacute p1
    have hq := principalSourceVector_mem U V hacute q1
    rw [if_neg (by simp), if_pos rfl]
    have h0 : ⟪principalSourceVector U V q1,
        principalOrthogonalVector U V hacute p1⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hq hp
    rw [← inner_conj_symm, h0]
    simp [Prod.ext_iff]
  · simpa [Prod.ext_iff] using orthonormal_iff_ite.mp
      (orthonormal_principalOrthogonalVector U V hacute) p1 q1

/-- The inverse direct rotation acts on a source vector by the transposed
rotation block. -/
theorem directRotation_symm_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    (directRotation U V hacute).symm (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i -
        (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i := by
  have htwo := LinearMap.congr_fun (two_smul_abs_canonicalIntertwiner U V hacute)
    (principalSourceVector U V i)
  have habs := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hRu := directRotation_apply_principalSourceVector U V hacute i
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at htwo
  rw [habs, hRu] at htwo
  -- `htwo : 2 • (c • u) = (c • u + s • j) + R.symm u`
  have h2 : (directRotation U V hacute).symm (principalSourceVector U V i) =
      (2 : 𝕜) • ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i) -
        ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
          (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i) :=
    eq_sub_of_add_eq' htwo.symm
  rw [h2]
  module

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
  have hsymm := directRotation_symm_apply_principalSourceVector U V hacute i
  have happ := congrArg (directRotation U V hacute) hsymm
  rw [LinearIsometryEquiv.apply_symm_apply, map_sub, map_smul, map_smul,
    directRotation_apply_principalSourceVector U V hacute i] at happ
  -- `happ : u = c • (c • u + s • j) - s • R j`
  have hs : ((principalPlaneSine U V i : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (principalPlaneSine_pos U V i))
  apply smul_right_injective E hs
  have h2 : (principalPlaneSine U V i : 𝕜) •
      directRotation U V hacute (principalOrthogonalVector U V hacute i) =
      (principalPlaneCosine U V i : 𝕜) •
        ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
          (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i) -
        principalSourceVector U V i := by
    rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq]
    exact happ.symm
  rw [h2]
  have hpyth := principalPlaneCosine_sq_add_sine_sq U V i
  match_scalars
  · push_cast
    nlinarith [hpyth]
  · push_cast
    ring

/-- The inverse direct rotation acts on the orthogonal partner by the second
column of the transposed rotation block. -/
theorem directRotation_symm_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    (directRotation U V hacute).symm (principalOrthogonalVector U V hacute i) =
      (principalPlaneSine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneCosine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  have hRj := directRotation_apply_principalOrthogonalVector U V hacute i
  have happ := congrArg (directRotation U V hacute).symm hRj
  rw [LinearIsometryEquiv.symm_apply_apply, map_add, map_smul, map_smul,
    directRotation_symm_apply_principalSourceVector U V hacute i] at happ
  -- `happ : j = -s • (c • u - s • j) + c • R.symm j`
  have hc : ((principalPlaneCosine U V i : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (principalPlaneCosine_pos U V hacute i))
  apply smul_right_injective E hc
  have h2 : (principalPlaneCosine U V i : 𝕜) •
      (directRotation U V hacute).symm (principalOrthogonalVector U V hacute i) =
      principalOrthogonalVector U V hacute i -
        -(principalPlaneSine U V i : 𝕜) •
          ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i -
            (principalPlaneSine U V i : 𝕜) •
              principalOrthogonalVector U V hacute i) := by
    rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at happ ⊢
    exact happ.symm
  rw [h2]
  have hpyth := principalPlaneCosine_sq_add_sine_sq U V i
  match_scalars
  · push_cast
    ring
  · push_cast
    nlinarith [hpyth]

/-- The positive modulus of the canonical intertwiner acts by the principal
cosine on the orthogonal partner as well. -/
theorem abs_canonicalIntertwiner_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    ForMathlib.abs (canonicalIntertwiner U V)
        (principalOrthogonalVector U V hacute i) =
      (principalPlaneCosine U V i : 𝕜) •
        principalOrthogonalVector U V hacute i := by
  have htwo := LinearMap.congr_fun (two_smul_abs_canonicalIntertwiner U V hacute)
    (principalOrthogonalVector U V hacute i)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at htwo
  rw [directRotation_apply_principalOrthogonalVector U V hacute i,
    directRotation_symm_apply_principalOrthogonalVector U V hacute i] at htwo
  have h2 : (2 : 𝕜) • ForMathlib.abs (canonicalIntertwiner U V)
      (principalOrthogonalVector U V hacute i) =
      (2 : 𝕜) • ((principalPlaneCosine U V i : 𝕜) •
        principalOrthogonalVector U V hacute i) := by
    rw [htwo]
    module
  exact smul_right_injective E (by norm_num : (2 : 𝕜) ≠ 0) h2

/-- Principal sines decrease with the index. -/
theorem principalPlaneSine_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneSine U V) := by
  intro i j hij
  exact (sinThetaMap U V).singularValues_antitone hij

/-- Principal cosines increase with the index. -/
theorem principalPlaneCosine_monotone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Monotone (principalPlaneCosine U V) := by
  intro i j hij
  have hs : principalPlaneSine U V j ≤ principalPlaneSine U V i :=
    principalPlaneSine_antitone U V hij
  rw [principalPlaneCosine, principalPlaneCosine]
  apply Real.sqrt_le_sqrt
  nlinarith [principalPlaneSine_pos U V i, principalPlaneSine_pos U V j]

/-- Chord lengths decrease with the index. -/
theorem principalPlaneChord_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneChord U V) := by
  intro i j hij
  have hc : principalPlaneCosine U V i ≤ principalPlaneCosine U V j :=
    principalPlaneCosine_monotone U V hij
  rw [principalPlaneChord, principalPlaneChord]
  apply Real.sqrt_le_sqrt
  linarith

/-- Chord lengths are nonnegative. -/
theorem principalPlaneChord_nonneg
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    0 ≤ principalPlaneChord U V i :=
  Real.sqrt_nonneg _

/-- The squared chord is `2 (1 - cos)`. -/
theorem principalPlaneChord_sq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneChord U V i ^ 2 = 2 * (1 - principalPlaneCosine U V i) := by
  rw [principalPlaneChord, Real.sq_sqrt]
  have := principalPlaneCosine_le_one U V i
  linarith

/-! ## Vanishing directions

A vector orthogonal to every principal source vector is annihilated by the
sine map; a vector orthogonal to the whole principal-plane family lies in the
common fixed part, where the two projections agree.  These descent lemmas are
the finite two-projection structure theory needed to compute the spectrum of
`I - R`. -/

/-- The sine map vanishes on vectors orthogonal to every principal source
vector. -/
theorem sinThetaMap_apply_eq_zero_of_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    sinThetaMap U V x = 0 := by
  classical
  set b := rightSingularBasis (sinThetaMap U V) with hb
  have hxdecomp := b.sum_repr x
  calc sinThetaMap U V x
      = sinThetaMap U V (∑ j, b.repr x j • b j) := by rw [hxdecomp]
    _ = ∑ j, b.repr x j • sinThetaMap U V (b j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : (j : ℕ) < nontrivialAngleCount U V
        · have hcoeff : b.repr x j = 0 := by
            rw [b.repr_apply_apply]
            have hidx : b j = principalSourceVector U V ⟨(j : ℕ), hj⟩ := by
              rw [principalSourceVector]
              congr 1
              ext
              simp [nontrivialAngleIndex]
            rw [hidx]
            exact hx ⟨(j : ℕ), hj⟩
          rw [hcoeff, zero_smul]
        · have hσ : (sinThetaMap U V).singularValues (j : ℕ) = 0 :=
            (sinThetaMap U V).singularValues_eq_zero_iff_le_finrank_range.mpr
              (Nat.le_of_not_lt hj)
          rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
            (sinThetaMap U V) hσ, smul_zero]

/-- A vector of `U` orthogonal to every principal source vector lies in `V`. -/
theorem mem_of_mem_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hxU : x ∈ U)
    (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    x ∈ V := by
  have hsin := sinThetaMap_apply_eq_zero_of_orthogonal_sources U V hx
  rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hxU] at hsin
  have hmem : x ∈ Vᗮᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hsin
  rwa [Submodule.orthogonal_orthogonal] at hmem

/-- The positive cosine fixes every vector of `U` orthogonal to the principal
source vectors. -/
theorem abs_canonicalIntertwiner_apply_eq_self_of_orthogonal_sources
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hxU : x ∈ U)
    (hx : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0) :
    ForMathlib.abs (canonicalIntertwiner U V) x = x := by
  have hxV := mem_of_mem_orthogonal_sources U V hxU hx
  exact abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V
    (by rw [projection_apply_of_mem hxU, projection_apply_of_mem hxV])

/-- Inner products against the sine map vanish on vectors orthogonal to the
principal-plane family. -/
theorem inner_sinThetaMap_apply_eq_zero_of_orthogonal_family
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    {z : E} (hzu : ∀ i, ⟪principalSourceVector U V i, z⟫_𝕜 = 0)
    (hzj : ∀ i, ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 = 0)
    (w : E) :
    ⟪sinThetaMap U V w, z⟫_𝕜 = 0 := by
  classical
  set b := rightSingularBasis (sinThetaMap U V) with hb
  have hwdecomp := b.sum_repr w
  have hsinu : ∀ i : Fin (nontrivialAngleCount U V),
      ⟪sinThetaMap U V (principalSourceVector U V i), z⟫_𝕜 = 0 := by
    intro i
    have hu := principalSourceVector_mem U V hacute i
    have hsin : sinThetaMap U V (principalSourceVector U V i) =
        principalSourceVector U V i -
          projection V (principalSourceVector U V i) := by
      rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hu]
      exact Submodule.starProjection_orthogonal_val _
    rw [hsin, projection_apply_principalSourceVector U V hacute i,
      directRotation_apply_principalSourceVector U V hacute i, inner_sub_left,
      inner_smul_left, inner_add_left, inner_smul_left, inner_smul_left,
      hzu i, hzj i]
    ring
  calc ⟪sinThetaMap U V w, z⟫_𝕜
      = ⟪sinThetaMap U V (∑ j, b.repr w j • b j), z⟫_𝕜 := by rw [hwdecomp]
    _ = ∑ j, (starRingEnd 𝕜) (b.repr w j) * ⟪sinThetaMap U V (b j), z⟫_𝕜 := by
        rw [map_sum, sum_inner]
        exact Finset.sum_congr rfl fun j _ => by
          rw [map_smul, inner_smul_left]
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : (j : ℕ) < nontrivialAngleCount U V
        · have hidx : b j = principalSourceVector U V ⟨(j : ℕ), hj⟩ := by
            rw [principalSourceVector]
            congr 1
            ext
            simp [nontrivialAngleIndex]
          rw [hidx, hsinu ⟨(j : ℕ), hj⟩, mul_zero]
        · have hσ : (sinThetaMap U V).singularValues (j : ℕ) = 0 :=
            (sinThetaMap U V).singularValues_eq_zero_iff_le_finrank_range.mpr
              (Nat.le_of_not_lt hj)
          rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
            (sinThetaMap U V) hσ, inner_zero_left, mul_zero]

/-- **Descent to the fixed part.**  On the orthogonal complement of the
principal-plane family the two projections agree. -/
theorem projection_eq_projection_of_orthogonal_family
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    {x : E} (hxu : ∀ i, ⟪principalSourceVector U V i, x⟫_𝕜 = 0)
    (hxj : ∀ i, ⟪principalOrthogonalVector U V hacute i, x⟫_𝕜 = 0) :
    projection U x = projection V x := by
  set y := projection U x with hy
  set z := complementaryProjection U x with hz
  have hxyz : y + z = x := U.starProjection_add_starProjection_orthogonal x
  have hyU : y ∈ U := U.starProjection_apply_mem x
  have hzUperp : z ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  -- `y` is orthogonal to the source vectors.
  have hyu : ∀ i, ⟪principalSourceVector U V i, y⟫_𝕜 = 0 := by
    intro i
    have := projection_inner_left_eq_right U (principalSourceVector U V i) x
    rw [projection_apply_of_mem (principalSourceVector_mem U V hacute i)] at this
    rw [hy, ← this, hxu i]
  -- Hence `y ∈ V`.
  have hyV : y ∈ V := mem_of_mem_orthogonal_sources U V hyU hyu
  -- `z` is orthogonal to the whole family.
  have hzu : ∀ i, ⟪principalSourceVector U V i, z⟫_𝕜 = 0 := by
    intro i
    have hsplit : ⟪principalSourceVector U V i, x⟫_𝕜 =
        ⟪principalSourceVector U V i, y⟫_𝕜 +
          ⟪principalSourceVector U V i, z⟫_𝕜 := by
      rw [← inner_add_right, hxyz]
    rw [hxu i, hyu i] at hsplit
    linarith [congrArg RCLike.re hsplit, congrArg RCLike.im hsplit,
      (RCLike.ext_iff (z := ⟪principalSourceVector U V i, z⟫_𝕜) (w := 0))]
  have hzj : ∀ i, ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 = 0 := by
    intro i
    have hjy : ⟪principalOrthogonalVector U V hacute i, y⟫_𝕜 = 0 := by
      have := projection_inner_left_eq_right U
        (principalOrthogonalVector U V hacute i) x
      rw [projection_apply_of_mem_orthogonal
        (principalOrthogonalVector_mem U V hacute i), inner_zero_left] at this
      rw [hy, ← this]
    have hsplit : ⟪principalOrthogonalVector U V hacute i, x⟫_𝕜 =
        ⟪principalOrthogonalVector U V hacute i, y⟫_𝕜 +
          ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜 := by
      rw [← inner_add_right, hxyz]
    rw [hxj i, hjy] at hsplit
    linarith [congrArg RCLike.re hsplit, congrArg RCLike.im hsplit,
      (RCLike.ext_iff (z := ⟪principalOrthogonalVector U V hacute i, z⟫_𝕜) (w := 0))]
  -- The `V`-projection of `z` vanishes: it is a vector of `V` orthogonal to `U`.
  have hvzero : projection V z = 0 := by
    set v := projection V z with hv
    have hvV : v ∈ V := V.starProjection_apply_mem z
    have hvUperp : ∀ u ∈ U, ⟪u, v⟫_𝕜 = 0 := by
      intro u huU
      have h1 : ⟪u, v⟫_𝕜 = ⟪projection V u, z⟫_𝕜 := by
        rw [hv, projection_inner_left_eq_right]
      have h2 : projection V u = u - sinThetaMap U V u := by
        rw [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem huU,
          Submodule.starProjection_orthogonal_val]
        abel
      rw [h1, h2, inner_sub_left,
        Submodule.inner_right_of_mem_orthogonal huU hzUperp,
        inner_sinThetaMap_apply_eq_zero_of_orthogonal_family U V hacute hzu hzj u,
        sub_zero]
    have hvmem : v ∈ Uᗮ := by
      rw [Submodule.mem_orthogonal]
      exact hvUperp
    have hproj0 : U.starProjection v = 0 :=
      projection_apply_of_mem_orthogonal hvmem
    exact hacute.2 v hvV hproj0
  -- Conclude.
  have hyproj : projection V y = y := projection_apply_of_mem hyV
  calc projection U x = y := hy.symm
    _ = projection V y + projection V z := by rw [hyproj, hvzero, add_zero]
    _ = projection V x := by rw [← map_add, hxyz]

/-! ## The spectrum of the direct displacement -/

/-- The Gram operator of the displacement `I - R` is twice the defect of the
positive cosine: `(I-R)⋆(I-R) = 2 (I - |S|)`. -/
theorem adjoint_comp_displacement_directRotation
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (LinearMap.id - (directRotation U V hacute).toLinearMap).adjoint ∘ₗ
        (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (2 : 𝕜) • (LinearMap.id -
        ForMathlib.abs (canonicalIntertwiner U V)) := by
  have htwo := two_smul_abs_canonicalIntertwiner U V hacute
  have hadj : (directRotation U V hacute).toLinearMap.adjoint =
      (directRotation U V hacute).symm.toLinearMap :=
    (directRotation U V hacute).adjoint_toLinearMap_eq_symm
  have hcomp : (directRotation U V hacute).symm.toLinearMap ∘ₗ
      (directRotation U V hacute).toLinearMap = LinearMap.id := by
    ext x
    simp [LinearMap.comp_apply]
  rw [map_sub, LinearMap.adjoint_id, hadj]
  have hexpand : (LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
      (LinearMap.id - (directRotation U V hacute).toLinearMap) =
      (2 : 𝕜) • LinearMap.id -
        ((directRotation U V hacute).toLinearMap +
          (directRotation U V hacute).symm.toLinearMap) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.comp_id, hcomp]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    module
  rw [hexpand, ← htwo]
  ext x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_sub]

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
  omega

/-- The angle count is bounded by the ambient dimension. -/
theorem nontrivialAngleCount_le_finrank
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    nontrivialAngleCount U V ≤ finrank 𝕜 E :=
  LinearMap.finrank_range_le (sinThetaMap U V)

/-- Elementary pairing identity for a sequence whose entries occur twice. -/
theorem sum_repeated_pair_prefix {m : ℕ}
    (d : Fin m → ℝ) (k : ℕ) :
    (∑ n : Fin k, if hn : (n : ℕ) < 2 * m then
        d ⟨(n : ℕ) / 2,
          (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
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
          have hq : q < m := by omega
          have h1 : (q + q) / 2 = q := by omega
          have h2 : (q + q) % 2 = 0 := by omega
          have h3 : (q + q + 1) % 2 = 1 := by omega
          have h4 : (q + q + 1) / 2 = q := by omega
          simp only [h1, h2, h3, h4]
          rw [dif_neg (by omega), dif_pos ⟨rfl, hq⟩]
          have hmin : min ((q + q) / 2) m = q := by omega
          have hmin' : min ((q + q + 1) / 2) m = q := by omega
          rw [show ((q+q)/2) = q from h1, show ((q+q+1)/2) = q from h4]
          simp
      · have hkm' : 2 * m ≤ k := Nat.le_of_not_gt hkm
        have h1 : min (k / 2) m = m := by omega
        have h2 : min ((k+1) / 2) m = m := by omega
        rw [dif_neg (by omega)]
        have h3 : ¬ (k % 2 = 1 ∧ k / 2 < m) := by omega
        have h4 : ¬ ((k+1) % 2 = 1 ∧ (k+1) / 2 < m) := by omega
        rw [dif_neg h3, dif_neg h4, add_zero, add_zero, add_zero]
        apply Finset.sum_congr
        · congr 1
          omega
        · intro i _
          rfl

/-- **The singular values of the direct displacement** are the principal chord
lengths, each repeated twice, followed by zeros.  This is the quantitative
heart of Davis--Kahan Proposition 4.1: `sigma_k (I - R) = 2 sin(theta_{k/2}/2)`. -/
theorem singularValues_directRotation_displacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (n : ℕ) :
    (LinearMap.id - (directRotation U V hacute).toLinearMap).singularValues n =
      if hn : n < 2 * nontrivialAngleCount U V then
        principalPlaneChord U V
          ⟨n / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      else 0 := by
  classical
  set m := nontrivialAngleCount U V with hm
  set A := LinearMap.id - (directRotation U V hacute).toLinearMap with hA
  set S := canonicalIntertwiner U V with hS
  have h2m : 2 * m ≤ finrank 𝕜 E :=
    twice_nontrivialAngleCount_le_finrank_of_acute U V hacute
  -- The candidate eigenvector family on `Fin (finrank 𝕜 E)`.
  set v : Fin (finrank 𝕜 E) → E := fun k =>
    if hk : (k : ℕ) < 2 * m then
      (if (k : ℕ) % 2 = 0
        then principalSourceVector U V
          ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
        else principalOrthogonalVector U V hacute
          ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩)
    else 0 with hv
  set s : Set (Fin (finrank 𝕜 E)) := {k | (k : ℕ) < 2 * m} with hs
  -- The family restricted to `s` is orthonormal.
  have hfam := orthonormal_principalPlaneFamily U V hacute
  have hres : Orthonormal 𝕜 (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : ℕ) < 2 * m := ha
    have hb' : (b : ℕ) < 2 * m := hb
    have hva : v a = (fun p : Fin m × Fin 2 =>
        if p.2 = 0 then principalSourceVector U V p.1
        else principalOrthogonalVector U V hacute p.1)
        (⟨⟨(a : ℕ) / 2, by omega⟩, ⟨(a : ℕ) % 2, by omega⟩⟩) := by
      rw [hv]
      simp only [dif_pos ha']
      by_cases hpar : (a : ℕ) % 2 = 0
      · simp [hpar, show (⟨(a:ℕ) % 2, by omega⟩ : Fin 2) = 0 from by
          ext; simp [hpar]]
      · have : (a : ℕ) % 2 = 1 := by omega
        simp [hpar, show (⟨(a:ℕ) % 2, by omega⟩ : Fin 2) ≠ 0 from by
          intro h; apply hpar; simpa [Fin.ext_iff] using h]
    have hvb : v b = (fun p : Fin m × Fin 2 =>
        if p.2 = 0 then principalSourceVector U V p.1
        else principalOrthogonalVector U V hacute p.1)
        (⟨⟨(b : ℕ) / 2, by omega⟩, ⟨(b : ℕ) % 2, by omega⟩⟩) := by
      rw [hv]
      simp only [dif_pos hb']
      by_cases hpar : (b : ℕ) % 2 = 0
      · simp [hpar, show (⟨(b:ℕ) % 2, by omega⟩ : Fin 2) = 0 from by
          ext; simp [hpar]]
      · have : (b : ℕ) % 2 = 1 := by omega
        simp [hpar, show (⟨(b:ℕ) % 2, by omega⟩ : Fin 2) ≠ 0 from by
          intro h; apply hpar; simpa [Fin.ext_iff] using h]
    have hij := orthonormal_iff_ite.mp hfam
      ⟨⟨(a : ℕ) / 2, by omega⟩, ⟨(a : ℕ) % 2, by omega⟩⟩
      ⟨⟨(b : ℕ) / 2, by omega⟩, ⟨(b : ℕ) % 2, by omega⟩⟩
    simp only [Set.restrict_apply]
    rw [hva, hvb, hij]
    congr 1
    simp only [Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq, eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      apply Fin.ext
      omega
    · intro h
      have : (a : ℕ) = (b : ℕ) := by exact_mod_cast congrArg Fin.val h
      omega
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := v)
  -- The eigenvalue list.
  set μ : Fin (finrank 𝕜 E) → ℝ := fun k =>
    if hk : (k : ℕ) < 2 * m then
      principalPlaneChord U V
        ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩ ^ 2
    else 0 with hμ
  have hμanti : Antitone μ := by
    intro a c hac
    rw [hμ]
    simp only
    split_ifs with h1 h2 h2
    · have hchord := principalPlaneChord_antitone U V
        (show (⟨(a : ℕ)/2, _⟩ : Fin m) ≤ ⟨(c : ℕ)/2, _⟩ from by
          simp only [Fin.mk_le_mk]
          omega)
      have h0a := principalPlaneChord_nonneg U V
        ⟨(a : ℕ)/2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      have h0c := principalPlaneChord_nonneg U V
        ⟨(c : ℕ)/2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩
      nlinarith
    · positivity
    · omega
    · exact le_rfl
  -- The Gram operator is diagonal in the extended basis.
  have hgram := adjoint_comp_displacement_directRotation U V hacute
  have habs_u := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute
  have habs_j := abs_canonicalIntertwiner_apply_principalOrthogonalVector U V hacute
  have hdiag : ∀ k, (A.adjoint ∘ₗ A) (b k) = ((μ k : ℝ) : 𝕜) • b k := by
    intro k
    rw [← hA]
    by_cases hk : (k : ℕ) < 2 * m
    · have hbk : b k = v k := hb k hk
      rw [hgram, hbk, hv]
      simp only [dif_pos hk]
      by_cases hpar : (k : ℕ) % 2 = 0
      · rw [if_pos hpar]
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
          habs_u ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩]
        rw [hμ]
        simp only [dif_pos hk]
        rw [principalPlaneChord_sq]
        match_scalars
        push_cast
        ring
      · rw [if_neg hpar]
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
          habs_j ⟨(k : ℕ) / 2, (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)⟩]
        rw [hμ]
        simp only [dif_pos hk]
        rw [principalPlaneChord_sq]
        match_scalars
        push_cast
        ring
    · -- `b k` is orthogonal to the whole family, so `|S|` fixes it.
      have hperp_u : ∀ i, ⟪principalSourceVector U V i, b k⟫_𝕜 = 0 := by
        intro i
        have hpos : 2 * (i : ℕ) < 2 * m := by omega
        have hval : ((⟨2 * (i : ℕ), by omega⟩ : Fin (finrank 𝕜 E)) : ℕ) < 2 * m := hpos
        have hbu : b ⟨2 * (i : ℕ), by omega⟩ = principalSourceVector U V i := by
          rw [hb _ hval, hv]
          simp only [dif_pos hval]
          rw [if_pos (by omega)]
          congr 1
          ext
          simp
          omega
        have hne : (⟨2 * (i : ℕ), by omega⟩ : Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hpos
        rw [← hbu]
        exact b.orthonormal.inner_eq_zero hne
      have hperp_j : ∀ i, ⟪principalOrthogonalVector U V hacute i, b k⟫_𝕜 = 0 := by
        intro i
        have hpos : 2 * (i : ℕ) + 1 < 2 * m := by omega
        have hval : ((⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (finrank 𝕜 E)) : ℕ) < 2 * m := hpos
        have hbj : b ⟨2 * (i : ℕ) + 1, by omega⟩ =
            principalOrthogonalVector U V hacute i := by
          rw [hb _ hval, hv]
          simp only [dif_pos hval]
          rw [if_neg (by omega)]
          congr 1
          ext
          simp
          omega
        have hne : (⟨2 * (i : ℕ) + 1, by omega⟩ : Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hpos
        rw [← hbj]
        exact b.orthonormal.inner_eq_zero hne
      have hproj := projection_eq_projection_of_orthogonal_family U V hacute
        hperp_u hperp_j
      have habs := abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hproj
      rw [hgram]
      rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, habs,
        sub_self, smul_zero, hμ]
      simp [dif_neg hk]
  -- Identify the sorted eigenvalues.
  have heig := eigenvalues_eq_of_eigenbasis A.isSymmetric_adjoint_comp_self rfl b
    hμanti hdiag
  rcases lt_or_ge n (finrank 𝕜 E) with hnE | hnE
  · rw [A.singularValues_of_lt rfl hnE, heig]
    rw [hμ]
    simp only
    split_ifs with hn
    · exact Real.sqrt_sq (principalPlaneChord_nonneg U V _)
    · exact Real.sqrt_zero
  · rw [A.singularValues_of_finrank_le hnE]
    rw [dif_neg (by omega)]

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
  exact sum_repeated_pair_prefix (fun i => principalPlaneChord U V i) k

/-! ## Davis's variational theorem for the restricted displacement

Davis 1958, Theorem 7.2 (= Davis--Kahan 1970, Proposition 4.1): among all
unitaries `W` carrying `U` onto `V`, the direct rotation minimizes every
singular value of the restricted displacement `(I - W) P_U` — pointwise, over
any `RCLike` field, with no angle restriction.  The proof is the minimax
argument: for a unit vector `x ∈ U`, the image `W x` is a *unit* vector of
`V`, so `‖x - W x‖² ≥ 2 - 2 ‖P_V x‖`, and on the span of the top source
vectors the cosine bound `‖P_V x‖ ≤ c_j` is uniform. -/

/-- Squared norms of orthonormal combinations. -/
private theorem norm_sq_sum_smul_orthonormal
    {ι : Type*} [Fintype ι] {w : ι → E} (hw : Orthonormal 𝕜 w) (β : ι → 𝕜) :
    ‖∑ a, β a • w a‖ ^ 2 = ∑ a, ‖β a‖ ^ 2 := by
  classical
  have hinner : ⟪∑ a, β a • w a, ∑ a, β a • w a⟫_𝕜 =
      ((∑ a, ‖β a‖ ^ 2 : ℝ) : 𝕜) := by
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_left, inner_sum]
    rw [Finset.sum_eq_single a]
    · rw [inner_smul_right, orthonormal_iff_ite.mp hw a a, if_pos rfl, mul_one,
        RCLike.conj_mul]
      norm_cast
    · intro c _ hca
      rw [inner_smul_right, orthonormal_iff_ite.mp hw a c,
        if_neg (fun h => hca h.symm), mul_zero, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have := congrArg RCLike.re hinner
  rwa [← norm_sq_eq_re_inner, RCLike.ofReal_re] at this

/-- **Davis 1958 Theorem 7.2 / Davis--Kahan Proposition 4.1** (lower bound):
for every unitary `W` carrying `U` onto `V`, the `i`-th singular value of the
restricted displacement `(I - W) ∘ P_U` is at least the `i`-th principal
chord. -/
theorem principalPlaneChord_le_singularValues_restrictedDisplacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneChord U V i ≤
      ((LinearMap.id - W.toLinearMap) ∘ₗ projection U).singularValues (i : ℕ) := by
  classical
  set m := nontrivialAngleCount U V with hm
  set AW := (LinearMap.id - W.toLinearMap) ∘ₗ projection U with hAW
  have hiE : (i : ℕ) < finrank 𝕜 E :=
    lt_of_lt_of_le i.isLt (nontrivialAngleCount_le_finrank U V)
  -- The span of the top `i+1` source vectors.
  set u' : Fin ((i : ℕ) + 1) → E := fun a =>
    principalSourceVector U V (Fin.castLE (by omega) a) with hu'
  have hu'on : Orthonormal 𝕜 u' :=
    (orthonormal_principalSourceVector U V).comp _
      (Fin.castLE_injective (by omega))
  set L : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range u') with hL
  have hLdim : finrank 𝕜 L = (i : ℕ) + 1 := by
    rw [hL, finrank_span_eq_card hu'on.linearIndependent, Fintype.card_fin]
  have hLU : L ≤ U := by
    rw [hL, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact principalSourceVector_mem U V hacute _
  -- Courant–Fischer gives a unit test vector in `L`.
  obtain ⟨x, hxL, hxnorm, hxbound⟩ :=
    exists_unit_vector_re_inner_le_eigenvalue
      AW.isSymmetric_adjoint_comp_self rfl ⟨(i : ℕ), hiE⟩ L hLdim
  -- The quadratic form at `x` is the squared displacement of `x`.
  have hform : RCLike.re ⟪(AW.adjoint ∘ₗ AW) x, x⟫_𝕜 = ‖x - W x‖ ^ 2 := by
    have hxU : x ∈ U := hLU hxL
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [← norm_sq_eq_re_inner]
    congr 2
    rw [hAW, LinearMap.comp_apply, projection_apply_of_mem hxU,
      LinearMap.sub_apply, LinearMap.id_apply]
    rfl
  -- Lower bound for the displacement on `L`.
  have hdisp : principalPlaneChord U V i ^ 2 ≤ ‖x - W x‖ ^ 2 := by
    have hxU : x ∈ U := hLU hxL
    -- Coefficients of `x` in the orthonormal family.
    obtain ⟨β, hβ⟩ := (mem_span_range_iff_exists_fun 𝕜).mp hxL
    -- Norm of `x`.
    have hxnorm2 : ∑ a, ‖β a‖ ^ 2 = 1 := by
      have := norm_sq_sum_smul_orthonormal hu'on β
      rw [hβ, hxnorm] at this
      simpa using this.symm
    -- `P_V x` in the rotated orthonormal family.
    have hPV : projection V x = ∑ a,
        (β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)) •
          directRotation U V hacute (u' a) := by
      rw [← hβ, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, hu',
        projection_apply_principalSourceVector U V hacute _, smul_smul]
    have hRon : Orthonormal 𝕜 (fun a => directRotation U V hacute (u' a)) := by
      rw [orthonormal_iff_ite]
      intro a c
      rw [(directRotation U V hacute).inner_map_map]
      exact orthonormal_iff_ite.mp hu'on a c
    have hPVnorm : ‖projection V x‖ ^ 2 = ∑ a,
        ‖β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)‖ ^ 2 := by
      rw [hPV]
      exact norm_sq_sum_smul_orthonormal hRon _
    -- Uniform cosine bound on the span.
    have hcos : ‖projection V x‖ ^ 2 ≤ principalPlaneCosine U V i ^ 2 := by
      rw [hPVnorm]
      calc ∑ a, ‖β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)‖ ^ 2
          ≤ ∑ a, principalPlaneCosine U V i ^ 2 * ‖β a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, mul_pow, RCLike.norm_ofReal]
            have hmono : principalPlaneCosine U V (Fin.castLE (by omega) a) ≤
                principalPlaneCosine U V i := by
              apply principalPlaneCosine_monotone
              simp only [Fin.le_def, Fin.coe_castLE]
              omega
            have h0 : 0 ≤ principalPlaneCosine U V (Fin.castLE (by omega) a) :=
              Real.sqrt_nonneg _
            have := sq_nonneg (β a)
            calc ‖β a‖ ^ 2 * |principalPlaneCosine U V (Fin.castLE (by omega) a)| ^ 2
                = |principalPlaneCosine U V (Fin.castLE (by omega) a)| ^ 2 * ‖β a‖ ^ 2 := by
                  ring
              _ ≤ principalPlaneCosine U V i ^ 2 * ‖β a‖ ^ 2 := by
                  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                  rw [abs_of_nonneg h0]
                  exact pow_le_pow_left₀ h0 hmono 2
        _ = principalPlaneCosine U V i ^ 2 := by
            rw [← Finset.mul_sum, hxnorm2, mul_one]
    have hPVle : ‖projection V x‖ ≤ principalPlaneCosine U V i := by
      have h0 : 0 ≤ principalPlaneCosine U V i := Real.sqrt_nonneg _
      nlinarith [norm_nonneg (projection V x)]
    -- `W x` is a unit vector of `V`.
    have hWxV : W x ∈ V := by
      rw [← hmap]
      exact ⟨x, hxU, rfl⟩
    have hWxnorm : ‖W x‖ = 1 := by rw [W.norm_map, hxnorm]
    -- Expand the squared displacement.
    have hre : RCLike.re ⟪x, W x⟫_𝕜 ≤ principalPlaneCosine U V i := by
      have h1 : ⟪x, W x⟫_𝕜 = ⟪projection V x, W x⟫_𝕜 := by
        rw [projection_inner_left_eq_right, projection_apply_of_mem hWxV]
      calc RCLike.re ⟪x, W x⟫_𝕜 = RCLike.re ⟪projection V x, W x⟫_𝕜 := by rw [h1]
        _ ≤ ‖⟪projection V x, W x⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖projection V x‖ * ‖W x‖ := norm_inner_le_norm _ _
        _ = ‖projection V x‖ := by rw [hWxnorm, mul_one]
        _ ≤ principalPlaneCosine U V i := hPVle
    have hexpand : ‖x - W x‖ ^ 2 = 2 - 2 * RCLike.re ⟪x, W x⟫_𝕜 := by
      rw [@norm_sub_sq 𝕜, hxnorm, hWxnorm]
      norm_num
      ring
    rw [hexpand, principalPlaneChord_sq]
    linarith
  -- Assemble.
  have hσ := AW.singularValues_of_lt rfl hiE
  rw [hσ]
  have hbound : principalPlaneChord U V i ^ 2 ≤
      AW.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨(i : ℕ), hiE⟩ := by
    calc principalPlaneChord U V i ^ 2 ≤ ‖x - W x‖ ^ 2 := hdisp
      _ = RCLike.re ⟪(AW.adjoint ∘ₗ AW) x, x⟫_𝕜 := hform.symm
      _ ≤ _ := hxbound
  calc principalPlaneChord U V i
      = Real.sqrt (principalPlaneChord U V i ^ 2) :=
        (Real.sqrt_sq (principalPlaneChord_nonneg U V i)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hbound

/-- Closed form for the singular values of the restricted direct displacement:
the principal chords, then zeros. -/
theorem singularValues_restrictedDisplacement_directRotation
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (n : ℕ) :
    ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U).singularValues n =
      if hn : n < nontrivialAngleCount U V then
        principalPlaneChord U V ⟨n, hn⟩ else 0 := by
  classical
  set m := nontrivialAngleCount U V with hm
  set AR := (LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
    projection U with hAR
  have hmE : m ≤ finrank 𝕜 E := nontrivialAngleCount_le_finrank U V
  -- Eigenvector family: the source vectors, then an orthonormal completion.
  set v : Fin (finrank 𝕜 E) → E := fun k =>
    if hk : (k : ℕ) < m then principalSourceVector U V ⟨(k : ℕ), hk⟩ else 0
    with hv
  set s : Set (Fin (finrank 𝕜 E)) := {k | (k : ℕ) < m} with hs
  have hres : Orthonormal 𝕜 (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : ℕ) < m := ha
    have hb' : (b : ℕ) < m := hb
    simp only [Set.restrict_apply, hv, dif_pos ha', dif_pos hb']
    rw [orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V)
      ⟨(a : ℕ), ha'⟩ ⟨(b : ℕ), hb'⟩]
    congr 1
    simp only [Fin.mk.injEq, Subtype.mk.injEq, eq_iff_iff]
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact_mod_cast congrArg Fin.val h
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := v)
  set μ : Fin (finrank 𝕜 E) → ℝ := fun k =>
    if hk : (k : ℕ) < m then principalPlaneChord U V ⟨(k : ℕ), hk⟩ ^ 2 else 0
    with hμ
  have hμanti : Antitone μ := by
    intro a c hac
    rw [hμ]
    simp only
    split_ifs with h1 h2 h2
    · have hchord := principalPlaneChord_antitone U V
        (show (⟨(a : ℕ), h2⟩ : Fin m) ≤ ⟨(c : ℕ), h1⟩ from hac)
      have h0a := principalPlaneChord_nonneg U V ⟨(a : ℕ), h2⟩
      have h0c := principalPlaneChord_nonneg U V ⟨(c : ℕ), h1⟩
      nlinarith
    · positivity
    · omega
    · exact le_rfl
  -- The Gram operator of the restricted displacement.
  have hgramfull := adjoint_comp_displacement_directRotation U V hacute
  have hgram : AR.adjoint ∘ₗ AR =
      projection U ∘ₗ ((2 : 𝕜) • (LinearMap.id -
        ForMathlib.abs (canonicalIntertwiner U V))) ∘ₗ projection U := by
    rw [hAR, LinearMap.adjoint_comp, projection_adjoint, ← hgramfull]
    ext x
    simp only [LinearMap.comp_apply]
  have hdiag : ∀ k, (AR.adjoint ∘ₗ AR) (b k) = ((μ k : ℝ) : 𝕜) • b k := by
    intro k
    by_cases hk : (k : ℕ) < m
    · have hbk : b k = v k := hb k hk
      have hsrc : b k = principalSourceVector U V ⟨(k : ℕ), hk⟩ := by
        rw [hbk, hv]; simp [dif_pos hk]
      rw [hgram, hsrc]
      have hu := principalSourceVector_mem U V hacute ⟨(k : ℕ), hk⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        projection_apply_of_mem hu, LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.id_apply,
        abs_canonicalIntertwiner_apply_principalSourceVector U V hacute
          ⟨(k : ℕ), hk⟩]
      rw [smul_sub, map_sub, map_smul, map_smul, projection_apply_of_mem hu,
        projection_apply_of_mem hu, hμ]
      simp only [dif_pos hk]
      rw [principalPlaneChord_sq]
      match_scalars
      push_cast
      ring
    · -- `b k` is orthogonal to the sources; `P_U (b k)` is fixed by `|S|`.
      have hperp_u : ∀ i, ⟪principalSourceVector U V i, b k⟫_𝕜 = 0 := by
        intro i
        have hval : ((⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ :
            Fin (finrank 𝕜 E)) : ℕ) < m := i.isLt
        have hbu : b ⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ =
            principalSourceVector U V i := by
          rw [hb _ hval, hv]
          simp only [dif_pos hval]
          congr 1
          ext
          simp
        have hne : (⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ :
            Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hval
        rw [← hbu]
        exact b.orthonormal.inner_eq_zero hne
      have hPmem : projection U (b k) ∈ U := U.starProjection_apply_mem _
      have hPperp : ∀ i, ⟪principalSourceVector U V i, projection U (b k)⟫_𝕜 = 0 := by
        intro i
        have := projection_inner_left_eq_right U (principalSourceVector U V i) (b k)
        rw [projection_apply_of_mem (principalSourceVector_mem U V hacute i)] at this
        rw [← this, hperp_u i]
      have habs := abs_canonicalIntertwiner_apply_eq_self_of_orthogonal_sources
        U V hPmem hPperp
      rw [hgram, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, habs,
        sub_self, smul_zero, map_zero, hμ]
      simp [dif_neg hk]
  have heig := eigenvalues_eq_of_eigenbasis AR.isSymmetric_adjoint_comp_self rfl b
    hμanti hdiag
  rcases lt_or_ge n (finrank 𝕜 E) with hnE | hnE
  · rw [AR.singularValues_of_lt rfl hnE, heig]
    rw [hμ]
    simp only
    split_ifs with hn
    · exact Real.sqrt_sq (principalPlaneChord_nonneg U V _)
    · exact Real.sqrt_zero
  · rw [AR.singularValues_of_finrank_le hnE, dif_neg (by omega)]

/-- **Pointwise singular-value minimality of the restricted displacement**
(Davis--Kahan Proposition 4.1): every singular value of `(I - R) P_U` is
dominated by the corresponding singular value of `(I - W) P_U` for any
unitary `W` carrying `U` onto `V`. -/
theorem singularValues_restrictedDisplacement_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (n : ℕ) :
    ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U).singularValues n ≤
      ((LinearMap.id - W.toLinearMap) ∘ₗ projection U).singularValues n := by
  rw [singularValues_restrictedDisplacement_directRotation U V hacute n]
  split_ifs with hn
  · exact principalPlaneChord_le_singularValues_restrictedDisplacement
      U V hacute W hmap ⟨n, hn⟩
  · exact LinearMap.singularValues_nonneg _ n

/-- **Ky Fan minimality of the restricted displacement** (Davis--Kahan
Corollary 4.1, Ky Fan form). -/
theorem kyFanSum_restrictedDisplacement_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    kyFanSum k ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      kyFanSum k ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  kyFanSum_le_of_singularValues_le
    (singularValues_restrictedDisplacement_le U V hacute W hmap) k

/-- **Unitarily-invariant-norm minimality of the restricted displacement**
(Davis--Kahan Corollary 4.1): the direct rotation minimizes `N ((I - W) P_U)`
for every UI norm `N`, with no angle restriction, over any `RCLike` field. -/
theorem uiNorm_restrictedDisplacement_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      N ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  N.apply_le_of_kyFanSum_le
    (kyFanSum_restrictedDisplacement_le U V hacute W hmap)

end DavisKahanTheory
end ForMathlib
