/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Geometry.Symplectic.Hermitian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The ambient norm of an orthogonal complex structure

The accepted almost-complex module construction and compatible Hermitian
core give a complex inner product. When the complex structure is an
isometry, that inner product induces the original real Hilbert norm.
Thus no replacement norm or parallel complex-module representation is needed.

These are classical compatible-triple facts, used in the real stationary
transport decomposition; no mathematical novelty is claimed for them.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An isometric complex structure preserves the ambient real product. -/
theorem inner_apply_apply_of_isometry (J : AlmostComplexStructure E)
    (hJ : Isometry J) (x y : E) : ⟪J x, J y⟫_ℝ = ⟪x, y⟫_ℝ :=
  (J.toLinearMap.toLinearIsometry hJ).inner_map_map x y

/-- An orthogonal complex structure is skew with respect to the real
inner product. -/
theorem inner_apply_eq_neg_inner_apply (J : AlmostComplexStructure E)
    (hJ : Isometry J) (x y : E) : ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ := by
  have h := (J.toLinearMap.toLinearIsometry hJ).inner_map_map x (J y)
  change ⟪J x, J (J y)⟫_ℝ = ⟪x, J y⟫_ℝ at h
  rw [J.apply_apply, inner_neg_right] at h
  linarith

/-- A vector is orthogonal to its image under an orthogonal complex
structure. -/
theorem inner_self_apply_eq_zero (J : AlmostComplexStructure E)
    (hJ : Isometry J) (x : E) : ⟪x, J x⟫_ℝ = 0 := by
  have h := J.inner_apply_eq_neg_inner_apply hJ x x
  linarith [real_inner_comm (J x) x]

private def orthogonalBilin (J : AlmostComplexStructure E) : LinearMap.BilinForm ℝ E :=
  (innerₗ E).compl₁₂ J.toLinearMap LinearMap.id

private theorem orthogonalBilin_apply (J : AlmostComplexStructure E) (x y : E) :
    orthogonalBilin J x y = ⟪J x, y⟫_ℝ := rfl

private theorem orthogonalBilin_isAlt (J : AlmostComplexStructure E)
    (hJ : Isometry J) : (orthogonalBilin J).IsAlt := by
  intro x
  rw [orthogonalBilin_apply, real_inner_comm]
  exact J.inner_self_apply_eq_zero hJ x

private def orthogonalSymplectic (J : AlmostComplexStructure E) (hJ : Isometry J) :
    SymplecticForm E where
  toBilinForm := orthogonalBilin J
  isAlt := orthogonalBilin_isAlt J hJ
  nondegenerate := by
    refine (LinearMap.IsAlt.isRefl
      (orthogonalBilin_isAlt J hJ)).nondegenerate_iff_separatingLeft.mpr ?_
    intro x hx
    have h : J x = 0 := inner_self_eq_zero.mp (hx (J x))
    apply J.injective
    simpa using h

private theorem orthogonalSymplectic_apply (J : AlmostComplexStructure E)
    (hJ : Isometry J) (x y : E) : orthogonalSymplectic J hJ x y = ⟪J x, y⟫_ℝ := rfl

private theorem orthogonalSymplectic_compatible (J : AlmostComplexStructure E)
    (hJ : Isometry J) : (orthogonalSymplectic J hJ).Compatible J := by
  apply SymplecticForm.Compatible.of_tames
  · rw [SymplecticForm.invariant_iff]
    intro x y
    exact (J.toLinearMap.toLinearIsometry hJ).inner_map_map (J x) y
  · intro x hx
    change 0 < ⟪J x, J x⟫_ℝ
    rw [J.inner_apply_apply_of_isometry hJ]
    exact real_inner_self_pos.mpr hx

/-- The complex scalar action supplied by the accepted module construction
scales the original Hilbert norm exactly. -/
theorem norm_complexModule_smul (J : AlmostComplexStructure E) (hJ : Isometry J)
    (z : ℂ) (x : E) :
    letI := J.complexModule
    ‖z • x‖ = ‖z‖ * ‖x‖ := by
  let := J.complexModule
  have hnorm (y : E) : ‖J y‖ = ‖y‖ := (J.toLinearMap.toLinearIsometry hJ).norm_map y
  rw [J.complexModule_smul_def,
    ← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    norm_add_sq (𝕜 := ℝ)]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left, real_inner_smul_right,
    J.inner_self_apply_eq_zero hJ, mul_zero, map_zero, add_zero, hnorm,
    mul_pow, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The complex module of an orthogonal almost complex structure is a
normed space for the existing real Hilbert norm. -/
@[instance_reducible]
def normedSpaceOfIsometry (J : AlmostComplexStructure E) (hJ : Isometry J) :
    letI := J.complexModule
    NormedSpace ℂ E :=
  letI := J.complexModule
  { J.complexModule with norm_smul_le := fun z x => (J.norm_complexModule_smul hJ z x).le }

/-- The compatible Hermitian product of an orthogonal complex structure
induces the original Hilbert norm. The accepted complex module and
Hermitian core are consumed directly. -/
@[instance_reducible]
def innerProductSpaceOfIsometry (J : AlmostComplexStructure E) (hJ : Isometry J) :
    letI := J.complexModule
    InnerProductSpace ℂ E :=
  letI := J.complexModule
  letI := J.normedSpaceOfIsometry hJ
  { (orthogonalSymplectic_compatible J hJ).hermitianCore with
    norm_sq_eq_re_inner := fun x => by
      rw [SymplecticForm.Compatible.hermitianCore_inner]
      change ‖x‖ ^ 2 =
        ((⟪J x, J x⟫_ℝ : ℂ) + Complex.I * (⟪J x, x⟫_ℝ : ℂ)).re
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
      rw [J.inner_apply_apply_of_isometry hJ]
      exact (real_inner_self_eq_norm_sq x).symm }

/-- The complex inner product has the original real part and the
symplectic imaginary part determined by the complex structure. -/
theorem innerProductSpaceOfIsometry_inner (J : AlmostComplexStructure E)
    (hJ : Isometry J) (x y : E) :
    letI := J.complexModule
    letI := J.innerProductSpaceOfIsometry hJ
    ⟪x, y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) + Complex.I * (⟪J x, y⟫_ℝ : ℂ) := by
  let := J.complexModule
  let := J.innerProductSpaceOfIsometry hJ
  change ((orthogonalSymplectic_compatible J hJ).hermitianCore.inner x y) = _
  rw [SymplecticForm.Compatible.hermitianCore_inner]
  change (⟪J x, J y⟫_ℝ : ℂ) + Complex.I * (⟪J x, y⟫_ℝ : ℂ) = _
  rw [J.inner_apply_apply_of_isometry hJ]

/-- An orthogonal complex structure on a finite real Hilbert space has
an orthonormal basis in quarter-turn pairs. The construction restricts an
orthonormal basis of its accepted induced complex module to real scalars. -/
theorem exists_paired_orthonormalBasis [FiniteDimensional ℝ E]
    (J : AlmostComplexStructure E) (hJ : Isometry J) :
    ∃ n : ℕ, ∃ e : OrthonormalBasis (Fin 2 × Fin n) ℝ E,
      (∀ i, J (e (0, i)) = e (1, i)) ∧
      (∀ i, J (e (1, i)) = -e (0, i)) := by
  classical
  let := J.complexModule
  let := J.complexModule_isScalarTower
  let := J.innerProductSpaceOfIsometry hJ
  let : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  let b := stdOrthonormalBasis ℂ E
  let br := Complex.basisOneI.smulTower b.toBasis
  have hre (x y : E) : ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
    rw [J.innerProductSpaceOfIsometry_inner hJ]
    simp
  have horth : Orthonormal ℝ br := by
    rw [orthonormal_iff_ite]
    rintro ⟨r, i⟩ ⟨s, j⟩
    simp only [br, Module.Basis.smulTower_apply, OrthonormalBasis.coe_toBasis]
    rw [hre, inner_smul_left, inner_smul_right, b.inner_eq_ite]
    by_cases hij : i = j
    · subst j
      fin_cases r <;> fin_cases s <;> simp [Complex.coe_basisOneI]
    · have hne : (r, i) ≠ (s, j) := fun h => hij (congrArg Prod.snd h)
      simp [hij, hne]
  let e := br.toOrthonormalBasis horth
  have he0 (i) : J (e (0, i)) = e (1, i) := by
    simp [e, Module.Basis.coe_toOrthonormalBasis, br, Module.Basis.smulTower_apply,
      Complex.coe_basisOneI, J.complexModule_I_smul]
  refine ⟨Module.finrank ℂ E, e, he0, ?_⟩
  intro i
  rw [← he0, J.apply_apply]

/-- A finite real vector space carrying a complex structure has even
real dimension. Orthogonality is unnecessary for this obstruction. -/
theorem even_finrank_real [FiniteDimensional ℝ E] (J : AlmostComplexStructure E) :
    Even (Module.finrank ℝ E) := by
  let := J.complexModule
  let := J.complexModule_isScalarTower
  refine ⟨Module.finrank ℂ E, ?_⟩
  calc
    Module.finrank ℝ E = Module.finrank ℝ ℂ * Module.finrank ℂ E :=
      (Module.finrank_mul_finrank ℝ ℂ E).symm
    _ = _ := by rw [Complex.finrank_real_complex]; omega

/-- **Exact finite-dimensional real complex-structure criterion.** A real
Hilbert multiplicity space admits an orthogonal quarter-turn exactly
when its real dimension is even. This is the algebraic obstruction for
real signed roots on a strictly acute positive angle block. -/
theorem exists_isometric_iff_even_finrank_real [FiniteDimensional ℝ E] :
    (∃ J : AlmostComplexStructure E, Isometry J) ↔ Even (Module.finrank ℝ E) := by
  constructor
  · rintro ⟨J, _⟩
    exact J.even_finrank_real
  · rintro ⟨m, hm⟩
    let F := EuclideanSpace ℂ (Fin m)
    have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
      rw [finrank_real_of_complex F, finrank_euclideanSpace_fin]
      omega
    let u : E ≃ₗᵢ[ℝ] F :=
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr.trans
        (stdOrthonormalBasis ℝ F).repr.symm
    let M : F →ₗ[ℝ] F :=
      (Complex.I • (LinearMap.id : F →ₗ[ℂ] F)).restrictScalars ℝ
    let J : AlmostComplexStructure E :=
      { toLinearMap := u.symm.toLinearMap.comp (M.comp u.toLinearMap)
        square_neg := by
          ext x
          change u.symm (Complex.I • u (u.symm (Complex.I • u x))) = -x
          rw [u.apply_symm_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
            map_neg, u.symm_apply_apply] }
    refine ⟨J, ?_⟩
    apply (show Isometry J.toLinearMap from ?_)
    apply AddMonoidHomClass.isometry_of_norm J.toLinearMap
    intro x
    change ‖u.symm (Complex.I • u x)‖ = ‖x‖
    rw [u.symm.norm_map, norm_smul, Complex.norm_I, one_mul, u.norm_map]

/-- **Exact real skew-unitary factor criterion.** A finite real
multiplicity space admits a skew-adjoint orthogonal operator exactly
when its dimension is even. The zero-dimensional space is included. -/
theorem exists_skew_unitary_iff_even_finrank_real [FiniteDimensional ℝ E] [CompleteSpace E] :
    (∃ U : E →L[ℝ] E, U ∈ unitary (E →L[ℝ] E) ∧ star U = -U) ↔
      Even (Module.finrank ℝ E) := by
  constructor
  · rintro ⟨U, hU, hstar⟩
    have hsq : U * U = -1 := by
      have h := Unitary.star_mul_self_of_mem hU
      rw [hstar, neg_mul] at h
      exact neg_eq_iff_eq_neg.mp h
    let J : AlmostComplexStructure E :=
      { toLinearMap := U.toLinearMap
        square_neg := by
          ext x
          exact congrArg (fun A : E →L[ℝ] E => A x) hsq }
    exact J.even_finrank_real
  · intro hdim
    obtain ⟨J, hJ⟩ := exists_isometric_iff_even_finrank_real.mpr hdim
    let V := (J.toLinearMap.toLinearIsometry hJ).toLinearIsometryEquiv rfl
    let U : E →L[ℝ] E := V
    have hU : U ∈ unitary (E →L[ℝ] E) :=
      (Unitary.linearIsometryEquiv.symm V).property
    have hsq : U * U = -1 := by
      ext x
      exact J.apply_apply x
    refine ⟨U, hU, ?_⟩
    have hneg : -star U = U := by
      calc
        _ = star U * (-1) := by simp only [mul_neg, mul_one]
        _ = star U * (U * U) := by rw [hsq]
        _ = U := by rw [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul]
    exact neg_eq_iff_eq_neg.mp hneg

end TauCeti.AlmostComplexStructure
