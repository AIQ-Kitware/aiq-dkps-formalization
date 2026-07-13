/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.Fourier.HaagerupZsidoKernel
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite reciprocal multipliers

This file isolates the harmonic-analysis core of the finite
Bhatia--Davis--McIntosh Sylvester estimate.

Literature bridge:

* `prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`
  reconstructs the separated-spectrum Fourier representation, the `pi / 2`
  provenance chain, the finite interpolation reduction, and the real-field
  descent that remains to be supplied.

The operator-theoretic theorem is factored through one simultaneous finite
interpolation certificate.  For fixed orthonormal coordinates and separated
real arrays `α` and `β`, the certificate supplies one finite family of
left/right unitaries whose orbit action realizes the reciprocal multiplier on
every coordinate matrix unit at once, with coefficient mass at most `π / 2`.

Once that certificate is available, the passage to an arbitrary rectangular
map is finite linear algebra: expand the map in coordinate matrix units, use
the entrywise Sylvester equation, and recombine the common orbit action.  The
Ky Fan estimate is then an immediate application of the existing finite-orbit
certificate bound.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The coordinate matrix unit sending the `j`th vector of `eE` to the `i`th
vector of `eF` and annihilating the other basis vectors. -/
noncomputable def basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) : E →ₗ[𝕜] F :=
  (InnerProductSpace.rankOne 𝕜 (eF i) (eE j)).toLinearMap

/-- Pointwise formula for a coordinate matrix unit. -/
theorem basisMatrixUnit_apply
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) (x : E) :
    basisMatrixUnit eF eE i j x = ⟪eE j, x⟫_𝕜 • eF i := by
  rfl

/-- A rectangular map is the finite sum of its matrix coefficients times the
coordinate matrix units in any pair of orthonormal bases. -/
theorem sum_basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (T : E →ₗ[𝕜] F) :
    T = ∑ i, ∑ j, ⟪eF i, T (eE j)⟫_𝕜 • basisMatrixUnit eF eE i j := by
  classical
  refine eE.toBasis.ext fun q => ?_
  rw [OrthonormalBasis.coe_toBasis]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    basisMatrixUnit_apply, eE.inner_eq_ite]
  rw [← eF.sum_repr' (T (eE q))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single q]
  · simp
  · intro j _ hjq
    simp [hjq]
  · simp

/-- The linear action on rectangular maps induced by left and right unitary
composition. -/
noncomputable def unitaryOrbitAction
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) where
  toFun T := U.toLinearMap ∘ₗ T ∘ₗ V.toLinearMap
  map_add' A B := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' a A := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

@[simp]
theorem unitaryOrbitAction_apply
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (T : E →ₗ[𝕜] F) :
    unitaryOrbitAction U V T = U.toLinearMap ∘ₗ T ∘ₗ V.toLinearMap :=
  rfl

/-- The unitary diagonal in an orthonormal basis with prescribed unit-modulus
coordinate factors.  This is the finite-dimensional operator attached to one
Fourier character in the reciprocal-multiplier argument. -/
noncomputable def basisDiagonalUnitary {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 G) (ζ : ι → unitary 𝕜) : G ≃ₗᵢ[𝕜] G :=
  e.repr.trans <|
    (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
      ζ i • LinearIsometryEquiv.refl 𝕜 𝕜).trans e.repr.symm

/-- A basis diagonal acts on each basis vector by its prescribed phase. -/
@[simp]
theorem basisDiagonalUnitary_apply_basis {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 G) (ζ : ι → unitary 𝕜) (i : ι) :
    basisDiagonalUnitary e ζ (e i) = (ζ i : 𝕜) • e i := by
  rw [← e.repr_symm_single i]
  simp only [basisDiagonalUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [LinearIsometryEquiv.piLpCongrRight_single]
  simp only [LinearIsometryEquiv.smul_apply]
  change e.repr.symm (PiLp.single 2 i ((ζ i : 𝕜) * 1)) = _
  rw [mul_one]
  rw [← map_smul]
  congr 1
  ext q
  simp [PiLp.single_apply]

/-- Left and right basis diagonals act on a coordinate matrix unit by the
product of the corresponding coordinate phases.  Taking the left phase at
frequency `α i` and the right phase at frequency `-β j` therefore realizes
the Fourier character at the difference `α i - β j`. -/
theorem unitaryOrbitAction_basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (ζF : Fin (Module.finrank 𝕜 F) → unitary 𝕜)
    (ζE : Fin (Module.finrank 𝕜 E) → unitary 𝕜)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) :
    unitaryOrbitAction (basisDiagonalUnitary eF ζF)
        (basisDiagonalUnitary eE ζE) (basisMatrixUnit eF eE i j) =
      ((ζF i : 𝕜) * (ζE j : 𝕜)) • basisMatrixUnit eF eE i j := by
  refine eE.toBasis.ext fun q => ?_
  rw [OrthonormalBasis.coe_toBasis]
  change basisDiagonalUnitary eF ζF
      (basisMatrixUnit eF eE i j (basisDiagonalUnitary eE ζE (eE q))) =
    (((ζF i : 𝕜) * (ζE j : 𝕜)) • basisMatrixUnit eF eE i j) (eE q)
  rw [basisDiagonalUnitary_apply_basis, map_smul, map_smul,
    basisMatrixUnit_apply, LinearMap.smul_apply, basisMatrixUnit_apply,
    eE.inner_eq_ite]
  by_cases hjq : j = q
  · subst q
    simp only [ite_true, one_smul, basisDiagonalUnitary_apply_basis]
    rw [smul_smul, mul_comm]
  · simp [hjq]

/-- The complex unitary phase with angular frequency parameter `x`. -/
noncomputable def complexFourierPhase (x : ℝ) : unitary ℂ := by
  let z : ℂ := Circle.exp x
  have hz : ‖z‖ = 1 := Circle.norm_coe (Circle.exp x)
  refine ⟨z, ?_⟩
  rw [Unitary.mem_iff]
  constructor
  · change conj z * z = 1
    rw [RCLike.conj_mul, hz]
    norm_num
  · change z * conj z = 1
    rw [RCLike.mul_conj, hz]
    norm_num

@[simp]
theorem complexFourierPhase_coe (x : ℝ) :
    (complexFourierPhase x : ℂ) =
      Complex.exp ((x : ℂ) * Complex.I) :=
  rfl

@[simp]
theorem complexFourierPhase_mul (x y : ℝ) :
    (complexFourierPhase x : ℂ) * (complexFourierPhase y : ℂ) =
      (complexFourierPhase (x + y) : ℂ) := by
  exact (congrArg ((↑) : Circle → ℂ) (Circle.exp_add x y)).symm

/-- The real-linear rotation by `theta` on two copies of a real vector space. -/
private noncomputable def realRotationLinearEquiv
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (theta : ℝ) : (G × G) ≃ₗ[ℝ] (G × G) where
  toFun x :=
    (Real.cos theta • x.1 - Real.sin theta • x.2,
      Real.sin theta • x.1 + Real.cos theta • x.2)
  invFun x :=
    (Real.cos theta • x.1 + Real.sin theta • x.2,
      -Real.sin theta • x.1 + Real.cos theta • x.2)
  left_inv x := by
    have htrig : Real.cos theta * Real.cos theta +
        Real.sin theta * Real.sin theta = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  right_inv x := by
    have htrig : Real.cos theta * Real.cos theta +
        Real.sin theta * Real.sin theta = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  map_add' x y := by
    apply Prod.ext <;> simp <;> module
  map_smul' r x := by
    apply Prod.ext <;> simp [smul_smul] <;> module

/-- A complex phase acting on a real Hilbert space after doubling is the
ordinary two-dimensional rotation, applied simultaneously in every direction. -/
noncomputable def doubledRealRotation
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (theta : ℝ) : WithLp 2 (G × G) ≃ₗᵢ[ℝ] WithLp 2 (G × G) where
  __ := (realRotationLinearEquiv theta).withLpCongr 2
  norm_map' x := by
    have htrig : Real.cos theta * Real.cos theta +
        Real.sin theta * Real.sin theta = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    change ‖WithLp.toLp 2
      (Real.cos theta • x.fst - Real.sin theta • x.snd,
        Real.sin theta • x.fst + Real.cos theta • x.snd)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      norm_sq_eq_re_inner ( 𝕜 := ℝ), norm_sq_eq_re_inner ( 𝕜 := ℝ)]
    simp only [WithLp.prod_inner_apply]
    change _ = ⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      RCLike.re_to_real]
    rw [real_inner_comm x.fst x.snd]
    linear_combination
      (⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ) * htrig

@[simp] theorem doubledRealRotation_apply
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (theta : ℝ) (x : WithLp 2 (G × G)) :
    doubledRealRotation theta x = WithLp.toLp 2
      (Real.cos theta • x.fst - Real.sin theta • x.snd,
        Real.sin theta • x.fst + Real.cos theta • x.snd) :=
  rfl

/-- A real diagonal map in an orthonormal basis. -/
private noncomputable def basisDiagonalRealMap
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (c : ι → ℝ) : G →ₗ[ℝ] G :=
  e.toBasis.constr ℝ fun i => c i • e i

@[simp] private theorem basisDiagonalRealMap_apply_basis
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (c : ι → ℝ) (i : ι) :
    basisDiagonalRealMap e c (e i) = c i • e i := by
  exact e.toBasis.constr_basis ℝ _ i

@[simp] private theorem basisDiagonalRealMap_repr
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (c : ι → ℝ) (x : G) (i : ι) :
    e.repr (basisDiagonalRealMap e c x) i = c i * e.repr x i := by
  rw [← e.sum_repr x]
  simp only [map_sum, map_smul, basisDiagonalRealMap_apply_basis, smul_smul]
  simp [Pi.single_apply]
  ring

/-- Coordinatewise real rotations in an orthonormal basis, before transporting
the product norm to `WithLp 2`. -/
private noncomputable def basisDoubledRealRotationLinearEquiv
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) :
    (G × G) ≃ₗ[ℝ] (G × G) := by
  let C := basisDiagonalRealMap e fun i => Real.cos (theta i)
  let S := basisDiagonalRealMap e fun i => Real.sin (theta i)
  refine
    { toFun := fun x => (C x.1 - S x.2, S x.1 + C x.2)
      invFun := fun x => (C x.1 + S x.2, -S x.1 + C x.2)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Prod.ext <;> simp [C, S] <;> module
  · intro r x
    apply Prod.ext <;> simp [C, S] <;> module
  · intro x
    have htrig (i : ι) : Real.cos (theta i) * Real.cos (theta i) +
        Real.sin (theta i) * Real.sin (theta i) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (theta i)]
    apply Prod.ext
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.1 i) * htrig i
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.2 i) * htrig i
  · intro x
    have htrig (i : ι) : Real.cos (theta i) * Real.cos (theta i) +
        Real.sin (theta i) * Real.sin (theta i) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (theta i)]
    apply Prod.ext
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.1 i) * htrig i
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.2 i) * htrig i

/-- Coordinatewise phase rotations on two real copies of a Hilbert space. -/
noncomputable def basisDoubledRealRotation
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) :
    WithLp 2 (G × G) ≃ₗᵢ[ℝ] WithLp 2 (G × G) where
  __ := (basisDoubledRealRotationLinearEquiv e theta).withLpCongr 2
  norm_map' x := by
    let C := basisDiagonalRealMap e fun i => Real.cos (theta i)
    let S := basisDiagonalRealMap e fun i => Real.sin (theta i)
    have hparseval (z : G) : ∑ i, ‖e.repr z i‖ ^ 2 = ‖z‖ ^ 2 := by
      simp_rw [e.repr_apply_apply]
      exact e.sum_sq_norm_inner_right z
    change ‖WithLp.toLp 2 (C x.fst - S x.snd, S x.fst + C x.snd)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖C x.fst - S x.snd‖ ^ 2 + ‖S x.fst + C x.snd‖ ^ 2 =
      ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
    rw [
      ← hparseval (C x.fst - S x.snd), ← hparseval (S x.fst + C x.snd),
      ← hparseval x.fst, ← hparseval x.snd,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_sub, map_add, C, S, basisDiagonalRealMap_repr,
      PiLp.sub_apply, PiLp.add_apply, Real.norm_eq_abs, sq_abs]
    have htrig : Real.cos (theta i) * Real.cos (theta i) +
        Real.sin (theta i) * Real.sin (theta i) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (theta i)]
    linear_combination
      ((e.repr x.fst i) ^ 2 + (e.repr x.snd i) ^ 2) * htrig

@[simp] theorem basisDoubledRealRotation_apply
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ)
    (x : WithLp 2 (G × G)) :
    basisDoubledRealRotation e theta x = WithLp.toLp 2
      (basisDiagonalRealMap e (fun i => Real.cos (theta i)) x.fst -
          basisDiagonalRealMap e (fun i => Real.sin (theta i)) x.snd,
        basisDiagonalRealMap e (fun i => Real.sin (theta i)) x.fst +
          basisDiagonalRealMap e (fun i => Real.cos (theta i)) x.snd) := by
  rfl

@[simp] theorem basisDoubledRealRotation_apply_first
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) (i : ι) :
    basisDoubledRealRotation e theta (WithLp.toLp 2 (e i, 0)) =
      WithLp.toLp 2
        (Real.cos (theta i) • e i, Real.sin (theta i) • e i) := by
  change WithLp.toLp 2
    (basisDiagonalRealMap e (fun q => Real.cos (theta q)) (e i) -
        basisDiagonalRealMap e (fun q => Real.sin (theta q)) 0,
      basisDiagonalRealMap e (fun q => Real.sin (theta q)) (e i) +
        basisDiagonalRealMap e (fun q => Real.cos (theta q)) 0) = _
  simp

@[simp] theorem basisDoubledRealRotation_apply_second
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) (i : ι) :
    basisDoubledRealRotation e theta (WithLp.toLp 2 (0, e i)) =
      WithLp.toLp 2
        (-Real.sin (theta i) • e i, Real.cos (theta i) • e i) := by
  change WithLp.toLp 2
    (basisDiagonalRealMap e (fun q => Real.cos (theta q)) 0 -
        basisDiagonalRealMap e (fun q => Real.sin (theta q)) (e i),
      basisDiagonalRealMap e (fun q => Real.sin (theta q)) 0 +
        basisDiagonalRealMap e (fun q => Real.cos (theta q)) (e i)) = _
  simp

/-- The doubled-real map corresponding to multiplication by the complex phase
`exp (theta * I)` after applying a real rectangular map. -/
noncomputable def doubledPhaseAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR) :=
  (doubledRealRotation (G := FR) theta).toLinearMap ∘ₗ
    RectangularUnitarilyInvariantNorm.orthogonalBlockSum T T

@[simp] theorem doubledPhaseAction_apply
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) (x : WithLp 2 (ER × ER)) :
    doubledPhaseAction theta T x = WithLp.toLp 2
      (Real.cos theta • T x.fst - Real.sin theta • T x.snd,
        Real.sin theta • T x.fst + Real.cos theta • T x.snd) := by
  rfl

/-- The real `2 × 2` block action of a complex scalar on a doubled real map. -/
def doubledComplexScalarAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z : ℂ) (T : ER →ₗ[ℝ] FR) :
    WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR) where
  toFun x := WithLp.toLp 2
    (z.re • T x.fst - z.im • T x.snd,
      z.im • T x.fst + z.re • T x.snd)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp <;> module
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp [smul_smul] <;> module

@[simp] theorem doubledComplexScalarAction_apply
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z : ℂ) (T : ER →ₗ[ℝ] FR) (x : WithLp 2 (ER × ER)) :
    doubledComplexScalarAction z T x = WithLp.toLp 2
      (z.re • T x.fst - z.im • T x.snd,
        z.im • T x.fst + z.re • T x.snd) :=
  rfl

/-- A doubled phase action is complex scalar action by its unit phase. -/
theorem doubledPhaseAction_eq_complexScalarAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    doubledPhaseAction theta T =
      doubledComplexScalarAction (Complex.exp ((theta : ℂ) * Complex.I)) T := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [doubledPhaseAction_apply, doubledComplexScalarAction_apply,
    Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- Complex-scalar block action is additive in the scalar. -/
theorem doubledComplexScalarAction_add
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z w : ℂ) (T : ER →ₗ[ℝ] FR) :
    doubledComplexScalarAction (z + w) T =
      doubledComplexScalarAction z T + doubledComplexScalarAction w T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [doubledComplexScalarAction_apply] <;> module

/-- Real scaling of complex-scalar block action agrees with multiplication of
the complex scalar by that real number. -/
theorem doubledComplexScalarAction_real_smul
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (r : ℝ) (z : ℂ) (T : ER →ₗ[ℝ] FR) :
    r • doubledComplexScalarAction z T =
      doubledComplexScalarAction ((r : ℂ) * z) T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarAction_apply, smul_smul] <;> module

/-- A real complex scalar acts as the same real scalar on two orthogonal
copies of a real map. -/
theorem doubledComplexScalarAction_ofReal
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (r : ℝ) (T : ER →ₗ[ℝ] FR) :
    doubledComplexScalarAction (r : ℂ) T =
      r • RectangularUnitarilyInvariantNorm.orthogonalBlockSum T T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarAction_apply,
      RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply] <;> module

/-- A finite sum of complex-scalar block actions is the action of the scalar
sum. -/
theorem sum_doubledComplexScalarAction
    {ER FR ι : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (T : ER →ₗ[ℝ] FR) :
    ∑ i, doubledComplexScalarAction (z i) T =
      doubledComplexScalarAction (∑ i, z i) T := by
  classical
  have h (s : Finset ι) :
      s.sum (fun i => doubledComplexScalarAction (z i) T) =
        doubledComplexScalarAction (s.sum z) T := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        ext x
        apply WithLp.ofLp_injective 2
        simp [doubledComplexScalarAction]
        exact Prod.ext rfl rfl
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
          doubledComplexScalarAction_add]
  exact h Finset.univ

/-- Polar decomposition of one complex Fourier coefficient: its norm becomes
a nonnegative real weight and its argument becomes an additional doubled-real
rotation angle. -/
theorem norm_smul_doubledPhaseAction_arg_add
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (a : ℂ) (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    ‖a‖ • doubledPhaseAction (Complex.arg a + theta) T =
      doubledComplexScalarAction
        (a * Complex.exp ((theta : ℂ) * Complex.I)) T := by
  rw [doubledPhaseAction_eq_complexScalarAction,
    doubledComplexScalarAction_real_smul]
  congr 1
  change ((‖a‖ : ℝ) : ℂ) *
      Complex.exp (((Complex.arg a + theta : ℝ) : ℂ) * Complex.I) =
    a * Complex.exp ((theta : ℂ) * Complex.I)
  calc
    ((‖a‖ : ℝ) : ℂ) *
        Complex.exp (((Complex.arg a + theta : ℝ) : ℂ) * Complex.I) =
      ((‖a‖ : ℝ) : ℂ) *
        (Complex.exp (((Complex.arg a : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((theta : ℂ) * Complex.I)) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = (((‖a‖ : ℝ) : ℂ) *
          Complex.exp (((Complex.arg a : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((theta : ℂ) * Complex.I) := by ring
    _ = a * Complex.exp ((theta : ℂ) * Complex.I) := by
      rw [Complex.norm_mul_exp_arg_mul_I]

/-- A finite complex Fourier sum acts on doubled real maps as a finite sum of
nonnegatively weighted real phase rotations. -/
theorem sum_norm_smul_doubledPhaseAction_arg_add
    {ER FR ι : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (theta : ι → ℝ) (T : ER →ₗ[ℝ] FR) :
    ∑ r, ‖a r‖ • doubledPhaseAction (Complex.arg (a r) + theta r) T =
      doubledComplexScalarAction
        (∑ r, a r * Complex.exp (((theta r : ℝ) : ℂ) * Complex.I)) T := by
  classical
  simp_rw [norm_smul_doubledPhaseAction_arg_add]
  exact sum_doubledComplexScalarAction _ T

/-- Coordinatewise doubled-real rotations realize addition of the left and
right phase angles on a doubled coordinate matrix unit. -/
theorem basisDoubledRealRotation_comp_basisMatrixUnit
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (thetaF : Fin (Module.finrank ℝ FR) → ℝ)
    (thetaE : Fin (Module.finrank ℝ ER) → ℝ)
    (i : Fin (Module.finrank ℝ FR))
    (j : Fin (Module.finrank ℝ ER)) :
    (basisDoubledRealRotation eF thetaF).toLinearMap ∘ₗ
        RectangularUnitarilyInvariantNorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) ∘ₗ
        (basisDoubledRealRotation eE thetaE).toLinearMap =
      doubledPhaseAction (thetaF i + thetaE j)
        (basisMatrixUnit eF eE i j) := by
  apply (eE.prod eE).toBasis.ext
  intro q
  rcases q with q | q
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          real_inner_smul_right, Real.cos_add, Real.sin_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          real_inner_smul_right, hq]
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          real_inner_smul_right, Real.cos_add, Real.sin_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          real_inner_smul_right, hq]

/-- The complex basis-diagonal orbit realizes the Fourier character at the
coordinate difference `α i - β j`.  This is the exact operator-valued atom
used after obtaining a scalar reciprocal Fourier representation. -/
theorem complexUnitaryOrbitAction_basisMatrixUnit_exp_sub
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    [FiniteDimensional ℂ FC]
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    (t : ℝ) (i : Fin (Module.finrank ℂ FC))
    (j : Fin (Module.finrank ℂ EC)) :
    unitaryOrbitAction
        (basisDiagonalUnitary eF fun q => complexFourierPhase (t * α q))
        (basisDiagonalUnitary eE fun q => complexFourierPhase (-(t * β q)))
        (basisMatrixUnit eF eE i j) =
      Complex.exp ((((t * (α i - β j)) : ℝ) : ℂ) * Complex.I) •
        basisMatrixUnit eF eE i j := by
  rw [unitaryOrbitAction_basisMatrixUnit, complexFourierPhase_mul,
    complexFourierPhase_coe]
  congr 1
  congr 1
  ring_nf

/-- The average of an integrable function for a nonzero finite measure can be
approximated by a finite convex combination of actual values of the function.

This is the finite quadrature step used to turn an integrable scalar Fourier
kernel into finitely many Fourier atoms.  It is stated for a general real
normed space so the coefficient mass can later be included as one additional
coordinate of the integrand. -/
theorem exists_finite_average_approximation
    {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ] [NeZero μ]
    (g : Ω → V) (hg : MeasureTheory.Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ z : Fin q → Ω,
      (∀ r, 0 ≤ w r) ∧
      ∑ r, w r = 1 ∧
      dist (∑ r, w r • g (z r)) (⨍ x, g x ∂μ) < ε := by
  classical
  have havg : (⨍ x, g x ∂μ) ∈
      closedConvexHull ℝ (Set.range g) := by
    exact convex_closedConvexHull.average_mem isClosed_closedConvexHull
      (Filter.Eventually.of_forall fun x => subset_closedConvexHull (Set.mem_range_self x)) hg
  rw [closedConvexHull_eq_closure_convexHull] at havg
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp havg ε hε
  rcases mem_convexHull_iff_exists_fintype.mp hy with
    ⟨ι, hι, w, v, hw₀, hw₁, hv, hvsum⟩
  letI : Fintype ι := hι
  let z : ι → Ω := fun i => Classical.choose (hv i)
  have hz (i : ι) : g (z i) = v i := Classical.choose_spec (hv i)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, w ∘ e.symm, z ∘ e.symm, ?_, ?_, ?_⟩
  · intro r
    exact hw₀ (e.symm r)
  · simpa only [Function.comp_apply] using (e.symm.sum_comp w).trans hw₁
  · have hsum : ∑ i, w i • g (z i) = y := by
      calc
        ∑ i, w i • g (z i) = ∑ i, w i • v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hz i]
        _ = y := hvsum
    have hreindex :
        (∑ r : Fin (Fintype.card ι),
          (w ∘ e.symm) r • g ((z ∘ e.symm) r)) =
        ∑ i : ι, w i • g (z i) := by
      simpa only [Function.comp_apply] using
        e.symm.sum_comp (fun i => w i • g (z i))
    rw [hreindex, hsum, dist_comm]
    exact hdist

/-- Arbitrary complex values on a finite set of real frequencies admit an
exact finite Fourier interpolation.

The proof places the finitely many frequencies in an arc shorter than a full
circle, applies Lagrange interpolation to their distinct complex phases, and
reads the polynomial coefficients as Fourier coefficients.  This is the
algebraic correction mechanism needed when a reciprocal Fourier integral is
first approximated by a finite sum. -/
theorem exists_finite_fourier_interpolation
    (s : Finset ℝ) (y : ℝ → ℂ) :
    ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
      ∀ x ∈ s, y x = ∑ r, a r * Complex.exp
        ((((t r * x) : ℝ) : ℂ) * Complex.I) := by
  classical
  let R : ℝ := ∑ x ∈ s, |x|
  let τ : ℝ := (1 + R)⁻¹
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hτ : 0 < τ := by
    simp only [τ]
    positivity
  have harg (x : ℝ) (hx : x ∈ s) : τ * x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hxR : |x| ≤ R := by
      exact Finset.single_le_sum
        (fun z hz => abs_nonneg z) hx
    have hden : 0 < 1 + R := by linarith
    have habs : |τ * x| < 1 := by
      rw [abs_mul, abs_of_pos hτ]
      change (1 + R)⁻¹ * |x| < 1
      rw [inv_mul_eq_div, div_lt_one hden]
      linarith
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  let z : ℝ → ℂ := fun x => (Circle.exp (τ * x) : ℂ)
  have hzinj : Set.InjOn z s := by
    intro x hx x' hx' hzx
    have harc : (1 : ℝ) - (-1) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hphase : τ * x = τ * x' :=
      Circle.exp_injOn_Icc harc (harg x hx) (harg x' hx') (Subtype.ext hzx)
    exact (mul_left_cancel₀ (ne_of_gt hτ) hphase)
  let p : Polynomial ℂ := Lagrange.interpolate s z y
  refine ⟨p.natDegree + 1, fun r => p.coeff r, fun r => (r : ℕ) * τ, ?_⟩
  intro x hx
  rw [← Lagrange.eval_interpolate_at_node y hzinj hx]
  rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  change p.coeff r * z x ^ (r : ℕ) =
    p.coeff r * Complex.exp
      ((((((r : ℕ) : ℝ) * τ * x) : ℝ) : ℂ) * Complex.I)
  congr 1
  simp only [z, Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The finite Fourier interpolation map can be chosen with coefficient mass
bounded linearly by the `ℓ1` mass of the prescribed values.

For a fixed finite frequency set the constant is allowed to depend on that
set.  This is exactly the stability needed to correct a uniformly vanishing
finite error vector without changing the limiting Fourier mass. -/
theorem exists_finite_fourier_interpolation_with_mass_bound
    (s : Finset ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ → ℂ,
      ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
        (∀ x ∈ s, y x = ∑ r, a r * Complex.exp
          ((((t r * x) : ℝ) : ℂ) * Complex.I)) ∧
        ∑ r, ‖a r‖ ≤ K * ∑ x ∈ s, ‖y x‖ := by
  classical
  let R : ℝ := ∑ x ∈ s, |x|
  let τ : ℝ := (1 + R)⁻¹
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hτ : 0 < τ := by
    simp only [τ]
    positivity
  have harg (x : ℝ) (hx : x ∈ s) : τ * x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hxR : |x| ≤ R := by
      exact Finset.single_le_sum (fun z hz => abs_nonneg z) hx
    have hden : 0 < 1 + R := by linarith
    have habs : |τ * x| < 1 := by
      rw [abs_mul, abs_of_pos hτ]
      change (1 + R)⁻¹ * |x| < 1
      rw [inv_mul_eq_div, div_lt_one hden]
      linarith
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  let z : ℝ → ℂ := fun x => (Circle.exp (τ * x) : ℂ)
  have hzinj : Set.InjOn z s := by
    intro x hx x' hx' hzx
    have harc : (1 : ℝ) - (-1) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hphase : τ * x = τ * x' :=
      Circle.exp_injOn_Icc harc (harg x hx) (harg x' hx') (Subtype.ext hzx)
    exact mul_left_cancel₀ (ne_of_gt hτ) hphase
  let q : ℕ := s.card + 1
  let K : ℝ := ∑ n : Fin q, ∑ x ∈ s,
    ‖(Lagrange.basis s z x).coeff (n : ℕ)‖
  refine ⟨K, Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro y
  let p : Polynomial ℂ := Lagrange.interpolate s z y
  have hpdeg : p.natDegree < q := by
    apply Nat.lt_succ_of_le
    apply Polynomial.natDegree_le_of_degree_le
    exact (Lagrange.degree_interpolate_le y hzinj).trans (by
      exact_mod_cast Nat.sub_le s.card 1)
  refine ⟨q, fun n => p.coeff n, fun n => (n : ℕ) * τ, ?_, ?_⟩
  · intro x hx
    rw [← Lagrange.eval_interpolate_at_node y hzinj hx]
    rw [Polynomial.eval_eq_sum_range' hpdeg, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    change p.coeff n * z x ^ (n : ℕ) =
      p.coeff n * Complex.exp
        ((((((n : ℕ) : ℝ) * τ * x) : ℝ) : ℂ) * Complex.I)
    congr 1
    simp only [z, Circle.coe_exp]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · have hcoeff (n : ℕ) :
        p.coeff n = ∑ x ∈ s, y x * (Lagrange.basis s z x).coeff n := by
      simp [p, Lagrange.interpolate_apply]
    calc
      ∑ n : Fin q, ‖p.coeff n‖ ≤
          ∑ n : Fin q, ∑ x ∈ s,
            ‖y x‖ * ‖(Lagrange.basis s z x).coeff (n : ℕ)‖ := by
        apply Finset.sum_le_sum
        intro n _
        rw [hcoeff]
        simpa only [norm_mul] using
          norm_sum_le s (fun x => y x * (Lagrange.basis s z x).coeff (n : ℕ))
      _ ≤ ∑ n : Fin q, (∑ x ∈ s, ‖y x‖) *
          (∑ x ∈ s, ‖(Lagrange.basis s z x).coeff (n : ℕ)‖) := by
        apply Finset.sum_le_sum
        intro n _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        gcongr
        exact Finset.single_le_sum (fun u hu => norm_nonneg (y u)) hx
      _ = K * ∑ x ∈ s, ‖y x‖ := by
        simp only [K]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        ring

/-- A finite scalar Fourier interpolation of the reciprocal function on two
finite real frequency arrays.

The certificate is deliberately independent of Hilbert spaces, matrix units,
singular values, and norms on operators.  Its coefficient mass is the finite
analogue of the total variation of the classical reciprocal Fourier measure. -/
def HasFiniteReciprocalFourierInterpolation
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (δ mass : ℝ) : Prop :=
  ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
    (∀ i j,
      (δ : ℂ) = (((α i - β j : ℝ) : ℂ)) *
        ∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)) ∧
    ∑ r, ‖a r‖ ≤ mass

/-- A finite Fourier sum that approximates the reciprocal function on two
finite real frequency arrays.  Unlike the exact certificate, the error is
measured before multiplication by the frequency difference. -/
def HasApproximateFiniteReciprocalFourierInterpolation
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (mass tolerance : ℝ) : Prop :=
  ∃ q : ℕ, ∃ a : Fin q → ℂ, ∃ t : Fin q → ℝ,
    (∀ i j,
      ‖(1 : ℂ) / (((α i - β j : ℝ) : ℂ)) -
        ∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)‖ ≤ tolerance) ∧
    ∑ r, ‖a r‖ ≤ mass

/-- A reciprocal interpolation on real coordinate matrix units after doubling
both Hilbert spaces.  Complex Fourier coefficients have been replaced by real
weights and coordinatewise orthogonal rotations. -/
def HasDoubledRealReciprocalOrbitInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    (delta mass : ℝ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ,
    ∃ U : Fin q → WithLp 2 (FR × FR) ≃ₗᵢ[ℝ] WithLp 2 (FR × FR),
      ∃ V : Fin q → WithLp 2 (ER × ER) ≃ₗᵢ[ℝ] WithLp 2 (ER × ER),
        (∀ i j,
          delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
            (alpha i - beta j) •
              ((∑ r, w r • unitaryOrbitAction (U r) (V r))
                (RectangularUnitarilyInvariantNorm.orthogonalBlockSum
                  (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)))) ∧
        ∑ r, |w r| ≤ mass

/-- An integrable scalar Fourier kernel representing the reciprocal function
outside the unit interval, with controlled `L¹` mass. -/
def HasIntegrableReciprocalFourierKernel (mass : ℝ) : Prop :=
  ∃ f : ℝ → ℂ,
    Measurable f ∧
    MeasureTheory.Integrable f ∧
    (∀ x : ℝ, 1 ≤ |x| →
      (∫ t, f t * Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        (1 : ℂ) / (x : ℂ)) ∧
    (∫ t, ‖f t‖) ≤ mass

/-- **The sharp reciprocal kernel exists.**  The explicit Haagerup--Zsidó
`α = 0` kernel is measurable and integrable, represents `1 / x` on the whole
exterior region `1 ≤ |x|`, and has `L¹` mass exactly `π / 2`. -/
theorem hasIntegrableReciprocalFourierKernel_pi_div_two :
    HasIntegrableReciprocalFourierKernel (Real.pi / 2) :=
  ⟨HaagerupZsido.reciprocalKernel,
    HaagerupZsido.measurable_reciprocalKernel,
    HaagerupZsido.integrable_reciprocalKernel,
    fun x hx => HaagerupZsido.reciprocalKernel_fourier x hx,
    HaagerupZsido.integral_norm_reciprocalKernel.le⟩

/-- An integrable reciprocal Fourier kernel yields finite Fourier sums of no
greater mass which uniformly approximate any prescribed finite frequency
array. -/
theorem hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {mass tolerance : ℝ}
    (hgap : ∀ i j, 1 ≤ |α i - β j|) (htolerance : 0 < tolerance)
    (hkernel : HasIntegrableReciprocalFourierKernel mass) :
    HasApproximateFiniteReciprocalFourierInterpolation
      α β mass tolerance := by
  classical
  rcases hkernel with ⟨f, hfmeas, hfint, hfourier, hmass⟩
  have hmass_nonneg : 0 ≤ mass :=
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _).trans hmass
  cases isEmpty_or_nonempty (Fin m) with
  | inl hm =>
      letI := hm
      exact ⟨0, Fin.elim0, Fin.elim0, (fun i => isEmptyElim i), by simpa⟩
  | inr hm =>
    letI := hm
    cases isEmpty_or_nonempty (Fin n) with
    | inl hn =>
        letI := hn
        exact ⟨0, Fin.elim0, Fin.elim0,
          (fun _i j => isEmptyElim j), by simpa⟩
    | inr hn =>
      letI := hn
      let M : ℝ := ∫ t, ‖f t‖
      let density : ℝ → ENNReal := fun t => ENNReal.ofReal ‖f t‖
      let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.withDensity density
      haveI : MeasureTheory.IsFiniteMeasure μ := by
        dsimp only [μ, density]
        exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hfint.norm.2
      let i₀ : Fin m := Classical.choice inferInstance
      let j₀ : Fin n := Classical.choice inferInstance
      let d₀ : ℝ := α i₀ - β j₀
      have hd₀ : d₀ ≠ 0 := by
        intro hd
        have := hgap i₀ j₀
        simp only [d₀, hd, abs_zero] at this
        norm_num at this
      have hMpos : 0 < M := by
        have hbound : ‖(1 : ℂ) / (d₀ : ℂ)‖ ≤ M := by
          rw [← hfourier d₀ (hgap i₀ j₀)]
          have hexpnorm (t : ℝ) :
              ‖Complex.exp ((((t * d₀ : ℝ) : ℂ) * Complex.I))‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          calc
            ‖∫ t, f t * Complex.exp ((((t * d₀ : ℝ) : ℂ) * Complex.I))‖ ≤
                ∫ t, ‖f t * Complex.exp ((((t * d₀ : ℝ) : ℂ) * Complex.I))‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
            _ = M := by
              dsimp only [M]
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with t
              rw [norm_mul, hexpnorm t, mul_one]
        exact lt_of_lt_of_le (norm_pos_iff.mpr (div_ne_zero one_ne_zero (by exact_mod_cast hd₀))) hbound
      have hMnonneg : 0 ≤ M := hMpos.le
      have hμreal : μ.real Set.univ = M := by
        rw [MeasureTheory.measureReal_def]
        simp only [μ, density, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
          MeasureTheory.setLIntegral_univ]
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint.norm
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
        exact ENNReal.toReal_ofReal hMnonneg
      have hμne : μ ≠ 0 := by
        intro hzero
        have : μ.real Set.univ = 0 := by simp [hzero]
        rw [hμreal] at this
        linarith
      letI : NeZero μ := ⟨hμne⟩
      let phase : ℝ → ℂ := fun t =>
        if f t = 0 then 0 else f t / (‖f t‖ : ℂ)
      have hphase_meas : Measurable phase := by
        dsimp only [phase]
        exact Measurable.ite
          (measurableSet_eq_fun hfmeas measurable_const)
          measurable_const (by fun_prop)
      have hphase_norm (t : ℝ) : ‖phase t‖ ≤ 1 := by
        by_cases ht : f t = 0
        · simp [phase, ht]
        · simp [phase, ht]
      have hnorm_mul_phase (t : ℝ) : (‖f t‖ : ℂ) * phase t = f t := by
        by_cases ht : f t = 0
        · simp [phase, ht]
        · simp only [phase, if_neg ht]
          field_simp [norm_ne_zero_iff.mpr ht]
      let atom : ℝ → (Fin m × Fin n → ℂ) := fun t ij =>
        phase t * Complex.exp
          ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I))
      have hatom_meas : Measurable atom := by
        apply measurable_pi_lambda
        intro ij
        dsimp only [atom]
        fun_prop
      have hatom_norm (t : ℝ) : ‖atom t‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro ij
        have hexpnorm :
            ‖Complex.exp
              ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I))‖ = 1 := by
          rw [Complex.norm_exp]
          simp
        simp only [atom, norm_mul, hexpnorm, mul_one]
        exact hphase_norm t
      have hatom_int : MeasureTheory.Integrable atom μ :=
        MeasureTheory.Integrable.of_bound hatom_meas.aestronglyMeasurable 1
          (Filter.Eventually.of_forall hatom_norm)
      have htolM : 0 < tolerance / M := div_pos htolerance hMpos
      rcases exists_finite_average_approximation μ atom hatom_int htolM with
        ⟨q, w, z, hw_nonneg, hw_sum, hquad⟩
      have hmoment (ij : Fin m × Fin n) :
          (∫ t, atom t ij ∂μ) =
            (1 : ℂ) / ((α ij.1 - β ij.2 : ℝ) : ℂ) := by
        change (∫ t, atom t ij ∂MeasureTheory.volume.withDensity density) = _
        rw [integral_withDensity_eq_integral_toReal_smul
          (by fun_prop)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ]
        rw [← hfourier (α ij.1 - β ij.2) (hgap ij.1 ij.2)]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        simp only [ENNReal.toReal_ofReal (norm_nonneg _), atom]
        calc
          ‖f t‖ • (phase t * Complex.exp
              ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I))) =
              ((‖f t‖ : ℂ) * phase t) * Complex.exp
                ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I)) := by
            rw [RCLike.real_smul_eq_coe_mul, ← mul_assoc]
            rfl
          _ = _ := congrArg (fun u : ℂ => u * Complex.exp
            ((((t * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I)))
              (hnorm_mul_phase t)
      let A : Fin m × Fin n → ℂ := ⨍ t, atom t ∂μ
      let Q : Fin m × Fin n → ℂ := ∑ r, w r • atom (z r)
      have hMA : M • A = ∫ t, atom t ∂μ := by
        dsimp only [A]
        rw [MeasureTheory.average_eq, hμreal, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hMpos), one_smul]
      have hA_moment (ij : Fin m × Fin n) :
          (M : ℂ) * A ij =
            (1 : ℂ) / ((α ij.1 - β ij.2 : ℝ) : ℂ) := by
        calc
          (M : ℂ) * A ij = (M • A) ij := by
            change (M : ℂ) * A ij = M • A ij
            exact (RCLike.real_smul_eq_coe_mul M (A ij)).symm
          _ = (∫ t, atom t ∂μ) ij := congrFun hMA ij
          _ = ∫ t, atom t ij ∂μ := by
            exact MeasureTheory.eval_integral
              (fun ij => hatom_int.eval ij) ij
          _ = _ := hmoment ij
      have hQ : dist Q A < tolerance / M := by
        exact hquad
      rw [dist_eq_norm] at hQ
      have hcoord (ij : Fin m × Fin n) :
          ‖Q ij - A ij‖ < tolerance / M := by
        exact (pi_norm_lt_iff htolM).mp hQ ij
      let a : Fin q → ℂ := fun r =>
        ((M * w r : ℝ) : ℂ) * phase (z r)
      have hsum (ij : Fin m × Fin n) :
          ∑ r, a r * Complex.exp
              ((((z r * (α ij.1 - β ij.2) : ℝ) : ℂ) * Complex.I)) =
            (M : ℂ) * Q ij := by
        simp only [a, Q, Finset.sum_apply, Pi.smul_apply,
          RCLike.real_smul_eq_coe_mul, atom]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        push_cast
        ac_rfl
      refine ⟨q, a, z, ?_, ?_⟩
      · intro i j
        rw [hsum (i, j), ← hA_moment (i, j)]
        calc
          ‖(M : ℂ) * A (i, j) - (M : ℂ) * Q (i, j)‖ =
              M * ‖A (i, j) - Q (i, j)‖ := by
            rw [← mul_sub, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg hMnonneg]
          _ ≤ M * (tolerance / M) := by
            apply (mul_lt_mul_of_pos_left _ hMpos).le
            simpa only [norm_sub_rev] using hcoord (i, j)
          _ = tolerance := by field_simp [ne_of_gt hMpos]
      · calc
          ∑ r, ‖a r‖ ≤ ∑ r, M * w r := by
            apply Finset.sum_le_sum
            intro r _
            simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hMnonneg, abs_of_nonneg (hw_nonneg r)]
            calc
              M * w r * ‖phase (z r)‖ ≤ M * w r * 1 := by
                exact mul_le_mul_of_nonneg_left (hphase_norm (z r))
                  (mul_nonneg hMnonneg (hw_nonneg r))
              _ = M * w r := mul_one _
          _ = M := by rw [← Finset.mul_sum, hw_sum, mul_one]
          _ ≤ mass := hmass

/-- Uniformly accurate finite reciprocal Fourier sums can be corrected to an
exact finite interpolation with arbitrarily small additional coefficient
mass.

The correction uses the fixed linear mass bound from
`exists_finite_fourier_interpolation_with_mass_bound` on the finite set of
distinct frequency differences. -/
theorem hasFiniteReciprocalFourierInterpolation_of_approximate
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {mass ε : ℝ}
    (hgap : ∀ i j, 1 ≤ |α i - β j|) (hε : 0 < ε)
    (happrox : ∀ η : ℝ, 0 < η →
      HasApproximateFiniteReciprocalFourierInterpolation α β mass η) :
    HasFiniteReciprocalFourierInterpolation α β 1 (mass + ε) := by
  classical
  let d : Fin m × Fin n → ℝ := fun ij => α ij.1 - β ij.2
  let s : Finset ℝ := (Finset.univ ×ˢ Finset.univ).image d
  obtain ⟨K, hK, hcorrect⟩ :=
    exists_finite_fourier_interpolation_with_mass_bound s
  let c : ℝ := s.card
  let η : ℝ := ε / ((K + 1) * (c + 1))
  have hc : 0 ≤ c := by positivity
  have hden : 0 < (K + 1) * (c + 1) :=
    mul_pos (by linarith) (by linarith)
  have hη : 0 < η := div_pos hε hden
  rcases happrox η hη with ⟨q₀, a₀, t₀, happ, hmass₀⟩
  let base : ℝ → ℂ := fun x => ∑ r, a₀ r * Complex.exp
    ((((t₀ r * x) : ℝ) : ℂ) * Complex.I)
  let y : ℝ → ℂ := fun x => (1 : ℂ) / (x : ℂ) - base x
  have hy (x : ℝ) (hx : x ∈ s) : ‖y x‖ ≤ η := by
    rcases Finset.mem_image.mp hx with ⟨⟨i, j⟩, _, rfl⟩
    simpa only [y, base, d] using happ i j
  have hysum : ∑ x ∈ s, ‖y x‖ ≤ c * η := by
    calc
      ∑ x ∈ s, ‖y x‖ ≤ ∑ _x ∈ s, η := by
        exact Finset.sum_le_sum fun x hx => hy x hx
      _ = c * η := by simp [c]
  rcases hcorrect y with ⟨q₁, a₁, t₁, hexact₁, hmass₁⟩
  have hsmall : K * (∑ x ∈ s, ‖y x‖) < ε := by
    have hnum : K * c < (K + 1) * (c + 1) := by nlinarith
    have hfrac : K * c / ((K + 1) * (c + 1)) < 1 :=
      (div_lt_one hden).2 hnum
    calc
      K * (∑ x ∈ s, ‖y x‖) ≤ K * (c * η) := by
        exact mul_le_mul_of_nonneg_left hysum hK
      _ = ε * (K * c / ((K + 1) * (c + 1))) := by
        dsimp only [η]
        field_simp
      _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one _
  refine ⟨q₀ + q₁, Fin.append a₀ a₁, Fin.append t₀ t₁, ?_, ?_⟩
  · intro i j
    let x : ℝ := α i - β j
    have hx : x ∈ s := by
      exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
    have hx₀ : x ≠ 0 := by
      intro hxz
      have := hgap i j
      change 1 ≤ |x| at this
      rw [hxz, abs_zero] at this
      norm_num at this
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx₀
    have hsum :
        (∑ r : Fin (q₀ + q₁),
          Fin.append a₀ a₁ r * Complex.exp
            (((Fin.append t₀ t₁ r * x : ℝ) : ℂ) * Complex.I)) =
          base x + ∑ r : Fin q₁, a₁ r * Complex.exp
            ((((t₁ r * x) : ℝ) : ℂ) * Complex.I) := by
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, base]
    have hrecip :
        (1 : ℂ) / (x : ℂ) = base x +
          ∑ r : Fin q₁, a₁ r * Complex.exp
            ((((t₁ r * x) : ℝ) : ℂ) * Complex.I) := by
      rw [← hexact₁ x hx]
      simp only [y]
      ring
    change (1 : ℂ) = (x : ℂ) * ∑ r : Fin (q₀ + q₁),
      Fin.append a₀ a₁ r * Complex.exp
        (((Fin.append t₀ t₁ r * x : ℝ) : ℂ) * Complex.I)
    rw [hsum, ← hrecip]
    field_simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    calc
      ∑ r, ‖a₀ r‖ + ∑ r, ‖a₁ r‖ ≤
          mass + K * (∑ x ∈ s, ‖y x‖) := add_le_add hmass₀ hmass₁
      _ ≤ mass + ε := by
        simpa only [add_comm] using (add_lt_add_left hsmall mass).le

/-- Approximate reciprocal Fourier sums with masses tending to `π / 2`
produce the exact normalized finite interpolation with mass `π / 2 + ε`.
All exact finite compression is discharged here; the remaining analytic input
only has to provide uniformly accurate finite sums. -/
theorem hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_approximate
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hgap : ∀ i j, 1 ≤ |α i - β j|) {ε : ℝ} (hε : 0 < ε)
    (happrox : ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η →
      HasApproximateFiniteReciprocalFourierInterpolation
        α β (Real.pi / 2 + μ) η) :
    HasFiniteReciprocalFourierInterpolation α β 1 (Real.pi / 2 + ε) := by
  have hhalf : 0 < ε / 2 := by positivity
  have h := hasFiniteReciprocalFourierInterpolation_of_approximate
    α β hgap hhalf (happrox (ε / 2) hhalf)
  convert h using 1
  ring

/-- A sharp integrable reciprocal kernel gives exact finite interpolation on
every separated finite frequency array, with arbitrarily small excess mass.

The kernel is first compressed to an approximate finite Fourier sum by
`hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel`.
The finite interpolation correction then removes every moment error exactly;
its coefficient cost tends to zero with the quadrature tolerance. -/
theorem hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hgap : ∀ i j, 1 ≤ |α i - β j|) {eps : ℝ} (heps : 0 < eps)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2)) :
    HasFiniteReciprocalFourierInterpolation
      α β 1 (Real.pi / 2 + eps) := by
  exact hasFiniteReciprocalFourierInterpolation_of_approximate
    α β hgap heps fun tolerance htolerance =>
      hasApproximateFiniteReciprocalFourierInterpolation_of_integrableKernel
        α β hgap htolerance hkernel

/-- Rescale a unit-gap finite Fourier interpolation to an arbitrary positive
gap.  The coefficient mass is unchanged and the Fourier frequencies are
divided by the gap. -/
theorem hasFiniteReciprocalFourierInterpolation_of_normalized
    {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    {δ mass : ℝ} (hδ : 0 < δ)
    (h : HasFiniteReciprocalFourierInterpolation
      (fun i => α i / δ) (fun j => β j / δ) 1 mass) :
    HasFiniteReciprocalFourierInterpolation α β δ mass := by
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  refine ⟨q, a, fun r => t r / δ, ?_, hmass⟩
  intro i j
  have harg (r : Fin q) :
      (t r / δ) * (α i - β j) =
        t r * (α i / δ - β j / δ) := by
    field_simp [ne_of_gt hδ]
  simp_rw [harg]
  let S : ℂ := ∑ r, a r * Complex.exp
    ((((t r * (α i / δ - β j / δ)) : ℝ) : ℂ) * Complex.I)
  have hs : (1 : ℂ) =
      (((α i / δ - β j / δ : ℝ) : ℂ)) * S := by
    simpa [S] using hscalar i j
  calc
    (δ : ℂ) = (δ : ℂ) * 1 := by ring
    _ = (δ : ℂ) *
        ((((α i / δ - β j / δ : ℝ) : ℂ)) * S) := by rw [hs]
    _ = (((α i - β j : ℝ) : ℂ)) * S := by
      push_cast
      field_simp [ne_of_gt hδ]

/-- A simultaneous finite orbit interpolation of the reciprocal coordinate
multiplier.

The same coefficients and unitary factors must work for every coordinate
matrix unit.  The displayed identity is written without division: multiplying
the orbit average by the coordinate difference gives `δ` times the matrix
unit.  Positive separation guarantees that this is equivalent to reciprocal
interpolation, while the division-free form is substantially more robust in
the downstream finite algebra. -/
def HasReciprocalOrbitInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    (δ mass : ℝ) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → 𝕜,
    ∃ U : Fin n → F ≃ₗᵢ[𝕜] F,
      ∃ V : Fin n → E ≃ₗᵢ[𝕜] E,
        (∀ i j,
          ((δ : 𝕜)) • basisMatrixUnit eF eE i j =
            ((((α i - β j : ℝ) : 𝕜)) •
              ((∑ r, a r • unitaryOrbitAction (U r) (V r))
                (basisMatrixUnit eF eE i j)))) ∧
        ∑ r, ‖a r‖ ≤ mass

/-- A finite scalar reciprocal Fourier interpolation produces the exact
simultaneous complex unitary-orbit interpolation.  All matrix-unit transport
is supplied by `complexUnitaryOrbitAction_basisMatrixUnit_exp_sub`; the input
certificate contains the whole remaining analytic content. -/
theorem hasReciprocalOrbitInterpolation_of_finiteFourierInterpolation
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    [FiniteDimensional ℂ FC]
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    {δ mass : ℝ}
    (h : HasFiniteReciprocalFourierInterpolation α β δ mass) :
    HasReciprocalOrbitInterpolation eF eE α β δ mass := by
  classical
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  let U : Fin q → FC ≃ₗᵢ[ℂ] FC := fun r =>
    basisDiagonalUnitary eF fun i => complexFourierPhase (t r * α i)
  let V : Fin q → EC ≃ₗᵢ[ℂ] EC := fun r =>
    basisDiagonalUnitary eE fun j => complexFourierPhase (-(t r * β j))
  refine ⟨q, a, U, V, ?_, hmass⟩
  intro i j
  have horbit :
      ((∑ r, a r • unitaryOrbitAction (U r) (V r))
          (basisMatrixUnit eF eE i j)) =
        (∑ r, a r * Complex.exp
          ((((t r * (α i - β j)) : ℝ) : ℂ) * Complex.I)) •
            basisMatrixUnit eF eE i j := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, U, V,
      complexUnitaryOrbitAction_basisMatrixUnit_exp_sub, smul_smul]
    rw [Finset.sum_smul]
  rw [horbit, smul_smul]
  exact congrArg (fun z : ℂ => z • basisMatrixUnit eF eE i j)
    (hscalar i j)

/-- A finite complex Fourier interpolation descends exactly to doubled real
coordinate spaces.  The complex coefficient norm is the real orbit weight and
its argument is absorbed into the left coordinate rotation. -/
theorem hasDoubledRealReciprocalOrbitInterpolation_of_finiteFourierInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {delta mass : ℝ}
    (h : HasFiniteReciprocalFourierInterpolation alpha beta delta mass) :
    HasDoubledRealReciprocalOrbitInterpolation
      eF eE alpha beta delta mass := by
  classical
  rcases h with ⟨q, a, t, hscalar, hmass⟩
  let w : Fin q → ℝ := fun r => ‖a r‖
  let U : Fin q → WithLp 2 (FR × FR) ≃ₗᵢ[ℝ] WithLp 2 (FR × FR) := fun r =>
    basisDoubledRealRotation eF fun i => Complex.arg (a r) + t r * alpha i
  let V : Fin q → WithLp 2 (ER × ER) ≃ₗᵢ[ℝ] WithLp 2 (ER × ER) := fun r =>
    basisDoubledRealRotation eE fun j => -(t r * beta j)
  refine ⟨q, w, U, V, ?_, ?_⟩
  · intro i j
    let T : ER →ₗ[ℝ] FR := basisMatrixUnit eF eE i j
    let d : ℝ := alpha i - beta j
    have horbit :
        ((∑ r, w r • unitaryOrbitAction (U r) (V r))
            (RectangularUnitarilyInvariantNorm.orthogonalBlockSum T T)) =
          doubledComplexScalarAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
      calc
        ((∑ r, w r • unitaryOrbitAction (U r) (V r))
            (RectangularUnitarilyInvariantNorm.orthogonalBlockSum T T)) =
            ∑ r, ‖a r‖ •
              doubledPhaseAction (Complex.arg (a r) + t r * d) T := by
                simp only [LinearMap.sum_apply, LinearMap.smul_apply, w]
                apply Finset.sum_congr rfl
                intro r _
                rw [unitaryOrbitAction_apply]
                change ‖a r‖ •
                    ((basisDoubledRealRotation eF
                        (fun i => Complex.arg (a r) + t r * alpha i)).toLinearMap ∘ₗ
                      RectangularUnitarilyInvariantNorm.orthogonalBlockSum T T ∘ₗ
                        (basisDoubledRealRotation eE
                          (fun j => -(t r * beta j))).toLinearMap) = _
                rw [show T = basisMatrixUnit eF eE i j by rfl,
                  basisDoubledRealRotation_comp_basisMatrixUnit]
                congr 2
                dsimp only [d]
                ring
        _ = doubledComplexScalarAction
            (∑ r, a r * Complex.exp ((((t r * d : ℝ) : ℂ) * Complex.I))) T := by
              exact sum_norm_smul_doubledPhaseAction_arg_add
                a (fun r => t r * d) T
    rw [← doubledComplexScalarAction_ofReal delta T, horbit,
      doubledComplexScalarAction_real_smul]
    congr 1
    exact hscalar i j
  · simpa only [w, abs_of_nonneg (norm_nonneg _)] using hmass

/-! ### The two-by-two real obstruction

The following theorems refute the exact *undoubled* real reciprocal orbit
interpolation at mass `π / 2`.  The frequency data is `α = (-1, 1)`,
`β = (0, 2)`, `δ = 1`, so the separation hypothesis holds with gap one, yet
any real certificate has coefficient mass at least `5 / 3 > π / 2`.

The reduction extracts, from the operator identity on each coordinate matrix
unit, the scalar identities `M i j = ∑ r, a r * u r i * v r j`, where
`u r i` and `v r j` are the diagonal matrix coefficients of the arbitrary
real orthogonal factors, hence bounded by one in absolute value.  Testing
the entrywise-reciprocal matrix `M = ![![-1, -1/3], ![1, -1]]` against the
functional `L X = (-X₀₀ - X₀₁ + X₁₀ - X₁₁) / 2`, whose value on every
rank-one atom `u vᵀ` with `‖u‖∞, ‖v‖∞ ≤ 1` is at most one while
`L M = 5 / 3`, forces the mass bound.  Because only diagonal matrix
coefficients of arbitrary orthogonal operators are used, no choice of
non-basis-diagonal real rotations can evade the argument. -/

/-- Left frequency array of the two-by-two obstruction: `(-1, 1)`. -/
def obstructionAlpha {n : ℕ} (i : Fin n) : ℝ :=
  if (i : ℕ) = 0 then -1 else 1

/-- Right frequency array of the two-by-two obstruction: `(0, 2)`. -/
def obstructionBeta {n : ℕ} (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then 0 else 2

/-- The obstruction data satisfies the unit separation hypothesis, so it is
admissible input for any claimed generic interpolation theorem. -/
theorem obstruction_gap {n : ℕ} (i j : Fin n) :
    1 ≤ |obstructionAlpha i - obstructionBeta j| := by
  unfold obstructionAlpha obstructionBeta
  by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0
  · rw [if_pos hi, if_pos hj, le_abs]
    right
    norm_num
  · rw [if_pos hi, if_neg hj, le_abs]
    right
    norm_num
  · rw [if_neg hi, if_pos hj, le_abs]
    left
    norm_num
  · rw [if_neg hi, if_neg hj, le_abs]
    right
    norm_num

/-- **Mass obstruction.**  Every undoubled real reciprocal orbit interpolation
certificate for the two-by-two obstruction data has coefficient mass at least
`5 / 3`. -/
theorem real_reciprocalOrbitInterpolation_mass_lower_bound
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G]
    (e : OrthonormalBasis (Fin (Module.finrank ℝ G)) ℝ G)
    (h2 : Module.finrank ℝ G = 2)
    {mass : ℝ}
    (hcert : HasReciprocalOrbitInterpolation e e
      obstructionAlpha obstructionBeta 1 mass) :
    (5 : ℝ) / 3 ≤ mass := by
  classical
  obtain ⟨n, a, U, V, hinterp, hmass⟩ := hcert
  let u : Fin n → Fin (Module.finrank ℝ G) → ℝ := fun r i =>
    ⟪e i, (U r).toLinearMap (e i)⟫_ℝ
  let v : Fin n → Fin (Module.finrank ℝ G) → ℝ := fun r j =>
    ⟪e j, (V r).toLinearMap (e j)⟫_ℝ
  have hu_le (r : Fin n) (i : Fin (Module.finrank ℝ G)) : |u r i| ≤ 1 := by
    have hnorm : ‖(U r).toLinearMap (e i)‖ = 1 := by
      change ‖(U r) (e i)‖ = 1
      rw [(U r).norm_map, e.norm_eq_one]
    calc
      |u r i| ≤ ‖e i‖ * ‖(U r).toLinearMap (e i)‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by rw [hnorm, e.norm_eq_one, one_mul]
  have hv_le (r : Fin n) (j : Fin (Module.finrank ℝ G)) : |v r j| ≤ 1 := by
    have hnorm : ‖(V r).toLinearMap (e j)‖ = 1 := by
      change ‖(V r) (e j)‖ = 1
      rw [(V r).norm_map, e.norm_eq_one]
    calc
      |v r j| ≤ ‖e j‖ * ‖(V r).toLinearMap (e j)‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by rw [hnorm, e.norm_eq_one, one_mul]
  have hterm (r : Fin n) (i j : Fin (Module.finrank ℝ G)) :
      ⟪e i, (unitaryOrbitAction (U r) (V r))
        (basisMatrixUnit e e i j) (e j)⟫_ℝ = u r i * v r j := by
    change ⟪e i, (U r).toLinearMap
      ((basisMatrixUnit e e i j) ((V r).toLinearMap (e j)))⟫_ℝ = _
    rw [basisMatrixUnit_apply, map_smul, real_inner_smul_right]
    exact mul_comm _ _
  have hscalar (i j : Fin (Module.finrank ℝ G)) :
      (1 : ℝ) = (obstructionAlpha i - obstructionBeta j) *
        ∑ r, a r * (u r i * v r j) := by
    have h := congrArg (fun T : G →ₗ[ℝ] G => ⟪e i, T (e j)⟫_ℝ) (hinterp i j)
    rw [LinearMap.smul_apply, LinearMap.smul_apply, real_inner_smul_right,
      real_inner_smul_right, basisMatrixUnit_apply, e.inner_eq_one, one_smul,
      e.inner_eq_one, LinearMap.sum_apply, LinearMap.sum_apply, inner_sum] at h
    calc
      (1 : ℝ) = (1 : ℝ) * 1 := (mul_one 1).symm
      _ = (obstructionAlpha i - obstructionBeta j) *
          ∑ r, ⟪e i, (a r • unitaryOrbitAction (U r) (V r))
            (basisMatrixUnit e e i j) (e j)⟫_ℝ := h
      _ = (obstructionAlpha i - obstructionBeta j) *
          ∑ r, a r * (u r i * v r j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        rw [LinearMap.smul_apply, LinearMap.smul_apply,
          real_inner_smul_right, hterm r i j]
  have hzero : (0 : ℕ) < Module.finrank ℝ G := by omega
  have hone : (1 : ℕ) < Module.finrank ℝ G := by omega
  set i₀ : Fin (Module.finrank ℝ G) := ⟨0, hzero⟩ with hi₀
  set i₁ : Fin (Module.finrank ℝ G) := ⟨1, hone⟩ with hi₁
  have hS00 : (∑ r, a r * (u r i₀ * v r i₀)) = -1 := by
    have h := hscalar i₀ i₀
    rw [show obstructionAlpha i₀ - obstructionBeta i₀ = -1 by
      simp [obstructionAlpha, obstructionBeta, hi₀]] at h
    linarith
  have hS01 : (∑ r, a r * (u r i₀ * v r i₁)) = -(1 / 3) := by
    have h := hscalar i₀ i₁
    rw [show obstructionAlpha i₀ - obstructionBeta i₁ = -3 by
      simp [obstructionAlpha, obstructionBeta, hi₀, hi₁]
      norm_num] at h
    linarith
  have hS10 : (∑ r, a r * (u r i₁ * v r i₀)) = 1 := by
    have h := hscalar i₁ i₀
    rw [show obstructionAlpha i₁ - obstructionBeta i₀ = 1 by
      simp [obstructionAlpha, obstructionBeta, hi₀, hi₁]] at h
    linarith
  have hS11 : (∑ r, a r * (u r i₁ * v r i₁)) = -1 := by
    have h := hscalar i₁ i₁
    rw [show obstructionAlpha i₁ - obstructionBeta i₁ = -1 by
      simp [obstructionAlpha, obstructionBeta, hi₁]
      norm_num] at h
    linarith
  let ℓ : Fin n → ℝ := fun r =>
    (u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)) / 2
  have hLval : (∑ r, a r * ℓ r) = 5 / 3 := by
    have hsplit : (∑ r, a r * ℓ r) =
        ((∑ r, a r * (u r i₁ * v r i₀)) - (∑ r, a r * (u r i₁ * v r i₁)) -
          (∑ r, a r * (u r i₀ * v r i₀)) -
          (∑ r, a r * (u r i₀ * v r i₁))) / 2 := by
      rw [eq_div_iff (two_ne_zero (α := ℝ)), Finset.sum_mul,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      simp only [ℓ]
      ring
    rw [hsplit, hS00, hS01, hS10, hS11]
    norm_num
  have hℓ_le (r : Fin n) : |ℓ r| ≤ 1 := by
    obtain ⟨hv0l, hv0r⟩ := abs_le.mp (hv_le r i₀)
    obtain ⟨hv1l, hv1r⟩ := abs_le.mp (hv_le r i₁)
    have hsum2 : |v r i₀ - v r i₁| + |v r i₀ + v r i₁| ≤ 2 := by
      rcases abs_cases (v r i₀ - v r i₁) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases (v r i₀ + v r i₁) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e1, e2] <;> linarith
    have hnum : |u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)| ≤ 2 := by
      calc
        |u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)| ≤
            |u r i₁ * (v r i₀ - v r i₁)| + |u r i₀ * (v r i₀ + v r i₁)| :=
          abs_sub _ _
        _ = |u r i₁| * |v r i₀ - v r i₁| + |u r i₀| * |v r i₀ + v r i₁| := by
          rw [abs_mul, abs_mul]
        _ ≤ 1 * |v r i₀ - v r i₁| + 1 * |v r i₀ + v r i₁| := by
          gcongr
          · exact hu_le r i₁
          · exact hu_le r i₀
        _ = |v r i₀ - v r i₁| + |v r i₀ + v r i₁| := by ring
        _ ≤ 2 := hsum2
    simp only [ℓ]
    rw [abs_div, abs_two, div_le_one (by norm_num : (0 : ℝ) < 2)]
    exact hnum
  have habs : |∑ r, a r * ℓ r| ≤ ∑ r, |a r| := by
    calc
      |∑ r, a r * ℓ r| ≤ ∑ r, |a r * ℓ r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, |a r| := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hℓ_le r)
  rw [hLval] at habs
  have hmass' : (∑ r, |a r|) ≤ mass := by
    calc
      (∑ r, |a r|) = ∑ r, ‖a r‖ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Real.norm_eq_abs]
      _ ≤ mass := hmass
  calc
    (5 : ℝ) / 3 = |(5 : ℝ) / 3| := by norm_num
    _ ≤ ∑ r, |a r| := habs
    _ ≤ mass := hmass'

/-- **The exact undoubled real reciprocal orbit interpolation at mass `π / 2`
is refuted.**  The separation hypotheses are satisfiable (`obstruction_gap`
with `δ = 1 > 0`), yet no certificate of mass `π / 2` exists because
`π / 2 < 5 / 3`. -/
theorem not_real_reciprocalOrbitInterpolation_pi_div_two
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G]
    (e : OrthonormalBasis (Fin (Module.finrank ℝ G)) ℝ G)
    (h2 : Module.finrank ℝ G = 2) :
    ¬ HasReciprocalOrbitInterpolation e e
      obstructionAlpha obstructionBeta 1 (Real.pi / 2) := by
  intro hcert
  have h53 := real_reciprocalOrbitInterpolation_mass_lower_bound e h2 hcert
  nlinarith [Real.pi_lt_d2]

/-- The concrete two-dimensional Euclidean orthonormal basis witnessing the
obstruction. -/
noncomputable def obstructionBasis :
    OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) ℝ
      (EuclideanSpace ℝ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).reindex
    (finCongr finrank_euclideanSpace_fin.symm)

/-- Fully concrete refutation on `EuclideanSpace ℝ (Fin 2)`: the hypotheses
of the previously conjectured generic undoubled interpolation are satisfied,
but its conclusion fails. -/
theorem not_hasReciprocalOrbitInterpolation_pi_div_two_euclidean :
    ¬ HasReciprocalOrbitInterpolation obstructionBasis obstructionBasis
      obstructionAlpha obstructionBeta 1 (Real.pi / 2) :=
  not_real_reciprocalOrbitInterpolation_pi_div_two obstructionBasis
    finrank_euclideanSpace_fin

/-- **Finite harmonic-analysis root.**  Separated finite real frequencies admit
a simultaneous reciprocal orbit interpolation of mass at most `π / 2`.

This statement contains no unknown rectangular map, no singular values, and no
unitarily invariant norm.  Its data are only finite real frequency arrays,
coordinate matrix units, and a common finite unitary representation of their
reciprocal multiplier.

Status: this declaration remains an open obligation, but it is no longer on
the critical path of the sharp real and complex results.  The explicit
Haagerup--Zsidó kernel now proves
`hasIntegrableReciprocalFourierKernel_pi_div_two`, and the unconditional
endpoints `kyFan_reciprocalMultiplier_le_complex`,
`kyFan_reciprocalMultiplier_le_real`, and the field-specific Sylvester
theorems are derived from it through certificates of mass `π / 2 + ε` for
every positive `ε`.  Only the generic `RCLike` statements still route through
this declaration.

What is genuinely missing is exact attainment at mass `π / 2` for a *finite*
orbit certificate, uniformly in the scalar field:

1. For `𝕜 = ℂ`, fix the finite arrays and consider the map sending a finite
   Fourier certificate to its matrix of coordinate multiplier values in
   `ℂ^(m × n)`.  The `π / 2 + ε` certificates witness that the reciprocal
   value matrix lies in `(π / 2 + ε) K` for every `ε > 0`, where `K` is the
   absolutely convex hull of the compact set of phase-orbit value matrices.
   In finite dimension `K` is compact, hence closed, so the intersection over
   `ε` places the value matrix in `(π / 2) K`; finite-dimensional
   Carathéodory then recovers a finite certificate of mass at most `π / 2`.
2. For `𝕜 = ℝ` the `π / 2 + ε` certificates currently exist only on the
   doubled spaces (`HasDoubledRealReciprocalOrbitInterpolation`), not for
   this undoubled real orbit statement, because real diagonal unitaries carry
   only signs, not phases.  A real proof must either produce genuinely real
   finite certificates (for example from rotation pairs that are not
   basis-diagonal) or reformulate the generic root at the doubled level.

Do not obtain this theorem from the downstream Ky Fan or orbit-convexity
statements, since that would create a dependency cycle, and do not replace it
with an assumption of equivalent content. -/
theorem hasReciprocalOrbitInterpolation_pi_div_two
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|) :
    HasReciprocalOrbitInterpolation eF eE α β δ (Real.pi / 2) := by
  sorry

/-- Convert the basis orientation used by the coordinate expansion into the
orientation used by the Sylvester coefficient equation. -/
private theorem basisFirst_coefficient_equation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F}
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) :
    (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
        ⟪eF i, X (eE j)⟫_𝕜 =
      ⟪eF i, C (eE j)⟫_𝕜 := by
  simpa only [map_mul, map_sub, RCLike.conj_ofReal, inner_conj_symm] using
    congrArg (starRingEnd 𝕜) (hcoeff i j)

/-- A simultaneous reciprocal orbit interpolation turns the entrywise
Sylvester relation into an exact finite two-sided unitary-orbit certificate. -/
theorem finiteUnitaryOrbitCertificate_of_reciprocalInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ mass : ℝ}
    (hinterp : HasReciprocalOrbitInterpolation eF eE α β δ mass)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜) :
    RectangularUnitarilyInvariantNorm.HasFiniteUnitaryOrbitCertificate
      mass (((δ : 𝕜)) • X) C := by
  classical
  rcases hinterp with ⟨n, a, U, V, hinterp, hmass⟩
  let S : (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) :=
    ∑ r, a r • unitaryOrbitAction (U r) (V r)
  have hS_unit (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((δ : 𝕜)) • basisMatrixUnit eF eE i j =
        ((((α i - β j : ℝ) : 𝕜)) •
          S (basisMatrixUnit eF eE i j)) := by
    exact hinterp i j
  have hcoeff' (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((((α i - β j : ℝ) : 𝕜)) *
          ⟪eF i, X (eE j)⟫_𝕜) =
        ⟪eF i, C (eE j)⟫_𝕜 := by
    simpa only [RCLike.ofReal_sub] using
      basisFirst_coefficient_equation eF eE α β hcoeff i j
  refine ⟨n, a, U, V, ?_, hmass⟩
  have hX := sum_basisMatrixUnit eF eE X
  have hC := sum_basisMatrixUnit eF eE C
  calc
    ((δ : 𝕜)) • X =
        ((δ : 𝕜)) •
          (∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
            basisMatrixUnit eF eE i j) := by rw [← hX]
    _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
          (((δ : 𝕜)) • basisMatrixUnit eF eE i j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, smul_smul, mul_comm]
    _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
          (((((α i - β j : ℝ) : 𝕜)) •
            S (basisMatrixUnit eF eE i j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hS_unit i j]
    _ = ∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
          S (basisMatrixUnit eF eE i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hcoeff' i j]
      rw [smul_smul, mul_comm]
    _ = S (∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
          basisMatrixUnit eF eE i j) := by
      simp only [map_sum, map_smul]
    _ = S C := by rw [← hC]
    _ = ∑ r, a r •
        ((U r).toLinearMap ∘ₗ C ∘ₗ (V r).toLinearMap) := by
      simp only [S, LinearMap.sum_apply, LinearMap.smul_apply,
        unitaryOrbitAction_apply]

/-- A doubled-real reciprocal interpolation recombines from matrix units into
an exact finite orthogonal-orbit certificate for arbitrary real maps. -/
theorem finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_reciprocalInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {X C : ER →ₗ[ℝ] FR} {delta mass : ℝ}
    (hinterp : HasDoubledRealReciprocalOrbitInterpolation
      eF eE alpha beta delta mass)
    (hcoeff : ∀ i j,
      (alpha i - beta j) * ⟪X (eE j), eF i⟫_ℝ =
        ⟪C (eE j), eF i⟫_ℝ) :
    RectangularUnitarilyInvariantNorm.HasFiniteUnitaryOrbitCertificate
      mass
      (delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum X X)
      (RectangularUnitarilyInvariantNorm.orthogonalBlockSum C C) := by
  classical
  rcases hinterp with ⟨q, w, U, V, hinterp, hmass⟩
  let S :
      (WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR)) →ₗ[ℝ]
        (WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR)) :=
    ∑ r, w r • unitaryOrbitAction (U r) (V r)
  have hunit (i : Fin (Module.finrank ℝ FR))
      (j : Fin (Module.finrank ℝ ER)) :
      delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
        (alpha i - beta j) •
          S (RectangularUnitarilyInvariantNorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
    exact hinterp i j
  have hcoeff' (i : Fin (Module.finrank ℝ FR))
      (j : Fin (Module.finrank ℝ ER)) :
      (alpha i - beta j) * ⟪eF i, X (eE j)⟫_ℝ =
        ⟪eF i, C (eE j)⟫_ℝ := by
    simpa only [real_inner_comm] using hcoeff i j
  let blockDiagonal :
      (ER →ₗ[ℝ] FR) →ₗ[ℝ]
        (WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR)) := by
    refine
      { toFun := fun A =>
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum A A
        map_add' := ?_
        map_smul' := ?_ }
    · intro A B
      ext x
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [RectangularUnitarilyInvariantNorm.orthogonalBlockSum_apply]
    · intro r A
      exact RectangularUnitarilyInvariantNorm.orthogonalBlockSum_smul r A A
  have hblock (A : ER →ₗ[ℝ] FR) :
      RectangularUnitarilyInvariantNorm.orthogonalBlockSum A A =
        ∑ i, ∑ j, ⟪eF i, A (eE j)⟫_ℝ •
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
    change blockDiagonal A = _
    conv_lhs => rw [sum_basisMatrixUnit eF eE A]
    simp only [map_sum, map_smul, blockDiagonal]
    rfl
  refine ⟨q, w, U, V, ?_, ?_⟩
  · calc
      delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum X X =
          delta • ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            RectangularUnitarilyInvariantNorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
        rw [hblock X]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            (delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul, smul_smul, mul_comm]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            ((alpha i - beta j) •
              S (RectangularUnitarilyInvariantNorm.orthogonalBlockSum
                (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hunit i j]
      _ = ∑ i, ∑ j, ⟪eF i, C (eE j)⟫_ℝ •
            S (RectangularUnitarilyInvariantNorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← hcoeff' i j, smul_smul, mul_comm]
      _ = S (∑ i, ∑ j, ⟪eF i, C (eE j)⟫_ℝ •
            RectangularUnitarilyInvariantNorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        simp only [map_sum, map_smul]
      _ = S (RectangularUnitarilyInvariantNorm.orthogonalBlockSum C C) := by
        rw [← hblock C]
      _ = ∑ r, w r • ((U r).toLinearMap ∘ₗ
          RectangularUnitarilyInvariantNorm.orthogonalBlockSum C C ∘ₗ
            (V r).toLinearMap) := by
        simp only [S, LinearMap.sum_apply, LinearMap.smul_apply,
          unitaryOrbitAction_apply]
  · simpa only [Real.norm_eq_abs] using hmass

/-- Approximate finite scalar Fourier interpolations with masses tending to
`π / 2` imply the sharp complex Ky Fan reciprocal-multiplier estimate.

This formulation matches the classical extremal result, whose sharp constant
is an infimum.  No attaining Fourier density and no compactness argument for
the family of frequencies is required: apply the finite orbit estimate at
mass `π / 2 + ε`, then let `ε` decrease to zero in `ℝ`. -/
theorem kyFan_reciprocalMultiplier_le_complex_of_approximateFourierInterpolation
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    [FiniteDimensional ℂ FC]
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    {X C : EC →ₗ[ℂ] FC} {δ : ℝ} (hδ : 0 < δ)
    (hfourier : ∀ ε : ℝ, 0 < ε →
      HasFiniteReciprocalFourierInterpolation
        α β δ (Real.pi / 2 + ε))
    (hcoeff : ∀ i j,
      (((α i : ℝ) : ℂ) - ((β j : ℝ) : ℂ)) *
          ⟪X (eE j), eF i⟫_ℂ =
        ⟪C (eE j), eF i⟫_ℂ)
    (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  let K := RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C
  have hK0 : 0 ≤ K := by
    dsimp [K, RectangularUnitarilyInvariantNorm.rectangularKyFanSum]
    exact Finset.sum_nonneg fun i _ => C.singularValues_nonneg (i : ℕ)
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (K + 1)
  have hdenom : 0 < K + 1 := by positivity
  have hε : 0 < ε := div_pos hη hdenom
  have hinterp :=
    hasReciprocalOrbitInterpolation_of_finiteFourierInterpolation
      eF eE α β (hfourier ε hε)
  have hcert := finiteUnitaryOrbitCertificate_of_reciprocalInterpolation
    eF eE α β hinterp hcoeff
  have hbound :=
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum_le_of_finiteUnitaryOrbitCertificate
      k hcert
  rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
    k X hδ.le] at hbound
  have hεK : ε * K ≤ η := by
    rw [show ε = η / (K + 1) by rfl, div_mul_eq_mul_div,
      div_le_iff₀ hdenom]
    nlinarith
  calc
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
        (Real.pi / 2 + ε) * K := hbound
    _ = (Real.pi / 2) * K + ε * K := by ring
    _ ≤ (Real.pi / 2) * K + η := by gcongr

/-- Approximate finite scalar Fourier interpolations imply the sharp real Ky
Fan estimate.  Complex coefficients first descend to orthogonal actions on two
real copies; duplication of every singular value then cancels the factor two. -/
theorem kyFan_reciprocalMultiplier_le_real_of_approximateFourierInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {X C : ER →ₗ[ℝ] FR} {delta : ℝ} (hdelta : 0 < delta)
    (hfourier : ∀ eps : ℝ, 0 < eps →
      HasFiniteReciprocalFourierInterpolation
        alpha beta delta (Real.pi / 2 + eps))
    (hcoeff : ∀ i j,
      (alpha i - beta j) * ⟪X (eE j), eF i⟫_ℝ =
        ⟪C (eE j), eF i⟫_ℝ)
    (k : ℕ) :
    delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  let K := RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C
  have hK0 : 0 ≤ K := by
    dsimp [K, RectangularUnitarilyInvariantNorm.rectangularKyFanSum]
    exact Finset.sum_nonneg fun i _ => C.singularValues_nonneg (i : ℕ)
  apply le_of_forall_pos_le_add
  intro eta heta
  let eps := eta / (K + 1)
  have hdenom : 0 < K + 1 := by positivity
  have heps : 0 < eps := div_pos heta hdenom
  have hinterp :=
    hasDoubledRealReciprocalOrbitInterpolation_of_finiteFourierInterpolation
      eF eE alpha beta (hfourier eps heps)
  have hcert :=
    finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_reciprocalInterpolation
      eF eE alpha beta hinterp hcoeff
  have hbound :=
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum_le_of_finiteUnitaryOrbitCertificate
      (2 * k) hcert
  have hscale :
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum (2 * k)
          (delta • RectangularUnitarilyInvariantNorm.orthogonalBlockSum X X) =
        delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum (2 * k)
          (RectangularUnitarilyInvariantNorm.orthogonalBlockSum X X) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      (RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
        (𝕜 := ℝ) (2 * k)
        (RectangularUnitarilyInvariantNorm.orthogonalBlockSum X X) hdelta.le)
  rw [hscale,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum_orthogonalBlockSum_self,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum_orthogonalBlockSum_self]
      at hbound
  have hbound' :
      delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
        (Real.pi / 2 + eps) * K := by
    dsimp only [K] at hbound ⊢
    nlinarith
  have hepsK : eps * K ≤ eta := by
    rw [show eps = eta / (K + 1) by rfl, div_mul_eq_mul_div,
      div_le_iff₀ hdenom]
    nlinarith
  calc
    delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
        (Real.pi / 2 + eps) * K := hbound'
    _ = (Real.pi / 2) * K + eps * K := by ring
    _ ≤ (Real.pi / 2) * K + eta := by gcongr

/-- A sharp integrable reciprocal kernel implies the unconditional complex
Ky Fan reciprocal-multiplier estimate.

The scalar kernel is compressed and corrected only after the finite spectral
differences are known.  The resulting certificates have mass
`pi / 2 + eps`; the preceding theorem removes `eps` at the level of the real
Ky Fan inequality. -/
theorem kyFan_reciprocalMultiplier_le_complex_of_integrableKernel
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    [FiniteDimensional ℂ FC]
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    {X C : EC →ₗ[ℂ] FC} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2))
    (hcoeff : ∀ i j,
      (((α i : ℝ) : ℂ) - ((β j : ℝ) : ℂ)) *
          ⟪X (eE j), eF i⟫_ℂ =
        ⟪C (eE j), eF i⟫_ℂ)
    (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_complex_of_approximateFourierInterpolation
    eF eE α β hδ _ hcoeff k
  intro eps heps
  apply hasFiniteReciprocalFourierInterpolation_of_normalized α β hδ
  apply hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    (fun i => α i / δ) (fun j => β j / δ) _ heps hkernel
  intro i j
  rw [show α i / δ - β j / δ = (α i - β j) / δ by ring]
  rw [abs_div, abs_of_pos hδ]
  exact (le_div_iff₀ hδ).2 (by simpa using hgap i j)

/-- A sharp integrable reciprocal kernel implies the sharp real Ky Fan
estimate through doubled orthogonal rotations and singular-value descent. -/
theorem kyFan_reciprocalMultiplier_le_real_of_integrableKernel
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {X C : ER →ₗ[ℝ] FR} {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ i j, delta ≤ |alpha i - beta j|)
    (hkernel : HasIntegrableReciprocalFourierKernel (Real.pi / 2))
    (hcoeff : ∀ i j,
      (alpha i - beta j) * ⟪X (eE j), eF i⟫_ℝ =
        ⟪C (eE j), eF i⟫_ℝ)
    (k : ℕ) :
    delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_real_of_approximateFourierInterpolation
    eF eE alpha beta hdelta _ hcoeff k
  intro eps heps
  apply hasFiniteReciprocalFourierInterpolation_of_normalized alpha beta hdelta
  apply hasFiniteReciprocalFourierInterpolation_pi_div_two_add_eps_of_integrableKernel
    (fun i => alpha i / delta) (fun j => beta j / delta) _ heps hkernel
  intro i j
  rw [show alpha i / delta - beta j / delta =
    (alpha i - beta j) / delta by ring]
  rw [abs_div, abs_of_pos hdelta]
  exact (le_div_iff₀ hdelta).2 (by simpa using hgap i j)

/-- **Unconditional sharp complex Ky Fan reciprocal-multiplier estimate.**
The explicit Haagerup--Zsidó kernel supplies the analytic certificate; no
open assumption remains. -/
theorem kyFan_reciprocalMultiplier_le_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    [FiniteDimensional ℂ FC]
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    {X C : EC →ₗ[ℂ] FC} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : ℂ) - ((β j : ℝ) : ℂ)) *
          ⟪X (eE j), eF i⟫_ℂ =
        ⟪C (eE j), eF i⟫_ℂ)
    (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
  kyFan_reciprocalMultiplier_le_complex_of_integrableKernel eF eE α β hδ hgap
    hasIntegrableReciprocalFourierKernel_pi_div_two hcoeff k

/-- **Unconditional sharp real Ky Fan reciprocal-multiplier estimate**,
through the doubled orthogonal descent from the explicit complex kernel. -/
theorem kyFan_reciprocalMultiplier_le_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [FiniteDimensional ℝ FR]
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {X C : ER →ₗ[ℝ] FR} {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ i j, delta ≤ |alpha i - beta j|)
    (hcoeff : ∀ i j,
      (alpha i - beta j) * ⟪X (eE j), eF i⟫_ℝ =
        ⟪C (eE j), eF i⟫_ℝ)
    (k : ℕ) :
    delta * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
  kyFan_reciprocalMultiplier_le_real_of_integrableKernel eF eE alpha beta
    hdelta hgap hasIntegrableReciprocalFourierKernel_pi_div_two hcoeff k

/-- Every finite reciprocal multiplier with gap `δ` satisfies the sharp
simultaneous Ky Fan prefix estimate.  All operator and singular-value content
is discharged from the finite orbit interpolation certificate. -/
theorem kyFan_reciprocalMultiplier_le
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  have hcert := finiteUnitaryOrbitCertificate_of_reciprocalInterpolation
    eF eE α β
    (hasReciprocalOrbitInterpolation_pi_div_two eF eE α β hδ hgap)
    hcoeff
  have hbound :=
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum_le_of_finiteUnitaryOrbitCertificate
      k hcert
  have hδ0 : 0 ≤ δ := hδ.le
  rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
    k X hδ0] at hbound
  exact hbound

end DavisKahanTheory
end ForMathlib
