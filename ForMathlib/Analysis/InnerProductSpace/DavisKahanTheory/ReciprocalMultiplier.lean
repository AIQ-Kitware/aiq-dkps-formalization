/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm

/-!
# Finite reciprocal multipliers

This file isolates the harmonic-analysis core of the finite
Bhatia--Davis--McIntosh Sylvester estimate.

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

/-- **Finite harmonic-analysis root.**  Separated finite real frequencies admit
a simultaneous reciprocal orbit interpolation of mass at most `π / 2`.

This statement contains no unknown rectangular map, no singular values, and no
unitarily invariant norm.  Its data are only finite real frequency arrays,
coordinate matrix units, and a common finite unitary representation of their
reciprocal multiplier.

The complex construction should come from the extremal Fourier--Stieltjes
representation of `1 / x` off `[-1, 1]`, with total variation `π / 2`, by
using diagonal phase unitaries in `eF` and `eE`.  The real case must be handled
honestly: either realify that phase representation through finite orthogonal
rotations and finite convex decomposition, or prove a real certificate with
the same mass directly.  Do not obtain this theorem from the downstream Ky Fan
or orbit-convexity statements, since that would create a dependency cycle. -/
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
