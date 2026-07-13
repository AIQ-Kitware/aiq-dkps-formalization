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

open scoped InnerProductSpace BigOperators

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
