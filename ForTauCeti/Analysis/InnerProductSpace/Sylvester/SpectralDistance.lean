/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Pairwise

/-!
# Sylvester estimates for arbitrary separated spectra

Finite orbit certificates and the sharp constant-one Frobenius estimate over
real and complex scalars. The pairwise `pi / 2` Ky Fan and arbitrary-UI-norm
foundations are consumed directly from accepted TauCeti `Sylvester.Pairwise`
(#24932, independent upstream proof); the former local forwarding declarations
are retired. The separate coordinate reciprocal-multiplier results remain in
`Sylvester.Internal.ReciprocalMultiplier`.

## Provenance

Originally developed in `DavisKahan/FiniteDimensional/Sylvester/SpectralDistance.lean`.
The reciprocal-multiplier estimate and rectangular Fan dominance are shared by
all scalar fields covered by `RCLike`.

-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Arbitrary disjoint spectra

The Bhatia--Davis--McIntosh extension is factored through the simultaneous Ky
Fan prefix estimate and rectangular Fan dominance.
-/

/-- In orthonormal eigenbases the Sylvester equation is the scalar identity
`(alpha i - beta j) * X i j = C i j`. -/
theorem sylvester_eigenbasis_coefficient_equation
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
        ⟪X (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 =
      ⟪C (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 := by
  have hpoint := LinearMap.congr_fun hEq (hB.eigenvectorBasis rfl j)
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change A (X (hB.eigenvectorBasis rfl j)) -
      X (B (hB.eigenvectorBasis rfl j)) =
        C (hB.eigenvectorBasis rfl j) at hpoint
  have hinner :
      ⟪X (hB.eigenvectorBasis rfl j),
          A (hA.eigenvectorBasis rfl i)⟫_𝕜 -
        ⟪X (B (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 =
        ⟪C (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    calc
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 -
          ⟪X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [← hA (X (hB.eigenvectorBasis rfl j))
          (hA.eigenvectorBasis rfl i)]
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)) -
          X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [inner_sub_left]
      _ = _ := congrArg
        (fun z : F => ⟪z, hA.eigenvectorBasis rfl i⟫_𝕜) hpoint
  simpa only [hA.apply_eigenvectorBasis rfl i,
    hB.apply_eigenvectorBasis rfl j, map_smul, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, sub_mul] using hinner

/-- Restrict scalars on the Sylvester map space from `𝕜` to `ℝ` so the
barycentric theorem can state real convex-hull membership. -/
local instance realModuleSylvesterMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

/-- The scaled solution of a separated self-adjoint Sylvester equation is a
bounded-mass multiple of a point in the real convex hull of the two-sided
unitary orbit of the defect.

The analytic work is exactly the simultaneous Ky Fan estimate above.  The
rectangular orbit-convexity theorem then converts weak singular-value
majorization into real convex-hull membership uniformly over `ℝ` and `ℂ`.
This avoids placing Fourier integration, phase absorption, normalization, or a
separate real-field descent inside the barycentric theorem.

We choose the maximal allowed mass `p = π / 2` and normalize
`Y = p⁻¹ • (δ • X)`.  Positive homogeneity and the analytic Ky Fan estimate
-- states the goal with the definition unfolded, in the shape the next step needs;
-- there is no `_apply` lemma to rewrite with here.
show every prefix of `Y` is bounded by the corresponding prefix of `C`;
rectangular Fan orbit-convexity gives `Y ∈ conv(orbit(C))`, and the defining
scalar identity recovers `δ • X = p • Y`. -/
theorem sylvester_barycentricOrbitRepresentation_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ Real.pi / 2 ∧
      ∃ Y : E →ₗ[𝕜] F,
        Y ∈ convexHull ℝ
          (LinearMap.twoSidedUnitaryOrbit C) ∧
        (((δ : 𝕜)) • X) = ((m : 𝕜)) • Y := by
  let p : ℝ := Real.pi / 2
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp0 : 0 ≤ p := le_of_lt hp
  have hpinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  let Y : E →ₗ[𝕜] F := (((p⁻¹ : ℝ) : 𝕜)) • (((δ : 𝕜)) • X)
  refine ⟨p, hp0, le_rfl, Y, ?_, ?_⟩
  · let : Module ℝ F := Module.compHom F (algebraMap ℝ 𝕜)
    let : IsScalarTower ℝ 𝕜 F := IsScalarTower.of_compHom ℝ 𝕜 F
    rw [← LinearMap.twoSidedUnitaryOrbitHull_eq_convexHull]
    apply LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr
    intro k
    have hcore := ContinuousLinearMap.mul_kyFanSum_le_pi_div_two_mul_kyFanSum_sylvester_apply
      (A := A.toContinuousLinearMap) (B := B.toContinuousLinearMap) hA hB
      (Module.End.pointSpectraSeparated_iff.mpr fun lam hlam μ hμ => hgap lam μ hlam hμ)
      X.toContinuousLinearMap k
    simp only [ContinuousLinearMap.sylvester_apply, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap, hEq] at hcore
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change δ *
        X.kyFanSum k ≤
      p * C.kyFanSum k at hcore
    calc
      Y.kyFanSum k =
          p⁻¹ * (((δ : 𝕜)) • X).kyFanSum k := by
        simp only [Y, LinearMap.kyFanSum_smul, RCLike.norm_of_nonneg hpinv0]
      _ = p⁻¹ *
          (δ * X.kyFanSum k) := by
        rw [LinearMap.kyFanSum_smul, RCLike.norm_of_nonneg (le_of_lt hδ)]
      _ ≤ p⁻¹ *
          (p * C.kyFanSum k) :=
        mul_le_mul_of_nonneg_left hcore hpinv0
      _ = C.kyFanSum k := by
        field_simp [ne_of_gt hp]
  · dsimp [Y]
    rw [smul_smul, ← RCLike.ofReal_mul]
    field_simp [ne_of_gt hp]
    simp
/-- A separated self-adjoint Sylvester equation admits a finite two-sided
unitary-orbit certificate of mass at most `π / 2` for the scaled solution
`δ • X` relative to the defect `C`.

Consequently this theorem contains no Fourier, integration, compactness, or
Carathéodory bookkeeping.  The harmonic analysis enters only through the
unconditional reciprocal Ky Fan theorem; this barycentric theorem and the
certificate extraction are finite-algebra and orbit-convexity
consequences, and they attain the exact mass `π / 2` for the particular
Sylvester solution even though the universal undoubled multiplier
certificate at that mass is refuted. -/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    UnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  rcases sylvester_barycentricOrbitRepresentation_of_spectralDistance
      hA hB hδ hgap hEq with ⟨m, hm, hmass, Y, hY, hXY⟩
  exact
    UnitarilyInvariantSeminorm.hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      hm hmass hY hXY

/-! ## Arbitrary disjoint spectra: the sharp Hilbert--Schmidt estimate

The `π/2` loss above is unavoidable for a general unitarily invariant norm, but
the Frobenius norm loses nothing under arbitrary positive separation.  The
coordinate equation `(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ` divides entrywise, and Parseval in the
two eigenbases sums the squares.  This is the estimate behind the
Hilbert--Schmidt form of Davis--Kahan Theorem 6.2.
-/

/-- **Frobenius Sylvester estimate, constant one.**  Under arbitrary positive
spectral separation the Hilbert--Schmidt norm of a Sylvester solution is
controlled by the residual with no dimensional or analytic loss. -/
theorem frobenius_sylvester_le_of_pointSpectraSeparated
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * UnitarilyInvariantSeminorm.frobenius 𝕜 E F X ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 E F C := by
  classical
  set bA := hA.eigenvectorBasis rfl with hbA
  set bB := hB.eigenvectorBasis rfl with hbB
  -- the coordinate equation divides by a denominator of size at least `δ`
  have hentry : ∀ (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)),
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ := by
    intro i j
    have hcoef := sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    have hsep : δ ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| :=
      hgap _ _ (eigenvalue_mem_restrictedPointSpectrum_top hA i)
        (eigenvalue_mem_restrictedPointSpectrum_top hB j)
    have hnorm :
        ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ =
          |hA.eigenvalues rfl i - hB.eigenvalues rfl j| := by
      rw [show ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) =
        ((hA.eigenvalues rfl i - hB.eigenvalues rfl j : ℝ) : 𝕜) by push_cast; ring]
      exact RCLike.norm_ofReal _
    calc
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖
          ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by
            gcongr
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by rw [hnorm]
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
              ⟪X (bB j), bA i⟫_𝕜‖ := (norm_mul _ _).symm
      _ = ‖⟪C (bB j), bA i⟫_𝕜‖ := by rw [hcoef]
  -- Parseval in the codomain eigenbasis turns the entry bound into a column bound
  have hcol : ∀ j : Fin (Module.finrank 𝕜 E),
      δ ^ 2 * ‖X (bB j)‖ ^ 2 ≤ ‖C (bB j)‖ ^ 2 := by
    intro j
    rw [← bA.sum_sq_norm_inner_left (X (bB j)),
      ← bA.sum_sq_norm_inner_left (C (bB j)), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc
      δ ^ 2 * ‖⟪X (bB j), bA i⟫_𝕜‖ ^ 2
          = (δ * ‖⟪X (bB j), bA i⟫_𝕜‖) ^ 2 := by ring
      _ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hentry i j) 2
  have htot : δ ^ 2 * (∑ j, ‖X (bB j)‖ ^ 2) ≤ ∑ j, ‖C (bB j)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  rw [UnitarilyInvariantSeminorm.frobenius_apply bB X,
    UnitarilyInvariantSeminorm.frobenius_apply bB C,
    ← Real.sqrt_sq hδ.le, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt htot

end TauCeti
