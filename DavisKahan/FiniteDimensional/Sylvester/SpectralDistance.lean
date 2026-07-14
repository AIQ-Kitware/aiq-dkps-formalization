/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Sylvester.Interval
import DavisKahan.FiniteDimensional.Sylvester.Internal.ReciprocalMultiplier

/-!
# Sylvester estimates for arbitrary separated spectra

The reciprocal spectral multiplier, finite orbit certificates, and the sharp
`pi / 2` Ky Fan and arbitrary-UI-norm bounds over real and complex scalars.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Arbitrary disjoint spectra: the `π/2` scaffold

The Bhatia--Davis--McIntosh extension is factored through the simultaneous Ky
Fan prefix estimate and rectangular Fan dominance.
-/

/-- Reciprocal spectral multiplier in the canonical eigenbases of `A` and `B`.
The gap hypothesis is not built into the definition; it is supplied when the
kernel is used, so the object remains a simple coordinate function. -/
noncomputable def sylvesterReciprocalKernel
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    Fin (Module.finrank 𝕜 F) → Fin (Module.finrank 𝕜 E) → 𝕜 :=
  fun i j =>
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))⁻¹

/-- Positive spectral separation makes every denominator of the reciprocal
kernel nonzero.  This is the scalar fact used both by the coordinate solution
formula and by the multiplier estimate. -/
theorem sylvester_eigenvalue_sub_ne_zero
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    (hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜) ≠ 0 := by
  let α : ℝ := hA.eigenvalues rfl i
  let β : ℝ := hB.eigenvalues rfl j
  have hα : α ∈ restrictedSpectrum A ⊤ :=
    eigenvalue_mem_restrictedSpectrum_top hA i
  have hβ : β ∈ restrictedSpectrum B ⊤ :=
    eigenvalue_mem_restrictedSpectrum_top hB j
  have habs : 0 < |α - β| := lt_of_lt_of_le hδ (hgap α β hα hβ)
  have hαβ : α ≠ β := sub_ne_zero.mp (abs_pos.mp habs)
  exact sub_ne_zero.mpr fun h => hαβ (RCLike.ofReal_injective h)

/-- Entrywise spectral-coordinate form of the Sylvester equation.  It exposes
exactly the scalar equation to which the reciprocal kernel is applied:
`(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ`. -/
theorem sylvester_eigenbasis_coefficient_equation
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
        ⟪X (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 =
      ⟪C (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 := by
  have hpoint := LinearMap.congr_fun hEq (hB.eigenvectorBasis rfl j)
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
barycentric theorem can state real convex-hull membership.-/
local instance realModuleSylvesterMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

/-- **Analytic Ky Fan root of the finite `π/2` front.**  Every singular-value
prefix of a separated self-adjoint Sylvester solution satisfies the
Bhatia--Davis--McIntosh estimate.

This is the weakest field-uniform analytic seam.  The operator-valued
barycenter, exact finite certificate, arbitrary unitarily invariant norm,
residual, and perturbation statements are formal consequences.

This statement deliberately contains no convex-hull or finite-certificate
bookkeeping.-/
theorem kyFan_sylvester_le_of_spectralDistance_analytic
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

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
show every prefix of `Y` is bounded by the corresponding prefix of `C`;
rectangular Fan orbit-convexity gives `Y ∈ conv(orbit(C))`, and the defining
scalar identity recovers `δ • X = p • Y`. -/
theorem sylvester_barycentricOrbitRepresentation_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ Real.pi / 2 ∧
      ∃ Y : E →ₗ[𝕜] F,
        Y ∈ convexHull ℝ
          (RectangularUnitarilyInvariantNorm.twoSidedUnitaryOrbit C) ∧
        (((δ : 𝕜)) • X) = ((m : 𝕜)) • Y := by
  let p : ℝ := Real.pi / 2
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp0 : 0 ≤ p := le_of_lt hp
  have hpinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  let Y : E →ₗ[𝕜] F := (((p⁻¹ : ℝ) : 𝕜)) • (((δ : 𝕜)) • X)
  refine ⟨p, hp0, le_rfl, Y, ?_, ?_⟩
  · apply
      RectangularUnitarilyInvariantNorm.mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    intro k
    have hcore :=
      kyFan_sylvester_le_of_spectralDistance_analytic
        hA hB hδ hgap hEq k
    change δ *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C at hcore
    calc
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k Y =
          p⁻¹ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
            (((δ : 𝕜)) • X) := by
        simpa only [Y] using
          RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k (((δ : 𝕜)) • X) hpinv0
      _ = p⁻¹ *
          (δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X) := by
        rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X (le_of_lt hδ)]
      _ ≤ p⁻¹ *
          (p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C) :=
        mul_le_mul_of_nonneg_left hcore hpinv0
      _ = RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
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
certificate at that mass is refuted.-/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    RectangularUnitarilyInvariantNorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  rcases sylvester_barycentricOrbitRepresentation_of_spectralDistance
      hA hB hδ hgap hEq with ⟨m, hm, hmass, Y, hY, hXY⟩
  exact
    RectangularUnitarilyInvariantNorm.hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      hm hmass hY hXY

/-- Every Ky Fan prefix satisfies the arbitrary-disjoint-spectrum Sylvester
bound.  This public theorem is the stable API alias for the analytic root;
the barycentric and finite-certificate layers are downstream consequences,
not proof dependencies. -/
theorem kyFan_sylvester_le_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
  kyFan_sylvester_le_of_spectralDistance_analytic
    hA hB hδ hgap hEq k

/-- General disjoint-spectrum extension with the Bhatia--Davis--McIntosh
constant `π/2`, lifted from the finite orbit certificate through Ky Fan
prefixes and rectangular Fan dominance.
-/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : 𝕜)) • X) ≤ N (((p : 𝕜)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X hδ0,
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k C hp0]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : 𝕜)) • X) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos hδ]
    _ ≤ N (((p : 𝕜)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-! ### Unconditional field-specific endpoints

The explicit Haagerup--Zsidó kernel closes the analytic root over `ℂ`
directly and over `ℝ` through the doubled orthogonal descent.  The theorems
below repeat the sharp arbitrary-separated-spectrum statements at the two
concrete scalar fields with no open obligation.  The generic `RCLike`
versions above remain routed through the finite orbit-interpolation seam,
which is still an open obligation. -/

/-- Unconditional complex Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_complex
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

/-- Unconditional real Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_real
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (alpha := hA.eigenvalues rfl)
    (beta := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    have h := sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h

/-- Unconditional complex arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : RectangularUnitarilyInvariantNorm ℂ EC FC)
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : ℂ)) • X) ≤ N (((p : ℂ)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX : RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (((δ : ℂ)) • X) =
        δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X :=
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X hδ0
    have hC : RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (((p : ℂ)) • C) =
        p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k C hp0
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_complex hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : ℂ)) • X) := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (((p : ℂ)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-- Unconditional real arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : RectangularUnitarilyInvariantNorm ℝ ER FR)
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (δ • X) ≤ N (p • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX := RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k X hδ0
    have hC := RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k C hp0
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hX hC
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_real hA hB hδ hgap hEq k
  calc
    δ * N X = N (δ • X) := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (p • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

end DavisKahanTheory
end ForMathlib
