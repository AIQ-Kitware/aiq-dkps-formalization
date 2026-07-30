/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.DoubledPhase

/-!
# Finite reciprocal multipliers

This file is the public face of the finite reciprocal multiplier development: it
carries the certificate built from an exact reciprocal orbit interpolation, the
two-by-two real obstruction that forces the doubled route, the status map of the
landscape, and the final Ky Fan estimates.  The three parts it imports supply the
orbit algebra, the Fourier interpolation, and the doubled phase realization.

Importing this module gives the whole development, as it did before the split.

The operator-theoretic theorem is factored through one simultaneous finite
interpolation certificate.  For fixed orthonormal coordinates and separated real
arrays `α` and `β`, the certificate supplies one finite family of left/right
unitaries whose orbit action realizes the reciprocal multiplier on every
coordinate matrix unit at once, with coefficient mass at most `π / 2`.  Once that
certificate is available, the passage to an arbitrary rectangular map is finite
linear algebra: expand the map in coordinate matrix units, use the entrywise
Sylvester equation, and recombine the common orbit action.

Literature bridge:

* `prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`
  reconstructs the separated-spectrum Fourier representation, the `pi / 2`
  provenance chain, the finite interpolation reduction, and the real-field
  descent that remains to be supplied.

## Provenance

*Split, not restated.*  Until 2026-07-29 this file held the whole development in
2887 lines — the largest module in the library, nearly 3x Tau Ceti's stated
1000-line limit for a new file (`ForTauCeti/README.md` §4).  The file was divided
it along its four mathematical seams into
`…ReciprocalMultiplier.{OrbitAction, Fourier, DoubledPhase}` and this
root.  **No statement, signature, proof, attribute or declaration name changed**;
the split is a file boundary plus the imports it forces, and the
`set_option linter.style.longFile 2900` it used to need is gone.

That file in turn was
`DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean`
before the whole remaining sin-Θ closure moved into the staging layer;
Y3(b2) and Y3(b3) are what made that possible, since before them this import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

namespace TauCeti

open TauCeti
open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

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
      -- names the application so the norm bound applies to it directly.
      change ‖(U r) (e i)‖ = 1
      rw [(U r).norm_map, e.norm_eq_one]
    calc
      |u r i| ≤ ‖e i‖ * ‖(U r).toLinearMap (e i)‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by rw [hnorm, e.norm_eq_one, one_mul]
  have hv_le (r : Fin n) (j : Fin (Module.finrank ℝ G)) : |v r j| ≤ 1 := by
    have hnorm : ‖(V r).toLinearMap (e j)‖ = 1 := by
      -- names the application so the norm bound applies to it directly.
      change ‖(V r) (e j)‖ = 1
      rw [(V r).norm_map, e.norm_eq_one]
    calc
      |v r j| ≤ ‖e j‖ * ‖(V r).toLinearMap (e j)‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by rw [hnorm, e.norm_eq_one, one_mul]
  have hterm (r : Fin n) (i j : Fin (Module.finrank ℝ G)) :
      ⟪e i, (unitaryOrbitAction (U r) (V r))
        (basisMatrixUnit e e i j) (e j)⟫_ℝ = u r i * v r j := by
    -- states the goal as the inner-product identity the structure lemma expects.
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

/-! ### Status map of the reciprocal interpolation landscape

This note records, durably, which reciprocal-multiplier representations are
true, which are refuted, and which carry the sharp generic theory.  Any
future strengthening work should consult it before touching this seam.

1. **False: exact undoubled real reciprocal orbit interpolation at mass
   `π / 2`.**  A universal statement asserting
   `HasReciprocalOrbitInterpolation eF eE α β δ (Real.pi / 2)` for every
   separated frequency data over every `RCLike` field is refuted over `ℝ`
   already in dimension two: see
   `real_reciprocalOrbitInterpolation_mass_lower_bound` (mass at least
   `5 / 3`) and `not_hasReciprocalOrbitInterpolation_pi_div_two_euclidean`.
   The obstruction bounds the diagonal matrix coefficients of arbitrary
   orthogonal factors, so neither compactness/Carathéodory arguments nor
   more general real rotations can rescue the exact undoubled statement.
   No declaration asserting it may be reintroduced.

2. **True: complex phase interpolation.**  Over `ℂ`, diagonal phase
   unitaries realize every finite Fourier character, giving
   `hasReciprocalOrbitInterpolation_of_finiteFourierInterpolation` at mass
   `π / 2 + ε` for every positive `ε` from the Haagerup--Zsidó kernel.
   Whether exact complex attainment at `π / 2` holds is not needed by any
   current consumer and is left unexplored.

3. **True: doubled phase realization over every `RCLike` field.**  The
   rotation `[[cos θ, -sin θ], [sin θ, cos θ]]` with real entries embedded
   in `𝕜` realizes each phase on two orthogonal copies:
   `hasDoubledReciprocalOrbitInterpolation_of_finiteFourierInterpolation`.
   This is the correct generic replacement for item 1.

4. **True: sharp real and complex Ky Fan inequalities.**  Singular-value
   duplication on `orthogonalBlockSum` cancels the doubling, so the
   endpoint estimates `kyFan_reciprocalMultiplier_le` (generic),
   `kyFan_reciprocalMultiplier_le_complex`, and
   `kyFan_reciprocalMultiplier_le_real` hold with the exact constant
   `π / 2` and no open obligation.  Inequalities need only the `π / 2 + ε`
   certificates, not exact endpoint attainment.

5. **Still possible: exact finite orbit certificates for a particular
   Sylvester solution.**  The obstruction refutes only the universal
   multiplier representation acting correctly on every matrix unit at once.
   Fan dominance and orbit convexity still produce the solution-specific
   exact certificates
   `sylvester_barycentricOrbitRepresentation_of_spectralDistance` and
   `sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance` at
   exact mass `π / 2`, which is weaker than item 1 and sufficient for all
   downstream finite theory. -/

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
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

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
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
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
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

/-- **Every finite reciprocal multiplier with gap `δ` satisfies the sharp
simultaneous Ky Fan prefix estimate**, over every `RCLike` scalar field.

The proof is unconditional: the explicit Haagerup--Zsidó kernel supplies
finite Fourier interpolations of mass `π / 2 + ε`, the generic doubled phase
rotations realize them on two orthogonal copies of the spaces, and
singular-value duplication removes the doubling at the level of every Ky Fan
prefix.  No exact undoubled orbit certificate is used; that statement is
refuted over `ℝ` by the two-by-two obstruction above. -/
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
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
  kyFan_reciprocalMultiplier_le_of_integrableKernel eF eE α β hδ hgap
    hasIntegrableReciprocalFourierKernel_pi_div_two hcoeff k

end TauCeti
