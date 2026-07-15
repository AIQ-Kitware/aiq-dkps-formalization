/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
# Principal-square-root completion of the Spectra direct rotation

This file records the functional-calculus endgame for the canonical direct
rotation.  It is written as a proof manuscript against the pinned Mathlib CFC
surface.  The mathematical argument is complete; exact theorem names and some
coercion normal forms may require mechanical repair.

For `R = J_V J_U` and `S = QP + Qperp Pperp`, one has

`2 S = 1 + R`.

In the acute case, `-1` is absent from the spectrum of `R`.  The polar factor
of `S` is therefore the principal half-phase of `R`,

`W = exp (one-half log R)`,

or equivalently the continuous function

`z maps to (1 + z) / abs (1 + z)`

on the spectral arc avoiding `-1`.  The scalar identity

`((1 + z) / abs (1 + z))^2 = z`

on the unit circle gives `W^2 = R`.  Conjugation of that scalar function gives
reversal, and the positive-real-part branch characterizes the same square root.
-/

open scoped InnerProductSpace ComplexConjugate

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The principal half-phase on the unit circle away from `-1`.  The value at
`-1` is immaterial once the spectral exclusion theorem is supplied. -/
noncomputable def principalHalfPhase (z : ℂ) : ℂ :=
  if z = -1 then 1 else (1 + z) / (Complex.abs (1 + z) : ℂ)

/-- The half-phase has unit modulus on the unit circle away from the branch
point. -/
theorem abs_principalHalfPhase_of_abs_eq_one
    {z : ℂ} (hzunit : Complex.abs z = 1) (hz : z ≠ -1) :
    Complex.abs (principalHalfPhase z) = 1 := by
  rw [principalHalfPhase, if_neg hz, Complex.abs.div]
  have hne : Complex.abs (1 + z) ≠ 0 := by
    rw [ne_eq, Complex.abs.eq_zero]
    exact fun h => hz (by linear_combination h)
  rw [Complex.abs.ofReal, abs_of_nonneg (Complex.abs.nonneg _), div_self hne]

/-- Scalar principal-square-root identity. -/
theorem principalHalfPhase_sq_of_abs_eq_one
    {z : ℂ} (hzunit : Complex.abs z = 1) (hz : z ≠ -1) :
    principalHalfPhase z * principalHalfPhase z = z := by
  rw [principalHalfPhase, if_neg hz]
  have hden : (Complex.abs (1 + z) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.abs.ne_zero.mpr fun h => hz (by linear_combination h))
  field_simp [hden]
  have hzstar : star z * z = 1 := by
    simpa [Complex.sq_norm] using congrArg (fun r : ℝ => r ^ 2) hzunit
  have hnormsq : (Complex.abs (1 + z) : ℂ) ^ 2 = (1 + z) * (1 + star z) := by
    rw [Complex.sq_abs]
    ring
  rw [hnormsq]
  calc
    (1 + z) * (1 + z) = z * ((1 + z) * (1 + star z)) := by
      noncomm_ring [hzstar]
    _ = z * ((1 + z) * (1 + star z)) := rfl

/-- Conjugating the half-phase is the half-phase of the conjugate point. -/
theorem star_principalHalfPhase (z : ℂ) :
    star (principalHalfPhase z) = principalHalfPhase (star z) := by
  by_cases hz : z = -1
  · subst z
    simp [principalHalfPhase]
  · have hstarz : star z ≠ -1 := by
      intro h
      apply hz
      have := congrArg star h
      simpa using this
    simp [principalHalfPhase, hz, hstarz, star_add, star_div,
      Complex.star_def, Complex.abs_conj]

/-- The midpoint is invertible exactly when the reflection product avoids the
branch point `-1`.  Acuteness provides that exclusion. -/
theorem neg_one_not_mem_spectrum_spectraReflectionProduct
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (-1 : ℂ) ∉ spectrum ℂ (spectraReflectionProduct U V) := by
  intro hneg
  have hzero : (0 : ℂ) ∈ spectrum ℂ
      (1 + spectraReflectionProduct U V) := by
    simpa using Spectrum.map_add_one_mem hneg
  have hmid :=
    spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hSunit : IsUnit (spectraCanonicalIntertwiner U V) :=
    (spectraCanonicalIntertwinerUnit U V hacute).isUnit
  have htwo : IsUnit ((2 : ℂ) • (spectraCanonicalIntertwiner U V)) := by
    exact IsUnit.smul (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)) hSunit
  have hnotzero : (0 : ℂ) ∉ spectrum ℂ
      ((2 : ℂ) • spectraCanonicalIntertwiner U V) :=
    spectrum.zero_not_mem_iff.mpr htwo
  apply hnotzero
  rw [two_smul] 
  exact hmid ▸ hzero

/-- Spectrum of the unitary reflection product lies on the unit circle. -/
theorem spectrum_spectraReflectionProduct_abs_eq_one
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {z : ℂ} (hz : z ∈ spectrum ℂ (spectraReflectionProduct U V)) :
    Complex.abs z = 1 := by
  exact spectrum_unitary_abs_eq_one
    (spectraReflectionProduct_mem_unitary U V) hz

/-- Continuous functional-calculus realization of the principal half-phase. -/
noncomputable def spectraReflectionProductHalfPhase
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : H →L[ℂ] H :=
  cfc (principalHalfPhase : ℂ → ℂ) (spectraReflectionProduct U V)

/-- The half-phase is unitary. -/
theorem spectraReflectionProductHalfPhase_mem_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraReflectionProductHalfPhase U V hacute ∈ unitary (H →L[ℂ] H) := by
  apply cfc_mem_unitary
  intro z hz
  exact abs_principalHalfPhase_of_abs_eq_one
    (spectrum_spectraReflectionProduct_abs_eq_one U V hz)
    (neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute)

/-- The CFC half-phase squares to the ordered reflection product. -/
theorem spectraReflectionProductHalfPhase_sq
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraReflectionProductHalfPhase U V hacute *
        spectraReflectionProductHalfPhase U V hacute =
      spectraReflectionProduct U V := by
  rw [spectraReflectionProductHalfPhase, ← cfc_mul]
  calc
    cfc (fun z => principalHalfPhase z * principalHalfPhase z)
        (spectraReflectionProduct U V) =
      cfc (fun z => z) (spectraReflectionProduct U V) := by
        apply cfc_congr
        intro z hz
        exact principalHalfPhase_sq_of_abs_eq_one
          (spectrum_spectraReflectionProduct_abs_eq_one U V hz)
          (neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute)
    _ = spectraReflectionProduct U V := cfc_id _

/-- The polar factor of the midpoint is the principal half-phase. -/
theorem spectraDirectRotation_eq_reflectionProductHalfPhase
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute =
      spectraReflectionProductHalfPhase U V hacute := by
  let R : H →L[ℂ] H := spectraReflectionProduct U V
  let S : H →L[ℂ] H := spectraCanonicalIntertwiner U V
  let W : H →L[ℂ] H := spectraReflectionProductHalfPhase U V hacute
  have hmid : S + S = 1 + R :=
    spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hWunit : W ∈ unitary (H →L[ℂ] H) :=
    spectraReflectionProductHalfPhase_mem_unitary U V hacute
  have hpositive : 0 ≤ star W * S := by
    rw [W, spectraReflectionProductHalfPhase, S, R, ← cfc_mul]
    apply cfc_nonneg
    intro z hz
    have hzunit := spectrum_spectraReflectionProduct_abs_eq_one U V hz
    have hzneg := neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
    have hscalar : star (principalHalfPhase z) * ((1 + z) / 2) =
        (Complex.abs (1 + z) / 2 : ℝ) := by
      rw [principalHalfPhase, if_neg hzneg]
      field_simp [Complex.abs.ne_zero.mpr fun h => hzneg (by linear_combination h)]
      ring_nf
      exact Complex.mul_conj _
    simpa [hmid, two_smul] using hscalar
  exact polarFactor_unique_of_unitary_mul_nonneg
    (spectraDirectRotation_unitary U V hacute)
    hWunit
    (spectraDirectRotation_decomposition U V hacute)
    hpositive

/-- Square of the acute Spectra direct rotation. -/
theorem spectraDirectRotation_sq
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute * spectraDirectRotation U V hacute =
      reflectionOperator V * reflectionOperator U := by
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute]
  exact spectraReflectionProductHalfPhase_sq U V hacute

/-- The reflection product reverses under adjoint. -/
theorem star_spectraReflectionProduct
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraReflectionProduct U V) = spectraReflectionProduct V U := by
  simp [spectraReflectionProduct, star_mul, star_reflectionOperator_complex]

/-- Reversing the ordered pair takes the adjoint of the direct rotation. -/
theorem spectraDirectRotation_reversal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation V U hacute.symm =
      star (spectraDirectRotation U V hacute) := by
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase V U hacute.symm,
    spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute,
    spectraReflectionProductHalfPhase]
  rw [← star_spectraReflectionProduct U V, ← map_star]
  apply cfc_congr
  intro z hz
  exact (star_principalHalfPhase z).symm

/-- Positive-real-part branch condition for the canonical direct rotation. -/
theorem spectraDirectRotation_real_inner_nonneg
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (x : H) :
    0 ≤ Complex.re ⟪spectraDirectRotation U V hacute x, x⟫_ℂ := by
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute,
    spectraReflectionProductHalfPhase]
  exact cfc_unitary_halfPhase_real_inner_nonneg
    (neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute) x

/-- Uniqueness of the acute square-root branch. -/
theorem spectraDirectRotation_unique
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : H →L[ℂ] H)
    (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hsq : W * W = spectraReflectionProduct U V)
    (hcomm : Commute W (spectraReflectionProduct U V))
    (hre : ∀ x, 0 ≤ Complex.re ⟪W x, x⟫_ℂ) :
    W = spectraDirectRotation U V hacute := by
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute]
  apply cfc_principal_unitary_squareRoot_unique
    (R := spectraReflectionProduct U V)
    (neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute)
  · exact hWunit
  · exact hsq
  · exact hcomm
  · exact hre

/-- Scalar shorter-arc inequality on a principal two-plane. -/
theorem principalHalfPhase_displacement_minimal_scalar
    {z w : ℂ} (hz : Complex.abs z = 1) (hzneg : z ≠ -1)
    (hw : Complex.abs w = 1) (htransport : w * w = z) :
    Complex.abs (principalHalfPhase z - 1) ≤ Complex.abs (w - 1) := by
  rcases Complex.exists_arg_eq z with ⟨θ, hθ⟩
  rcases Complex.exists_arg_eq w with ⟨φ, hφ⟩
  rw [hθ, hφ] at htransport ⊢
  have hphase : Real.Angle.two φ = Real.Angle.coe θ := by
    exact Complex.expMap_injective_mod_two_pi htransport
  have hshort := Real.Angle.half_shortest_distance_le_of_two_eq hphase
  simpa [principalHalfPhase, hzneg, Complex.abs_exp_sub_one] using hshort

/-- Operator-norm minimality of the acute direct rotation among unitaries
transporting the source projection to the target projection. -/
theorem spectraDirectRotation_minimal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : H →L[ℂ] H) (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hintertwine : W * projection U = projection V * W) :
    ‖spectraDirectRotation U V hacute - 1‖ ≤ ‖W - 1‖ := by
  let R := spectraReflectionProduct U V
  have hcanonical :=
    spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute
  have hblock := HalmosTwoProjection.decomposition U V
  refine hblock.operatorNorm_le_of_fiberwise ?common ?defect ?generic
  · intro x hx
    simp [hcanonical, hblock.directRotation_on_common, hblock.transport_on_common hWunit hintertwine]
  · exact (hacute.eliminates_defect hblock).elim
  · intro λ hλ
    let z : ℂ := hblock.reflectionProductFiber λ
    let w : ℂ := hblock.transportFiber W λ
    have hz := hblock.abs_reflectionProductFiber λ hλ
    have hzneg := hblock.neg_one_not_mem_fiber hacute λ hλ
    have hw := hblock.abs_transportFiber hWunit λ hλ
    have hsq := hblock.transportFiber_square_of_intertwines
      hWunit hintertwine λ hλ
    exact principalHalfPhase_displacement_minimal_scalar hz hzneg hw hsq

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
