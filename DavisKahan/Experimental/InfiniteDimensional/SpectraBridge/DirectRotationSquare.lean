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

open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The principal half-phase on the unit circle away from `-1`.  The value at
`-1` is immaterial once the spectral exclusion theorem is supplied. -/
noncomputable def principalHalfPhase (z : ℂ) : ℂ :=
  if z = -1 then 1 else (1 + z) / (‖1 + z‖ : ℂ)

/-- The half-phase has unit modulus on the unit circle away from the branch
point. -/
theorem abs_principalHalfPhase_of_abs_eq_one
    {z : ℂ} (hz : z ≠ -1) :
    ‖principalHalfPhase z‖ = 1 := by
  have h1z : (1 : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  have hne : ‖1 + z‖ ≠ 0 := norm_ne_zero_iff.mpr h1z
  rw [principalHalfPhase, if_neg hz, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hne]

/-- Scalar principal-square-root identity. -/
theorem principalHalfPhase_sq_of_abs_eq_one
    {z : ℂ} (hzunit : ‖z‖ = 1) (hz : z ≠ -1) :
    principalHalfPhase z * principalHalfPhase z = z := by
  have h1z : (1 : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hzunit]
    norm_num
  have h1cz : (1 : ℂ) + (starRingEnd ℂ) z ≠ 0 := by
    intro h
    apply h1z
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  -- `‖1 + z‖ ^ 2 = (1 + z) * conj (1 + z)`, expanded on the unit circle.
  have hden : ((‖1 + z‖ : ℝ) : ℂ) * ((‖1 + z‖ : ℝ) : ℂ)
      = (1 + z) * (1 + (starRingEnd ℂ) z) := by
    have h := Complex.mul_conj (1 + z)
    rw [map_add, map_one] at h
    rw [h, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [principalHalfPhase, if_neg hz, div_mul_div_comm, hden,
    div_eq_iff (mul_ne_zero h1z h1cz)]
  linear_combination (-1 - z) * hzz

/-- The half-phase is continuous away from the branch point `-1`. -/
theorem continuousOn_principalHalfPhase {s : Set ℂ} (hs : (-1 : ℂ) ∉ s) :
    ContinuousOn principalHalfPhase s := by
  have hcont : ContinuousOn (fun z : ℂ => (1 + z) / (‖1 + z‖ : ℂ)) s := by
    apply ContinuousOn.div
    · exact (continuous_const.add continuous_id).continuousOn
    · exact (Complex.continuous_ofReal.comp
        (continuous_const.add continuous_id).norm).continuousOn
    · intro z hz
      have hzne : z ≠ -1 := fun h => hs (h ▸ hz)
      exact Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr fun h => hzne (by linear_combination h))
  exact hcont.congr fun z hz =>
    if_neg fun h : z = -1 => hs (h ▸ hz)

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
    have hnorm : ‖(1 : ℂ) + star z‖ = ‖1 + z‖ := by
      rw [show (1 : ℂ) + star z = star (1 + z) by simp, norm_star]
    rw [principalHalfPhase, principalHalfPhase, if_neg hz, if_neg hstarz, hnorm]
    simp [star_div₀, Complex.star_def, Complex.conj_ofReal]

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
    simpa using
      (spectrum.add_mem_add_iff
        (a := spectraReflectionProduct U V) (r := (-1 : ℂ)) (s := (1 : ℂ))).mpr
        hneg
  have hmid :=
    spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hSunit : IsUnit (spectraCanonicalIntertwiner U V) := by
    rw [← coe_spectraCanonicalIntertwinerUnit U V hacute]
    exact (spectraCanonicalIntertwinerUnit U V hacute).isUnit
  have htwoS : (Units.mk0 (2 : ℂ) two_ne_zero) •
      spectraCanonicalIntertwiner U V =
      spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
    rw [Units.smul_def, Units.val_mk0, two_smul]
  have hzeroS : (0 : ℂ) ∈ spectrum ℂ (spectraCanonicalIntertwiner U V) := by
    have hSS : (Units.mk0 (2 : ℂ) two_ne_zero) • (0 : ℂ) ∈ spectrum ℂ
        ((Units.mk0 (2 : ℂ) two_ne_zero) • spectraCanonicalIntertwiner U V) := by
      rw [htwoS, hmid, smul_zero]
      exact hzero
    exact spectrum.smul_mem_smul_iff.mp hSS
  exact (spectrum.zero_notMem_iff ℂ).mpr hSunit hzeroS

/-- Spectrum of the unitary reflection product lies on the unit circle. -/
theorem spectrum_spectraReflectionProduct_abs_eq_one
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {z : ℂ} (hz : z ∈ spectrum ℂ (spectraReflectionProduct U V)) :
    ‖z‖ = 1 := by
  exact spectrum.norm_eq_one_of_unitary
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
  have hneg := neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  rw [spectraReflectionProductHalfPhase,
    cfc_unitary_iff (principalHalfPhase : ℂ → ℂ) (spectraReflectionProduct U V)
      hnormal (continuousOn_principalHalfPhase hneg)]
  intro z hz
  have hzne : z ≠ -1 := fun h => hneg (h ▸ hz)
  have h1 : ‖principalHalfPhase z‖ = 1 :=
    abs_principalHalfPhase_of_abs_eq_one hzne
  calc star (principalHalfPhase z) * principalHalfPhase z
      = ((Complex.normSq (principalHalfPhase z) : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    _ = 1 := by
        rw [Complex.normSq_eq_norm_sq, h1]
        norm_num

/-- The CFC half-phase squares to the ordered reflection product. -/
theorem spectraReflectionProductHalfPhase_sq
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraReflectionProductHalfPhase U V hacute *
        spectraReflectionProductHalfPhase U V hacute =
      spectraReflectionProduct U V := by
  have hneg := neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  have hcont : ContinuousOn principalHalfPhase
      (spectrum ℂ (spectraReflectionProduct U V)) :=
    continuousOn_principalHalfPhase hneg
  rw [spectraReflectionProductHalfPhase, ← cfc_mul _ _ _ hcont hcont]
  calc
    cfc (fun z => principalHalfPhase z * principalHalfPhase z)
        (spectraReflectionProduct U V) =
      cfc (fun z : ℂ => z) (spectraReflectionProduct U V) := by
        apply cfc_congr
        intro z hz
        exact principalHalfPhase_sq_of_abs_eq_one
          (spectrum_spectraReflectionProduct_abs_eq_one U V hz)
          (fun h => hneg (h ▸ hz))
    _ = spectraReflectionProduct U V := cfc_id' ℂ _

/-- Acuteness is symmetric in the two subspaces. -/
theorem _root_.ForMathlib.DavisKahan.IsAcute.symm
    {U V : Submodule ℂ H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsAcute U V) : IsAcute V U := by
  show subspaceGap V U < 1
  rw [subspaceGap, Submodule.projectionGap_comm]
  exact h

/-- The scalar cosine gauge `‖1 + z‖ / 2` of the reflection product. -/
noncomputable def cosineGauge (z : ℂ) : ℂ := ((‖1 + z‖ / 2 : ℝ) : ℂ)

theorem continuous_cosineGauge : Continuous cosineGauge :=
  Complex.continuous_ofReal.comp
    ((continuous_const.add continuous_id).norm.div_const 2)

/-- The gauge squares to `star ((1+z)/2) * ((1+z)/2)`. -/
theorem cosineGauge_mul_self (z : ℂ) :
    cosineGauge z * cosineGauge z =
      star ((2⁻¹ : ℂ) • (1 + z)) * ((2⁻¹ : ℂ) • (1 + z)) := by
  have h := Complex.normSq_eq_conj_mul_self (z := 1 + z)
  have hstar2 : star (2⁻¹ : ℂ) = 2⁻¹ := by
    simp
  rw [cosineGauge, star_smul, smul_mul_smul_comm]
  show _ = star (2⁻¹ : ℂ) * 2⁻¹ * ((starRingEnd ℂ) (1 + z) * (1 + z))
  rw [← h, Complex.normSq_eq_norm_sq, hstar2]
  push_cast
  ring

/-- The half-phase times the gauge recovers the midpoint function away from
the branch point. -/
theorem principalHalfPhase_mul_cosineGauge {z : ℂ} (hz : z ≠ -1) :
    principalHalfPhase z * cosineGauge z = (2⁻¹ : ℂ) • (1 + z) := by
  have h1z : (1 : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  have hne : (‖(1 : ℂ) + z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h1z)
  rw [principalHalfPhase, if_neg hz, cosineGauge, smul_eq_mul]
  push_cast
  field_simp

/-- The midpoint as `cfc` of the scalar midpoint function. -/
theorem spectraCanonicalIntertwiner_eq_cfc
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V =
      cfc (fun z : ℂ => (2⁻¹ : ℂ) • (1 + z)) (spectraReflectionProduct U V) := by
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  have hmid := spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hone_add : cfc (fun z : ℂ => 1 + z) (spectraReflectionProduct U V) =
      1 + spectraReflectionProduct U V := by
    have h1 := cfc_add (R := ℂ) (a := spectraReflectionProduct U V)
      (fun _ => 1) (fun z => z) continuous_const.continuousOn
      continuous_id.continuousOn
    rw [cfc_const_one ℂ (spectraReflectionProduct U V),
      cfc_id' ℂ (spectraReflectionProduct U V)] at h1
    exact h1
  have h2 : (2 : ℂ) • spectraCanonicalIntertwiner U V =
      1 + spectraReflectionProduct U V := by
    rw [two_smul]; exact hmid
  have h3 := cfc_smul (R := ℂ) (a := spectraReflectionProduct U V)
    (2⁻¹ : ℂ) (fun z => 1 + z)
    (continuous_const.add continuous_id).continuousOn
  rw [hone_add, ← h2, smul_smul] at h3
  rw [show ((2 : ℂ)⁻¹ * 2 : ℂ) = 1 by norm_num, one_smul] at h3
  exact h3.symm

/-- The Spectra modulus of the acute midpoint is `cfc` of the cosine gauge. -/
theorem spectraOperatorAbsoluteValue_intertwiner_eq_cfc
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
      cfc cosineGauge (spectraReflectionProduct U V) := by
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  have hg0 : (0 : H →L[ℂ] H) ≤ cfc cosineGauge (spectraReflectionProduct U V) := by
    apply cfc_nonneg
    intro z _
    exact Complex.zero_le_real.mpr (by positivity)
  have hu_cont : ContinuousOn (fun z : ℂ => (2⁻¹ : ℂ) • (1 + z))
      (spectrum ℂ (spectraReflectionProduct U V)) := by
    fun_prop
  have hstaru_cont : ContinuousOn (fun z : ℂ => star ((2⁻¹ : ℂ) • (1 + z)))
      (spectrum ℂ (spectraReflectionProduct U V)) := by
    fun_prop
  have hgsq : cfc cosineGauge (spectraReflectionProduct U V) *
      cfc cosineGauge (spectraReflectionProduct U V) =
      star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V := by
    rw [spectraCanonicalIntertwiner_eq_cfc U V,
      ← cfc_star (fun z : ℂ => (2⁻¹ : ℂ) • (1 + z)) (spectraReflectionProduct U V),
      ← cfc_mul _ _ _ hstaru_cont hu_cont,
      ← cfc_mul _ _ _ continuous_cosineGauge.continuousOn
        continuous_cosineGauge.continuousOn]
    exact cfc_congr fun z _ => cosineGauge_mul_self z
  have habs0 : (0 : H →L[ℂ] H) ≤
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) :=
    spectraOperatorAbsoluteValue_nonneg _
  have habssq := spectraOperatorAbsoluteValue_mul_self
    (spectraCanonicalIntertwiner U V)
  calc spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
      = CFC.sqrt (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V) :=
        (CFC.sqrt_unique habssq habs0).symm
    _ = cfc cosineGauge (spectraReflectionProduct U V) :=
        CFC.sqrt_unique hgsq hg0

/-- The polar factor of the midpoint is the principal half-phase.

The two operators are unitary factors in the same polar decomposition of the
canonical intertwiner: the modulus of the intertwiner is `cfc` of the cosine
gauge, the half-phase times the gauge is the scalar midpoint, and the acute
modulus is invertible, so the factor is unique. -/
theorem spectraDirectRotation_eq_reflectionProductHalfPhase
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute =
      spectraReflectionProductHalfPhase U V hacute := by
  have hneg : (-1 : ℂ) ∉ spectrum ℂ (spectraReflectionProduct U V) :=
    neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  have hphpcont : ContinuousOn principalHalfPhase
      (spectrum ℂ (spectraReflectionProduct U V)) :=
    continuousOn_principalHalfPhase hneg
  -- Both operators satisfy `X * |S| = S`.
  have hW : spectraReflectionProductHalfPhase U V hacute *
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V := by
    rw [spectraOperatorAbsoluteValue_intertwiner_eq_cfc U V,
      spectraReflectionProductHalfPhase,
      ← cfc_mul _ _ _ hphpcont continuous_cosineGauge.continuousOn,
      spectraCanonicalIntertwiner_eq_cfc U V]
    exact cfc_congr fun z hz =>
      principalHalfPhase_mul_cosineGauge fun h => hneg (h ▸ hz)
  have hP : spectraDirectRotation U V hacute *
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V :=
    spectraDirectRotation_decomposition U V hacute
  obtain ⟨v, hv⟩ := isUnit_spectraCanonicalAbsoluteValue U V hacute
  rw [← hv] at hW hP
  exact (Units.mul_left_inj v).mp (hP.trans hW.symm)

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
  have hnegUV : (-1 : ℂ) ∉ spectrum ℂ (spectraReflectionProduct U V) :=
    neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase V U hacute.symm,
    spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute,
    spectraReflectionProductHalfPhase, spectraReflectionProductHalfPhase,
    ← star_spectraReflectionProduct U V]
  -- `star R = cfc star R`, so composition turns the left side into a single
  -- `cfc` against `R`, and conjugating the half-phase matches the right side.
  have hstarR : star (spectraReflectionProduct U V) =
      cfc (fun z : ℂ => star z) (spectraReflectionProduct U V) := by
    have h := cfc_star (R := ℂ) (fun z : ℂ => z) (spectraReflectionProduct U V)
    rw [cfc_id' ℂ (spectraReflectionProduct U V)] at h
    exact h.symm
  have hg : ContinuousOn principalHalfPhase
      ((fun z : ℂ => star z) '' spectrum ℂ (spectraReflectionProduct U V)) := by
    apply continuousOn_principalHalfPhase
    intro hmem
    obtain ⟨z, hz, hz1⟩ := hmem
    apply hnegUV
    have hzeq : z = -1 := by
      have := congrArg star hz1
      simpa using this
    rwa [hzeq] at hz
  rw [hstarR,
    ← cfc_comp principalHalfPhase (fun z : ℂ => star z)
      (spectraReflectionProduct U V) hnormal hg continuous_star.continuousOn,
    show (principalHalfPhase ∘ fun z : ℂ => star z) =
        fun z : ℂ => star (principalHalfPhase z) from
      funext fun z => (star_principalHalfPhase z).symm,
    cfc_star]

/-- Positive-real-part branch condition for the canonical direct rotation.

`W + W⋆` is `cfc` of `z ↦ 2 * re (principalHalfPhase z)`, which is
nonnegative on the unit circle because `re (1 + z) ≥ 0` there; expanding
`⟪(W + W⋆) x, x⟫` identifies it with `2 * re ⟪W x, x⟫`. -/
theorem spectraDirectRotation_real_inner_nonneg
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (x : H) :
    0 ≤ Complex.re ⟪spectraDirectRotation U V hacute x, x⟫_ℂ := by
  rw [spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute]
  have hneg : (-1 : ℂ) ∉ spectrum ℂ (spectraReflectionProduct U V) :=
    neg_one_not_mem_spectrum_spectraReflectionProduct U V hacute
  have hnormal : IsStarNormal (spectraReflectionProduct U V) :=
    isStarNormal_of_mem_unitary (spectraReflectionProduct_mem_unitary U V)
  have hphpcont : ContinuousOn principalHalfPhase
      (spectrum ℂ (spectraReflectionProduct U V)) :=
    continuousOn_principalHalfPhase hneg
  have hstarcont : ContinuousOn (fun z : ℂ => star (principalHalfPhase z))
      (spectrum ℂ (spectraReflectionProduct U V)) :=
    continuous_star.comp_continuousOn hphpcont
  -- `W + W⋆` is nonnegative.
  have hpos : (0 : H →L[ℂ] H) ≤ spectraReflectionProductHalfPhase U V hacute +
      star (spectraReflectionProductHalfPhase U V hacute) := by
    have hadd := cfc_add (R := ℂ) (a := spectraReflectionProduct U V)
      principalHalfPhase (fun z => star (principalHalfPhase z))
      hphpcont hstarcont
    have hstar := cfc_star (R := ℂ) principalHalfPhase
      (spectraReflectionProduct U V)
    rw [spectraReflectionProductHalfPhase, ← hstar, ← hadd]
    apply cfc_nonneg
    intro z hz
    have hzne : z ≠ -1 := fun h => hneg (h ▸ hz)
    have hz1 : ‖z‖ = 1 := spectrum_spectraReflectionProduct_abs_eq_one U V hz
    have hre : (principalHalfPhase z).re = (1 + z).re / ‖1 + z‖ := by
      rw [principalHalfPhase, if_neg hzne, div_eq_inv_mul,
        ← Complex.ofReal_inv, Complex.re_ofReal_mul, inv_mul_eq_div]
    have hnum : 0 ≤ (1 + z).re := by
      have habs := Complex.abs_re_le_norm z
      rw [hz1] at habs
      have hb := abs_le.mp habs
      simp only [Complex.add_re, Complex.one_re]
      linarith [hb.1]
    have hre0 : 0 ≤ (principalHalfPhase z).re := by
      rw [hre]
      positivity
    calc (0 : ℂ) ≤ ((2 * (principalHalfPhase z).re : ℝ) : ℂ) :=
          Complex.zero_le_real.mpr (by linarith)
      _ = principalHalfPhase z + star (principalHalfPhase z) := by
          rw [Complex.star_def, Complex.add_conj]
  -- Expand the quadratic form of `W + W⋆`.
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos
  have hx := hp.inner_nonneg_left x
  have hexpand : ⟪(spectraReflectionProductHalfPhase U V hacute +
        star (spectraReflectionProductHalfPhase U V hacute)) x, x⟫_ℂ =
      ⟪spectraReflectionProductHalfPhase U V hacute x, x⟫_ℂ +
        (starRingEnd ℂ) ⟪spectraReflectionProductHalfPhase U V hacute x, x⟫_ℂ := by
    rw [ContinuousLinearMap.add_apply, inner_add_left]
    congr 1
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [hexpand, Complex.add_conj] at hx
  have := Complex.zero_le_real.mp hx
  linarith

/-- Uniqueness of the acute square-root branch.

Route: any unitary `W` squaring to the reflection product, commuting with it,
and with positive-real-part inner products must agree with the principal
half-phase on each spectral arc; this is the continuous-functional-calculus
branch-selection argument and needs a spectral-multiplicity API that is not
yet available. -/
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
  sorry

/-- Scalar shorter-arc inequality on a principal two-plane.

Route: write `z = exp (I θ)` and `w = exp (I φ)` with `2 φ ≡ θ [2π]`; the
half-phase displacement is `|exp (I θ/2) - 1| = 2 |sin (θ/4)| ≤ |w - 1|`
because the principal branch takes the shorter arc.  Needs the
`Real.Angle` halving API, which is not yet available. -/
theorem principalHalfPhase_displacement_minimal_scalar
    {z w : ℂ} (hz : ‖z‖ = 1) (hzneg : z ≠ -1)
    (hw : ‖w‖ = 1) (htransport : w * w = z) :
    ‖principalHalfPhase z - 1‖ ≤ ‖w - 1‖ := by
  sorry

/-- Operator-norm minimality of the acute direct rotation among unitaries
transporting the source projection to the target projection.

Route: the Halmos two-projection decomposition splits `H` into the common
subspaces and a direct integral of principal two-planes; on each plane the
displacement of the direct rotation is the scalar shorter-arc bound against
any transporting unitary.  The two-projection decomposition is not yet
formalized. -/
theorem spectraDirectRotation_minimal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : H →L[ℂ] H) (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hintertwine : W * projection U = projection V * W) :
    ‖spectraDirectRotation U V hacute - 1‖ ≤ ‖W - 1‖ := by
  sorry

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
