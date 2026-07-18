/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import ForMathlib.Analysis.InnerProductSpace.CoerciveUnit

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

/-- The real part of the quadratic form is unchanged by taking the
adjoint of a bounded operator. -/
private theorem re_inner_star_apply (T : H →L[ℂ] H) (x : H) :
    RCLike.re ⟪star T x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact inner_re_symm x (T x)

/-- The Hermitian part of the acute direct rotation is twice the
positive modulus of the canonical midpoint. -/
theorem spectraDirectRotation_add_star_eq_two_smul_absoluteValue
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute +
        star (spectraDirectRotation U V hacute) =
      (2 : ℂ) • spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner U V) := by
  have hdecomp :
      spectraDirectRotation U V hacute *
          spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
        spectraCanonicalIntertwiner U V :=
    spectraDirectRotation_decomposition U V hacute
  have hleft :
      star (spectraDirectRotation U V hacute) *
          spectraCanonicalIntertwiner U V =
        spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) := by
    calc
      star (spectraDirectRotation U V hacute) *
          spectraCanonicalIntertwiner U V =
        star (spectraDirectRotation U V hacute) *
          (spectraDirectRotation U V hacute *
            spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)) := by
              rw [hdecomp]
      _ = (star (spectraDirectRotation U V hacute) *
            spectraDirectRotation U V hacute) *
          spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) := by
              rw [mul_assoc]
      _ = spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) := by
              rw [star_spectraDirectRotation_mul_self U V hacute, one_mul]
  have hstarR :
      star (spectraDirectRotation U V hacute) *
          spectraReflectionProduct U V =
        spectraDirectRotation U V hacute := by
    calc
      star (spectraDirectRotation U V hacute) *
          spectraReflectionProduct U V =
        star (spectraDirectRotation U V hacute) *
          (spectraDirectRotation U V hacute *
            spectraDirectRotation U V hacute) := by
              rw [spectraDirectRotation_sq U V hacute]
      _ = (star (spectraDirectRotation U V hacute) *
            spectraDirectRotation U V hacute) *
          spectraDirectRotation U V hacute := by
              rw [mul_assoc]
      _ = spectraDirectRotation U V hacute := by
              rw [star_spectraDirectRotation_mul_self U V hacute, one_mul]
  have hmid := spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V
  have hmul := congrArg
    (fun T : H →L[ℂ] H => star (spectraDirectRotation U V hacute) * T) hmid
  have htwice :
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) +
          spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
        star (spectraDirectRotation U V hacute) +
          spectraDirectRotation U V hacute := by
    simpa only [mul_add, hleft, mul_one, hstarR] using hmul
  calc
    spectraDirectRotation U V hacute +
        star (spectraDirectRotation U V hacute) =
      star (spectraDirectRotation U V hacute) +
        spectraDirectRotation U V hacute := add_comm _ _
    _ = spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) +
        spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) := htwice.symm
    _ = (2 : ℂ) • spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner U V) := by rw [two_smul]

/-- The positive midpoint modulus has strictly positive quadratic form on
nonzero vectors in the acute regime. -/
theorem spectraCanonicalAbsoluteValue_inner_pos
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : H} (hx : x ≠ 0) :
    0 < Complex.re ⟪spectraOperatorAbsoluteValue
      (spectraCanonicalIntertwiner U V) x, x⟫_ℂ := by
  let B := spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  change 0 < RCLike.re ⟪B x, x⟫_ℂ
  have hBnonneg : (0 : H →L[ℂ] H) ≤ B :=
    spectraOperatorAbsoluteValue_nonneg _
  have hBpositive := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hBnonneg
  have hBform : ∀ z : H, 0 ≤ RCLike.re ⟪B z, z⟫_ℂ := fun z =>
    hBpositive.re_inner_nonneg_left z
  have hBsym : (B : H →ₗ[ℂ] H).IsSymmetric :=
    (spectraOperatorAbsoluteValue_isSelfAdjoint _).isSymmetric
  have hBinj : Function.Injective B :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp
      (isUnit_spectraCanonicalAbsoluteValue U V hacute)).1
  have hne : RCLike.re ⟪B x, x⟫_ℂ ≠ 0 := by
    intro hzero
    have hsq := ForMathlib.ContinuousLinearMap.norm_apply_sq_le_of_positive
      hBsym hBform x
    have hsq0 : ‖B x‖ ^ 2 ≤ 0 := by
      calc
        ‖B x‖ ^ 2 ≤ ‖B‖ * RCLike.re ⟪B x, x⟫_ℂ := hsq
        _ = 0 := by rw [hzero, mul_zero]
    have hBx : B x = 0 := by
      apply norm_eq_zero.mp
      exact sq_eq_zero_iff.mp (le_antisymm hsq0 (sq_nonneg _))
    apply hx
    apply hBinj
    simpa using hBx
  exact lt_of_le_of_ne (hBform x) (Ne.symm hne)

/-- The acute direct rotation has strictly positive numerical real part on
nonzero vectors. -/
theorem spectraDirectRotation_real_inner_pos
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : H} (hx : x ≠ 0) :
    0 < Complex.re ⟪spectraDirectRotation U V hacute x, x⟫_ℂ := by
  let D := spectraDirectRotation U V hacute
  let B := spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  change 0 < RCLike.re ⟪D x, x⟫_ℂ
  have hsum : D + star D = (2 : ℂ) • B := by
    simpa [D, B] using
      spectraDirectRotation_add_star_eq_two_smul_absoluteValue U V hacute
  have hsum' : D + star D = B + B := by
    simpa only [two_smul] using hsum
  have hreal :
      2 * RCLike.re ⟪D x, x⟫_ℂ =
        2 * RCLike.re ⟪B x, x⟫_ℂ := by
    have h := congrArg
      (fun T : H →L[ℂ] H => RCLike.re ⟪T x, x⟫_ℂ) hsum'
    have h' :
        RCLike.re ⟪D x, x⟫_ℂ + RCLike.re ⟪D x, x⟫_ℂ =
          RCLike.re ⟪B x, x⟫_ℂ + RCLike.re ⟪B x, x⟫_ℂ := by
      simpa only [add_apply, inner_add_left, map_add,
        re_inner_star_apply] using h
    linarith
  have hBpos : 0 < RCLike.re ⟪B x, x⟫_ℂ := by
    simpa [B] using spectraCanonicalAbsoluteValue_inner_pos U V hacute hx
  nlinarith

/-- Uniqueness of the acute square-root branch.

This proof avoids a spectral-multiplicity decomposition.  The canonical
branch has strictly positive numerical real part because its Hermitian part
is twice the positive invertible midpoint modulus.  The sum of any competing
nonnegative-real-part unitary square root with the canonical branch therefore
has trivial adjoint kernel and hence dense range.  The commuting quadratic
factorization then forces the two square roots to agree. -/
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
  let D := spectraDirectRotation U V hacute
  have hWstar : Commute W (star W) := by
    rw [commute_iff_eq]
    exact (Unitary.mul_star_self_of_mem hWunit).trans
      (Unitary.star_mul_self_of_mem hWunit).symm
  have hstarSq : star (spectraReflectionProduct U V) = star W * star W := by
    symm
    simpa only [star_mul] using congrArg star hsq
  have hstarR_W : Commute (star (spectraReflectionProduct U V)) W := by
    rw [hstarSq, commute_iff_eq]
    calc
      (star W * star W) * W = star W * (star W * W) := by rw [mul_assoc]
      _ = star W * (W * star W) := by rw [hWstar.eq]
      _ = (star W * W) * star W := by rw [mul_assoc]
      _ = (W * star W) * star W := by rw [hWstar.eq]
      _ = W * (star W * star W) := by rw [mul_assoc]
  have hDW : Commute D W := by
    dsimp [D]
    rw [spectraDirectRotation_eq_reflectionProductHalfPhase U V hacute,
      spectraReflectionProductHalfPhase]
    exact hcomm.symm.cfc hstarR_W principalHalfPhase
  have hWD : Commute W D := hDW.symm
  have hDsq : D * D = spectraReflectionProduct U V := by
    simpa [D] using spectraDirectRotation_sq U V hacute
  have hfactor : (W - D) * (W + D) = 0 := by
    calc
      (W - D) * (W + D) =
          W * W + W * D - (D * W + D * D) := by noncomm_ring
      _ = spectraReflectionProduct U V + D * W -
          (D * W + spectraReflectionProduct U V) := by
            rw [hWD.eq, hsq, hDsq]
      _ = 0 := by abel
  have hDpos : ∀ {x : H}, x ≠ 0 → 0 < RCLike.re ⟪D x, x⟫_ℂ := by
    intro x hx
    simpa [D] using spectraDirectRotation_real_inner_pos U V hacute hx
  have hstarWre : ∀ x : H, 0 ≤ RCLike.re ⟪star W x, x⟫_ℂ := by
    intro x
    rw [re_inner_star_apply]
    exact hre x
  have hstarDpos : ∀ {x : H}, x ≠ 0 →
      0 < RCLike.re ⟪star D x, x⟫_ℂ := by
    intro x hx
    rw [re_inner_star_apply]
    exact hDpos hx
  have ker_add_eq_bot
      (A B : H →L[ℂ] H)
      (hAre : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_ℂ)
      (hBpos : ∀ {x}, x ≠ 0 → 0 < RCLike.re ⟪B x, x⟫_ℂ) :
      (A + B).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hxker
    change (A + B) x = 0 at hxker
    have hAB : A x = -B x := by
      rw [eq_neg_iff_add_eq_zero]
      simpa only [add_apply] using hxker
    by_contra hx
    have hA0 := hAre x
    have hB0 := hBpos hx
    have hreEq : RCLike.re ⟪A x, x⟫_ℂ =
        -RCLike.re ⟪B x, x⟫_ℂ := by
      rw [hAB, inner_neg_left]
      simp
    linarith
  have hstarSumKer : (star W + star D).ker = ⊥ :=
    ker_add_eq_bot (star W) (star D) hstarWre hstarDpos
  have hrangeOrth : (W + D).rangeᗮ = ⊥ := by
    calc
      (W + D).rangeᗮ = (W + D).adjoint.ker :=
        (W + D).orthogonal_range
      _ = (star W + star D).ker := by
        rw [← ContinuousLinearMap.star_eq_adjoint, star_add]
      _ = ⊥ := hstarSumKer
  have hdense : (W + D).range.topologicalClosure = ⊤ := by
    calc
      (W + D).range.topologicalClosure = (W + D).rangeᗮᗮ :=
        (Submodule.orthogonal_orthogonal_eq_closure _).symm
      _ = ⊤ := by rw [hrangeOrth]; simp
  have hrange_le : (W + D).range ≤ (W - D).ker := by
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    change (W - D) ((W + D) x) = 0
    have h := congrArg (fun T : H →L[ℂ] H => T x) hfactor
    simpa only [mul_apply_eq_comp, Function.comp_apply, zero_apply] using h
  have hclosure_le : (W + D).range.topologicalClosure ≤ (W - D).ker :=
    Submodule.topologicalClosure_minimal _ hrange_le (W - D).isClosed_ker
  rw [hdense] at hclosure_le
  rw [← sub_eq_zero]
  ext x
  have hxker : x ∈ (W - D).ker := hclosure_le (by simp)
  exact LinearMap.mem_ker.mp hxker

/-- The commutation hypothesis in `spectraDirectRotation_unique` follows
formally from the square identity. -/
theorem spectraDirectRotation_unique_of_sq
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : H →L[ℂ] H)
    (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hsq : W * W = spectraReflectionProduct U V)
    (hre : ∀ x, 0 ≤ Complex.re ⟪W x, x⟫_ℂ) :
    W = spectraDirectRotation U V hacute := by
  apply spectraDirectRotation_unique U V hacute W hWunit hsq
  · rw [commute_iff_eq, ← hsq]
    exact (mul_assoc W W W).symm
  · exact hre

/-- Scalar shorter-arc inequality on a principal two-plane.  Any unit `w`
with `w² = z` is `±` the principal half-phase; the principal branch has
nonnegative real part, so its displacement from `1` is the smaller of the
two. -/
theorem principalHalfPhase_displacement_minimal_scalar
    {z w : ℂ} (hz : ‖z‖ = 1) (hzneg : z ≠ -1)
    (hw : ‖w‖ = 1) (htransport : w * w = z) :
    ‖principalHalfPhase z - 1‖ ≤ ‖w - 1‖ := by
  have hsq := principalHalfPhase_sq_of_abs_eq_one hz hzneg
  have hfactor : (w - principalHalfPhase z) * (w + principalHalfPhase z)
      = 0 := by
    linear_combination htransport - hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · rw [← sub_eq_zero.mp h]
  · have hw_eq : w = -principalHalfPhase z := by linear_combination h
    -- the principal branch has nonnegative real part
    have hre : 0 ≤ (principalHalfPhase z).re := by
      rw [principalHalfPhase, if_neg hzneg, Complex.div_ofReal_re]
      have hz_re : -1 ≤ z.re := by
        have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        have := (abs_le.mp habs).1
        linarith [hz ▸ this]
      have hnum : 0 ≤ (1 + z).re := by
        simp only [Complex.add_re, Complex.one_re]
        linarith
      exact div_nonneg hnum (norm_nonneg _)
    -- displacement comparison through the real part
    have hcmp : ‖principalHalfPhase z - 1‖ ^ 2 ≤
        ‖principalHalfPhase z + 1‖ ^ 2 := by
      have e1 : ‖principalHalfPhase z - 1‖ ^ 2 =
          Complex.normSq (principalHalfPhase z - 1) := by
        rw [Complex.normSq_eq_norm_sq]
      have e2 : ‖principalHalfPhase z + 1‖ ^ 2 =
          Complex.normSq (principalHalfPhase z + 1) := by
        rw [Complex.normSq_eq_norm_sq]
      rw [e1, e2]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      nlinarith [hre]
    have hcmp' : ‖principalHalfPhase z - 1‖ ≤
        ‖principalHalfPhase z + 1‖ := by
      have hs := Real.sqrt_le_sqrt hcmp
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs
    calc ‖principalHalfPhase z - 1‖
        ≤ ‖principalHalfPhase z + 1‖ := hcmp'
      _ = ‖w - 1‖ := by
          rw [hw_eq, show -principalHalfPhase z - 1 =
            -(principalHalfPhase z + 1) from by ring, norm_neg]

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
