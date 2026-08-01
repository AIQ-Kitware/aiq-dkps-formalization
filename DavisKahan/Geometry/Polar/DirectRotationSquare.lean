/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Geometry.Polar.DirectRotation
import DavisKahan.Geometry.Halmos.TwoProjections
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit

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

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace Experimental

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The principal half-phase on the unit circle away from `-1`.  The value at
`-1` is immaterial once the spectral exclusion theorem is supplied. -/
noncomputable def principalHalfPhase (z : ℂ) : ℂ :=
  if z = -1 then 1 else (1 + z) / (‖1 + z‖ : ℂ)

omit [CompleteSpace H] in
/-- **A coercive real quadratic form gives a lower bound on the operator.**

If `c ‖x‖² ≤ Re ⟪C y, x⟫` and `‖y‖ = ‖x‖`, then `c ‖y‖ ≤ ‖C y‖`: Cauchy–Schwarz
turns the form bound into a norm bound and the common norm cancels.

`spectraDirectRotation_minimal` runs this twice, at `U` and at `Uᗮ`, two hundred
lines apart — **a proof duplicating itself rather than duplicating a sibling**,
which is why neither copy is visible to a reader.  See `{lane:DK-LONGPROOF-6}`. -/
theorem mul_norm_le_norm_apply_of_re_inner_ge {C : H →L[ℂ] H} {c : ℝ} {x y : H}
    (hform : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪C y, x⟫_ℂ) (hnorm : ‖y‖ = ‖x‖) :
    c * ‖y‖ ≤ ‖C y‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero] at hnorm
    rw [norm_eq_zero.mp hnorm]
    simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hcs : RCLike.re ⟪C y, x⟫_ℂ ≤ ‖C y‖ * ‖x‖ :=
      (RCLike.re_le_norm ⟪C y, x⟫_ℂ).trans (norm_inner_le_norm (C y) x)
    have hmul : (c * ‖x‖) * ‖x‖ ≤ ‖C y‖ * ‖x‖ := by
      calc
        (c * ‖x‖) * ‖x‖ = c * ‖x‖ ^ 2 := by ring
        _ ≤ RCLike.re ⟪C y, x⟫_ℂ := hform
        _ ≤ ‖C y‖ * ‖x‖ := hcs
    rw [hnorm]
    nlinarith only [hmul, hxpos]

/-- **The principal half-phase of a unit complex number has nonnegative real
part.**

On the unit circle `Re (1 + z) = 1 + Re z ≥ 0`, and dividing by a positive norm
keeps the sign.  Proved twice below by slightly different routes, inside two
*operator* theorems where a scalar fact about `principalHalfPhase` is not where
anyone would look for it.  See `{lane:DK-LONGPROOF-6}`. -/
theorem principalHalfPhase_re_nonneg {z : ℂ} (hz : ‖z‖ = 1) (hzneg : z ≠ -1) :
    0 ≤ (principalHalfPhase z).re := by
  rw [principalHalfPhase, if_neg hzneg, Complex.div_ofReal_re]
  have hnum : 0 ≤ (1 + z).re := by
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [hz] at habs
    simp only [Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp habs).1]
  exact div_nonneg hnum (norm_nonneg _)

/-- **The compression identity behind both diagonal blocks of the direct
rotation**, as a statement about a ring.

`(P D P) C = (C P) C` whenever `C` commutes with `P`, `D C = S`, `S P = Q P`,
`C² = Cos` and `Cos P = P Q P`.  The two projection theorems below run this
ten-line `calc` verbatim, once with `P = projection U` and once with
`P = complementaryProjection U`.  See `{lane:DK-LONGPROOF-6}`.

Their `hSP` and `hCosP` hypotheses look identical too, but are *not* the same
statement: each proof names its own projection `P`, and the two are proved from
different lemmas.  Only this step is shared, which is why only this step is
lifted. -/
theorem mul_compression_mul_eq_of_commute {R : Type*} [Ring R]
    {C D P Q S Cos : R} (hCP : Commute C P) (hDC : D * C = S)
    (hSP : S * P = Q * P) (hC2 : C * C = Cos) (hCosP : Cos * P = P * Q * P) :
    (P * D * P) * C = (C * P) * C := by
  calc
    (P * D * P) * C = P * D * (P * C) := by noncomm_ring
    _ = P * D * (C * P) := by rw [hCP.eq]
    _ = P * (D * C) * P := by noncomm_ring
    _ = P * S * P := by rw [hDC]
    _ = P * Q * P := by rw [mul_assoc, hSP, ← mul_assoc]
    _ = (C * C) * P := by rw [hC2, hCosP]
    _ = C * (C * P) := by rw [mul_assoc]
    _ = C * (P * C) := by rw [hCP.eq]
    _ = (C * P) * C := by rw [← mul_assoc]

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
    simp [star_div₀, Complex.conj_ofReal]

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
    (_hacute : IsAcute U V) : H →L[ℂ] H :=
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

omit [CompleteSpace H] in
/-- Acuteness is symmetric in the two subspaces. -/
theorem _root_.TauCeti.DavisKahan.IsAcute.symm
    {U V : Submodule ℂ H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsAcute U V) : IsAcute V U := by
  show subspaceGap V U < 1
  rw [subspaceGap, Submodule.projectionGap_comm]
  exact h

/-- The scalar cosine gauge `‖1 + z‖ / 2` of the reflection product. -/
noncomputable def cosineGauge (z : ℂ) : ℂ := ((‖1 + z‖ / 2 : ℝ) : ℂ)

/-- The cosine gauge is continuous. -/
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
    have hre0 : 0 ≤ (principalHalfPhase z).re :=
      principalHalfPhase_re_nonneg hz1 hzne
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
    rw [add_apply, inner_add_left]
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
    have hsq := TauCeti.ContinuousLinearMap.norm_apply_sq_le_of_positive
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
    (_hw : ‖w‖ = 1) (htransport : w * w = z) :
    ‖principalHalfPhase z - 1‖ ≤ ‖w - 1‖ := by
  have hsq := principalHalfPhase_sq_of_abs_eq_one hz hzneg
  have hfactor : (w - principalHalfPhase z) * (w + principalHalfPhase z)
      = 0 := by
    linear_combination htransport - hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · rw [← sub_eq_zero.mp h]
  · have hw_eq : w = -principalHalfPhase z := by linear_combination h
    -- the principal branch has nonnegative real part
    have hre : 0 ≤ (principalHalfPhase z).re :=
      principalHalfPhase_re_nonneg hz hzneg
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

/-- Squared displacement of a unitary from the identity. -/
theorem norm_sub_one_apply_sq_of_mem_unitary
    (T : H →L[ℂ] H) (hT : T ∈ unitary (H →L[ℂ] H)) (x : H) :
    ‖(T - 1) x‖ ^ 2 =
      2 * ‖x‖ ^ 2 - 2 * RCLike.re ⟪T x, x⟫_ℂ := by
  let u : unitary (H →L[ℂ] H) := ⟨T, hT⟩
  have hnorm : ‖T x‖ = ‖x‖ := Unitary.norm_map u x
  rw [sub_apply, one_apply_eq_self, norm_sub_sq (𝕜 := ℂ), hnorm]
  ring

/-- Every acute direct rotation lies in the closed radius-`√2` ball around
`1`. -/
theorem norm_spectraDirectRotation_sub_one_le_sqrt_two
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ‖spectraDirectRotation U V hacute - 1‖ ≤ Real.sqrt 2 := by
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  have hDunit : D ∈ unitary (H →L[ℂ] H) :=
    spectraDirectRotation_mem_unitary U V hacute
  refine (D - 1).opNorm_le_bound (Real.sqrt_nonneg 2) ?_
  intro x
  have hsq : ‖(D - 1) x‖ ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := by
    rw [norm_sub_one_apply_sq_of_mem_unitary D hDunit x]
    have hre : 0 ≤ RCLike.re ⟪D x, x⟫_ℂ := by
      rw [RCLike.re_eq_complex_re]
      simpa only [D] using
        spectraDirectRotation_real_inner_nonneg U V hacute x
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    rw [mul_pow, hsqrt]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg x))).mp hsq

/-- Numerical real part of the direct rotation equals the quadratic form of
the positive canonical modulus. -/
theorem re_inner_spectraDirectRotation_eq_absoluteValue
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (x : H) :
    RCLike.re ⟪spectraDirectRotation U V hacute x, x⟫_ℂ =
      RCLike.re ⟪spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner U V) x, x⟫_ℂ := by
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  have hsum : D + star D = C + C := by
    have h := spectraDirectRotation_add_star_eq_two_smul_absoluteValue
      U V hacute
    simpa only [two_smul] using h
  have h := congrArg
    (fun T : H →L[ℂ] H => RCLike.re ⟪T x, x⟫_ℂ) hsum
  have h' :
      RCLike.re ⟪D x, x⟫_ℂ + RCLike.re ⟪D x, x⟫_ℂ =
        RCLike.re ⟪C x, x⟫_ℂ + RCLike.re ⟪C x, x⟫_ℂ := by
    simpa only [add_apply, inner_add_left, map_add,
      re_inner_star_apply] using h
  change RCLike.re ⟪D x, x⟫_ℂ = RCLike.re ⟪C x, x⟫_ℂ
  linarith only [h']

/-- The source diagonal compression of the direct rotation is the positive
Halmos cosine. -/
theorem projection_mul_spectraDirectRotation_mul_projection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    projection U * spectraDirectRotation U V hacute * projection U =
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) *
        projection U := by
  let B := spectraCanonicalAbsoluteValueUnit U V hacute
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  let P : H →L[ℂ] H := projection U
  let Q : H →L[ℂ] H := projection V
  let S : H →L[ℂ] H := spectraCanonicalIntertwiner U V
  have hDB : D * C = S := by
    simpa only [ContinuousLinearMap.mul_def] using
      spectraDirectRotation_decomposition U V hacute
  have hCP : Commute C P := spectraCanonicalAbsoluteValue_commute_projection U V
  have hC2 : C * C = halmosCosineSq U V :=
    spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq U V
  have hSP : S * P = Q * P := by
    change
      (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) * U.starProjection =
      V.starProjection * U.starProjection
    have hP := projection_sq U
    have hPcP := complementaryProjection_mul_projection U
    noncomm_ring [hP, hPcP]
  have hCosP : halmosCosineSq U V * P = P * Q * P := by
    change
      (U.starProjection * V.starProjection * U.starProjection +
        Uᗮ.starProjection * Vᗮ.starProjection * Uᗮ.starProjection) *
        U.starProjection =
      U.starProjection * V.starProjection * U.starProjection
    have hP := projection_sq U
    have hPcP := complementaryProjection_mul_projection U
    noncomm_ring [hP, hPcP]
  have hmul : (P * D * P) * C = (C * P) * C :=
    mul_compression_mul_eq_of_commute hCP hDB hSP hC2 hCosP
  have hmul' :
      (P * D * P) * (B : H →L[ℂ] H) =
        (C * P) * (B : H →L[ℂ] H) := by
    simpa [B, C] using hmul
  change P * D * P = C * P
  let Binv : H →L[ℂ] H := (↑(B⁻¹) : H →L[ℂ] H)
  calc
    P * D * P = (P * D * P) * 1 := (mul_one _).symm
    _ = (P * D * P) * ((B : H →L[ℂ] H) * Binv) := by
      rw [B.mul_inv]
    _ = ((P * D * P) * (B : H →L[ℂ] H)) * Binv := by
      rw [← mul_assoc]
    _ = ((C * P) * (B : H →L[ℂ] H)) * Binv := by rw [hmul']
    _ = (C * P) * ((B : H →L[ℂ] H) * Binv) := by rw [mul_assoc]
    _ = C * P := by rw [B.mul_inv, mul_one]

/-- The complementary diagonal compression of the direct rotation is the
positive Halmos cosine. -/
theorem complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    complementaryProjection U * spectraDirectRotation U V hacute *
        complementaryProjection U =
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) *
        complementaryProjection U := by
  let B := spectraCanonicalAbsoluteValueUnit U V hacute
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  let P : H →L[ℂ] H := complementaryProjection U
  let Q : H →L[ℂ] H := complementaryProjection V
  let S : H →L[ℂ] H := spectraCanonicalIntertwiner U V
  have hDB : D * C = S := by
    simpa only [ContinuousLinearMap.mul_def] using
      spectraDirectRotation_decomposition U V hacute
  have hCP : Commute C P := by
    change Commute C Uᗮ.starProjection
    rw [Submodule.starProjection_orthogonal']
    rw [commute_iff_eq]
    change C * (1 - U.starProjection) = (1 - U.starProjection) * C
    rw [mul_sub, mul_one, sub_mul, one_mul,
      (spectraCanonicalAbsoluteValue_commute_projection U V).eq]
  have hSP : S * P = Q * P := by
    change
      (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) * Uᗮ.starProjection =
      Vᗮ.starProjection * Uᗮ.starProjection
    have hPPc := projection_mul_complementaryProjection U
    have hPc := complementaryProjection_sq U
    noncomm_ring [hPPc, hPc]
  have hC2 : C * C = halmosCosineSq U V :=
    spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq U V
  have hCosP : halmosCosineSq U V * P = P * Q * P := by
    change
      (U.starProjection * V.starProjection * U.starProjection +
        Uᗮ.starProjection * Vᗮ.starProjection * Uᗮ.starProjection) *
        Uᗮ.starProjection =
      Uᗮ.starProjection * Vᗮ.starProjection * Uᗮ.starProjection
    have hPPc := projection_mul_complementaryProjection U
    have hPc := complementaryProjection_sq U
    noncomm_ring [hPPc, hPc]
  have hmul : (P * D * P) * C = (C * P) * C :=
    mul_compression_mul_eq_of_commute hCP hDB hSP hC2 hCosP
  have hmul' :
      (P * D * P) * (B : H →L[ℂ] H) =
        (C * P) * (B : H →L[ℂ] H) := by
    simpa [B, C] using hmul
  change P * D * P = C * P
  let Binv : H →L[ℂ] H := (↑(B⁻¹) : H →L[ℂ] H)
  calc
    P * D * P = (P * D * P) * 1 := (mul_one _).symm
    _ = (P * D * P) * ((B : H →L[ℂ] H) * Binv) := by
      rw [B.mul_inv]
    _ = ((P * D * P) * (B : H →L[ℂ] H)) * Binv := by
      rw [← mul_assoc]
    _ = ((C * P) * (B : H →L[ℂ] H)) * Binv := by rw [hmul']
    _ = (C * P) * ((B : H →L[ℂ] H) * Binv) := by rw [mul_assoc]
    _ = C * P := by rw [B.mul_inv, mul_one]

/-- **A positive operator whose inverse is small is coercive.**

If `R C = 1` with `R` positive self-adjoint and `‖R‖ ≤ c⁻¹`, then
`c ‖z‖² ≤ Re ⟪C z, z⟫`.  This is the analytic core of
`spectraDirectRotation_minimal` below, where it was fifty lines deep and
unnamed; nothing in it is about direct rotations. -/
private theorem re_inner_ge_of_inverse_norm_le
    {C R : H →L[ℂ] H} {c : ℝ} (hc : 0 < c) (hRC : R * C = 1)
    (hRsa : IsSelfAdjoint R) (hRpos : ∀ z : H, 0 ≤ RCLike.re ⟪R z, z⟫_ℂ)
    (hRnorm : ‖R‖ ≤ c⁻¹) (hCpos : ∀ z : H, 0 ≤ RCLike.re ⟪C z, z⟫_ℂ) (z : H) :
    c * ‖z‖ ^ 2 ≤ RCLike.re ⟪C z, z⟫_ℂ := by
  have hRbound := TauCeti.ContinuousLinearMap.norm_apply_sq_le_of_positive
    hRsa.isSymmetric hRpos (C z)
  have hRCz : R (C z) = z := by
    have h := congrArg (fun T : H →L[ℂ] H => T z) hRC
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hform : RCLike.re ⟪R (C z), C z⟫_ℂ =
      RCLike.re ⟪C z, z⟫_ℂ := by
    calc
      RCLike.re ⟪R (C z), C z⟫_ℂ = RCLike.re ⟪z, C z⟫_ℂ := by
        rw [hRCz]
      _ = RCLike.re ⟪C z, z⟫_ℂ :=
        inner_re_symm (𝕜 := ℂ) z (C z)
  have hRbound' : ‖z‖ ^ 2 ≤
      ‖R‖ * RCLike.re ⟪C z, z⟫_ℂ := by
    calc
      ‖z‖ ^ 2 = ‖R (C z)‖ ^ 2 := by rw [hRCz]
      _ ≤ ‖R‖ * RCLike.re ⟪R (C z), C z⟫_ℂ := hRbound
      _ = ‖R‖ * RCLike.re ⟪C z, z⟫_ℂ := by rw [hform]
  have hz0 := hCpos z
  have hmul := mul_le_mul_of_nonneg_right hRnorm hz0
  have hzf : ‖z‖ ^ 2 ≤ c⁻¹ * RCLike.re ⟪C z, z⟫_ℂ :=
    hRbound'.trans hmul
  have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  calc
    c * ‖z‖ ^ 2 ≤ c * (c⁻¹ * RCLike.re ⟪C z, z⟫_ℂ) :=
      mul_le_mul_of_nonneg_left hzf hc.le
    _ = RCLike.re ⟪C z, z⟫_ℂ := by
      rw [← mul_assoc, hci, one_mul]

/-- **A lower bound on two orthogonal pieces is a lower bound overall.**

If `C` maps `U` into `U` and `Uᗮ` into `Uᗮ`, and is bounded below by `c` on
each, then it is bounded below by `c` on all of `H`: Pythagoras on both sides
of the decomposition.  Nothing here is about direct rotations. -/
private theorem norm_apply_ge_of_orthogonal_pieces
    {C : H →L[ℂ] H} {U : Submodule ℂ H} [U.HasOrthogonalProjection] {c : ℝ}
    (hc : 0 < c) (hCU : ∀ y ∈ U, C y ∈ U) (hCUc : ∀ y ∈ Uᗮ, C y ∈ Uᗮ)
    (hlowU : ∀ y ∈ U, c * ‖y‖ ≤ ‖C y‖) (hlowUc : ∀ y ∈ Uᗮ, c * ‖y‖ ≤ ‖C y‖)
    (z : H) : c * ‖z‖ ≤ ‖C z‖ := by
  let u : H := U.starProjection z
  let v : H := Uᗮ.starProjection z
  have hu : u ∈ U := U.starProjection_apply_mem z
  have hv : v ∈ Uᗮ := Uᗮ.starProjection_apply_mem z
  have hCu : C u ∈ U := hCU u hu
  have hCv : C v ∈ Uᗮ := hCUc v hv
  have hzuv : u + v = z := by
    change U.starProjection z + Uᗮ.starProjection z = z
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hCuv : C u + C v = C z := by rw [← map_add, hzuv]
  have huv : ⟪u, v⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu hv
  have hCuvorth : ⟪C u, C v⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hCu hCv
  have hnormz : ‖z‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [← hzuv, norm_add_sq (𝕜 := ℂ), huv, map_zero]
    ring
  have hnormC : ‖C z‖ ^ 2 = ‖C u‖ ^ 2 + ‖C v‖ ^ 2 := by
    rw [← hCuv, norm_add_sq (𝕜 := ℂ), hCuvorth, map_zero]
    ring
  have huLow := hlowU u hu
  have hvLow := hlowUc v hv
  have huSq0 : (c * ‖u‖) ^ 2 ≤ ‖C u‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg u))
      (norm_nonneg (C u))).2 huLow
  have hvSq0 : (c * ‖v‖) ^ 2 ≤ ‖C v‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg v))
      (norm_nonneg (C v))).2 hvLow
  have huSq : c ^ 2 * ‖u‖ ^ 2 ≤ ‖C u‖ ^ 2 := by
    calc
      c ^ 2 * ‖u‖ ^ 2 = (c * ‖u‖) ^ 2 := by ring
      _ ≤ ‖C u‖ ^ 2 := huSq0
  have hvSq : c ^ 2 * ‖v‖ ^ 2 ≤ ‖C v‖ ^ 2 := by
    calc
      c ^ 2 * ‖v‖ ^ 2 = (c * ‖v‖) ^ 2 := by ring
      _ ≤ ‖C v‖ ^ 2 := hvSq0
  have hsq : (c * ‖z‖) ^ 2 ≤ ‖C z‖ ^ 2 := by
    rw [show (c * ‖z‖) ^ 2 = c ^ 2 * ‖z‖ ^ 2 by ring,
      hnormz, hnormC]
    nlinarith only [huSq, hvSq]
  exact (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg z))
    (norm_nonneg (C z))).mp hsq

/-- Operator-norm minimality of the acute direct rotation among unitaries
transporting the source projection to the target projection.

The proof uses the operator-valued Halmos decomposition.  After conjugating a
competitor by the canonical rotation, its block diagonal part is tested
against the positive Halmos cosine.  A hypothetical smaller displacement
makes the inverse cosine uniformly bounded, hence makes the cosine quadratic
form uniformly coercive.  The Hermitian-part identity
`D + D⋆ = 2 C` then gives the desired displacement bound for `D`. -/
theorem spectraDirectRotation_minimal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : H →L[ℂ] H) (hWunit : W ∈ unitary (H →L[ℂ] H))
    (hintertwine : W * projection U = projection V * W) :
    ‖spectraDirectRotation U V hacute - 1‖ ≤ ‖W - 1‖ := by
  let D : H →L[ℂ] H := spectraDirectRotation U V hacute
  let C : H →L[ℂ] H :=
    spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  let P : H →L[ℂ] H := projection U
  let Pc : H →L[ℂ] H := complementaryProjection U
  let A : H →L[ℂ] H := star D * W
  let r : ℝ := ‖W - 1‖
  by_cases hrlarge : Real.sqrt 2 ≤ r
  · exact (norm_spectraDirectRotation_sub_one_le_sqrt_two U V hacute).trans hrlarge
  have hrsmall : r < Real.sqrt 2 := lt_of_not_ge hrlarge
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr2 : r ^ 2 < 2 := by
    have hsq : r ^ 2 < (Real.sqrt 2) ^ 2 :=
      (sq_lt_sq₀ hr0 (Real.sqrt_nonneg 2)).2 hrsmall
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
    exact hsq
  let c : ℝ := 1 - r ^ 2 / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hDunit : D ∈ unitary (H →L[ℂ] H) :=
    spectraDirectRotation_mem_unitary U V hacute
  have hstarDunit : star D ∈ unitary (H →L[ℂ] H) := by
    constructor
    · simpa [D] using spectraDirectRotation_mul_star_self U V hacute
    · simpa [D] using star_spectraDirectRotation_mul_self U V hacute
  have hAunit : A ∈ unitary (H →L[ℂ] H) :=
    (unitary (H →L[ℂ] H)).mul_mem hstarDunit hWunit
  have hAinj : Function.Injective A := by
    intro x y hxy
    have hmap := congrArg (fun z => star A z) hxy
    have hleft := Unitary.star_mul_self_of_mem hAunit
    have hx := congrArg (fun T : H →L[ℂ] H => T x) hleft
    have hy := congrArg (fun T : H →L[ℂ] H => T y) hleft
    calc
      x = star A (A x) := by
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using hx.symm
      _ = star A (A y) := hmap
      _ = y := by
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using hy
  have hAsurj : Function.Surjective A := by
    intro y
    refine ⟨star A y, ?_⟩
    have hright := Unitary.mul_star_self_of_mem hAunit
    have h := congrArg (fun T : H →L[ℂ] H => T y) hright
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hAcomm : Commute A P := by
    rw [commute_iff_eq]
    show A * P = P * A
    calc
      A * P = star D * (W * P) := by simp only [A]; rw [mul_assoc]
      _ = star D * (projection V * W) := by
        change star D * (W * projection U) = _
        rw [hintertwine]
      _ = (P * star D) * W := by
        change star D * (projection V * W) =
          (projection U * star D) * W
        rw [← mul_assoc, star_spectraDirectRotation_intertwines U V hacute]
      _ = P * A := by simp only [A]; rw [mul_assoc]
  have hAcommc : Commute A Pc := by
    rw [commute_iff_eq]
    change A * Uᗮ.starProjection = Uᗮ.starProjection * A
    rw [Submodule.starProjection_orthogonal']
    change A * (1 - P) = (1 - P) * A
    rw [mul_sub, mul_one, sub_mul, one_mul, hAcomm.eq]
  have hWeq : W = D * A := by
    calc
      W = 1 * W := (one_mul W).symm
      _ = (D * star D) * W := by
        rw [show D * star D = 1 by
          simpa [D] using spectraDirectRotation_mul_star_self U V hacute]
      _ = D * A := by simp only [A]; rw [mul_assoc]
  have hWform : ∀ x : H,
      c * ‖x‖ ^ 2 ≤ RCLike.re ⟪W x, x⟫_ℂ := by
    intro x
    have hop : ‖(W - 1) x‖ ≤ r * ‖x‖ := by
      simpa only [r] using (W - 1).le_opNorm x
    have hop2 : ‖(W - 1) x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hr0 (norm_nonneg x))).2 hop
    have hdisp := norm_sub_one_apply_sq_of_mem_unitary W hWunit x
    rw [RCLike.re_eq_complex_re] at hdisp ⊢
    dsimp [c]
    nlinarith only [hop2, hdisp]
  have hinnerU : ∀ {y x : H}, y ∈ U → x ∈ U →
      RCLike.re ⟪D y, x⟫_ℂ = RCLike.re ⟪C y, x⟫_ℂ := by
    intro y x hy hx
    have hdiag := projection_mul_spectraDirectRotation_mul_projection
      U V hacute
    have happ0 : P (D (P y)) = C (P y) := by
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : H →L[ℂ] H => T y) hdiag
    have hpy : P y = y := by
      dsimp [P]
      exact U.starProjection_eq_self_iff.mpr hy
    have happ : P (D y) = C y := by
      rw [hpy] at happ0
      exact happ0
    have hpx : U.starProjection x = x :=
      U.starProjection_eq_self_iff.mpr hx
    have hsym : ⟪P (D y), x⟫_ℂ = ⟪D y, x⟫_ℂ := by
      change ⟪U.starProjection (D y), x⟫_ℂ = ⟪D y, x⟫_ℂ
      calc
        ⟪U.starProjection (D y), x⟫_ℂ =
            ⟪D y, U.starProjection x⟫_ℂ :=
          U.starProjection_isSymmetric (D y) x
        _ = ⟪D y, x⟫_ℂ := by rw [hpx]
    calc
      RCLike.re ⟪D y, x⟫_ℂ = RCLike.re ⟪P (D y), x⟫_ℂ :=
        congrArg RCLike.re hsym.symm
      _ = RCLike.re ⟪C y, x⟫_ℂ := by rw [happ]
  have hinnerUc : ∀ {y x : H}, y ∈ Uᗮ → x ∈ Uᗮ →
      RCLike.re ⟪D y, x⟫_ℂ = RCLike.re ⟪C y, x⟫_ℂ := by
    intro y x hy hx
    have hdiag :=
      complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection
        U V hacute
    have happ0 : Pc (D (Pc y)) = C (Pc y) := by
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : H →L[ℂ] H => T y) hdiag
    have hpy : Pc y = y := by
      dsimp [Pc]
      exact Uᗮ.starProjection_eq_self_iff.mpr hy
    have happ : Pc (D y) = C y := by
      rw [hpy] at happ0
      exact happ0
    have hpx : Uᗮ.starProjection x = x :=
      Uᗮ.starProjection_eq_self_iff.mpr hx
    have hsym : ⟪Pc (D y), x⟫_ℂ = ⟪D y, x⟫_ℂ := by
      change ⟪Uᗮ.starProjection (D y), x⟫_ℂ = ⟪D y, x⟫_ℂ
      calc
        ⟪Uᗮ.starProjection (D y), x⟫_ℂ =
            ⟪D y, Uᗮ.starProjection x⟫_ℂ :=
          Uᗮ.starProjection_isSymmetric (D y) x
        _ = ⟪D y, x⟫_ℂ := by rw [hpx]
    calc
      RCLike.re ⟪D y, x⟫_ℂ = RCLike.re ⟪Pc (D y), x⟫_ℂ :=
        congrArg RCLike.re hsym.symm
      _ = RCLike.re ⟪C y, x⟫_ℂ := by rw [happ]
  have hlowU : ∀ y ∈ U, c * ‖y‖ ≤ ‖C y‖ := by
    intro y hy
    obtain ⟨x, hxy⟩ := hAsurj y
    have hcommapp : A (P x) = P (A x) := by
      have h := congrArg (fun T : H →L[ℂ] H => T x) hAcomm.eq
      simpa only [mul_apply_eq_comp] using h
    have hAP : A (P x) = A x := by
      calc
        A (P x) = P (A x) := hcommapp
        _ = P y := by rw [hxy]
        _ = y := by
          dsimp [P]
          exact U.starProjection_eq_self_iff.mpr hy
        _ = A x := hxy.symm
    have hPx : P x = x := hAinj hAP
    have hxU : x ∈ U := by
      apply U.starProjection_eq_self_iff.mp
      simpa only [P] using hPx
    have hform := hWform x
    have hWapp0 := congrArg (fun T : H →L[ℂ] H => T x) hWeq
    have hWapp : W x = D y := by
      simpa only [mul_apply_eq_comp, hxy] using hWapp0
    rw [hWapp, hinnerU hy hxU] at hform
    have hnormA : ‖A x‖ = ‖x‖ :=
      Unitary.norm_map (⟨A, hAunit⟩ : unitary (H →L[ℂ] H)) x
    rw [hxy] at hnormA
    exact mul_norm_le_norm_apply_of_re_inner_ge hform hnormA
  have hlowUc : ∀ y ∈ Uᗮ, c * ‖y‖ ≤ ‖C y‖ := by
    intro y hy
    obtain ⟨x, hxy⟩ := hAsurj y
    have hcommapp : A (Pc x) = Pc (A x) := by
      have h := congrArg (fun T : H →L[ℂ] H => T x) hAcommc.eq
      simpa only [mul_apply_eq_comp] using h
    have hAP : A (Pc x) = A x := by
      calc
        A (Pc x) = Pc (A x) := hcommapp
        _ = Pc y := by rw [hxy]
        _ = y := by
          dsimp [Pc]
          exact Uᗮ.starProjection_eq_self_iff.mpr hy
        _ = A x := hxy.symm
    have hPx : Pc x = x := hAinj hAP
    have hxU : x ∈ Uᗮ := by
      apply Uᗮ.starProjection_eq_self_iff.mp
      simpa only [Pc] using hPx
    have hform := hWform x
    have hWapp0 := congrArg (fun T : H →L[ℂ] H => T x) hWeq
    have hWapp : W x = D y := by
      simpa only [mul_apply_eq_comp, hxy] using hWapp0
    rw [hWapp, hinnerUc hy hxU] at hform
    have hnormA : ‖A x‖ = ‖x‖ :=
      Unitary.norm_map (⟨A, hAunit⟩ : unitary (H →L[ℂ] H)) x
    rw [hxy] at hnormA
    exact mul_norm_le_norm_apply_of_re_inner_ge hform hnormA
  have hCP : Commute C P := spectraCanonicalAbsoluteValue_commute_projection U V
  have hCPc : Commute C Pc := by
    rw [commute_iff_eq]
    change C * Uᗮ.starProjection = Uᗮ.starProjection * C
    rw [Submodule.starProjection_orthogonal']
    change C * (1 - P) = (1 - P) * C
    rw [mul_sub, mul_one, sub_mul, one_mul, hCP.eq]
  have hlow : ∀ z : H, c * ‖z‖ ≤ ‖C z‖ :=
    norm_apply_ge_of_orthogonal_pieces hc
      (fun y hy => by
        apply U.starProjection_eq_self_iff.mp
        have h := congrArg (fun T : H →L[ℂ] H => T y) hCP.eq
        rw [mul_apply_eq_comp, mul_apply_eq_comp,
          U.starProjection_eq_self_iff.mpr hy] at h
        exact h.symm)
      (fun y hy => by
        apply Uᗮ.starProjection_eq_self_iff.mp
        have h := congrArg (fun T : H →L[ℂ] H => T y) hCPc.eq
        rw [mul_apply_eq_comp, mul_apply_eq_comp,
          Uᗮ.starProjection_eq_self_iff.mpr hy] at h
        exact h.symm)
      hlowU hlowUc
  let Cunit := spectraCanonicalAbsoluteValueUnit U V hacute
  let R : H →L[ℂ] H := (↑(Cunit⁻¹) : H →L[ℂ] H)
  have hCcoe : (Cunit : H →L[ℂ] H) = C := by
    simpa only [Cunit, C] using
      coe_spectraCanonicalAbsoluteValueUnit U V hacute
  have hCR : C * R = 1 := by
    rw [← hCcoe]
    dsimp [R]
    exact Cunit.mul_inv
  have hRC : R * C = 1 := by
    rw [← hCcoe]
    dsimp [R]
    exact Cunit.inv_mul
  have hRsa : IsSelfAdjoint R := by
    have hstarRC : star R * C = 1 := by
      have h := congrArg star hCR
      have hCsa : star C = C :=
        (spectraOperatorAbsoluteValue_isSelfAdjoint
          (spectraCanonicalIntertwiner U V)).star_eq
      simpa only [star_mul, star_one, hCsa] using h
    show star R = R
    calc
      star R = star R * 1 := (mul_one _).symm
      _ = star R * (C * R) := by rw [hCR]
      _ = (star R * C) * R := by rw [← mul_assoc]
      _ = R := by rw [hstarRC, one_mul]
  have hRpos : ∀ z : H, 0 ≤ RCLike.re ⟪R z, z⟫_ℂ := by
    intro z
    have hCpos :=
      (ContinuousLinearMap.nonneg_iff_isPositive C).mp
        (spectraOperatorAbsoluteValue_nonneg
          (spectraCanonicalIntertwiner U V))
    have hz : C (R z) = z := by
      have h := congrArg (fun T : H →L[ℂ] H => T z) hCR
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
    calc
      0 ≤ RCLike.re ⟪C (R z), R z⟫_ℂ :=
        hCpos.re_inner_nonneg_left (R z)
      _ = RCLike.re ⟪R z, C (R z)⟫_ℂ :=
        inner_re_symm (𝕜 := ℂ) (C (R z)) (R z)
      _ = RCLike.re ⟪R z, z⟫_ℂ := by rw [hz]
  have hRnorm : ‖R‖ ≤ c⁻¹ := by
    refine R.opNorm_le_bound (inv_nonneg.mpr hc.le) ?_
    intro z
    have h := hlow (R z)
    have hz : C (R z) = z := by
      have h' := congrArg (fun T : H →L[ℂ] H => T z) hCR
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using h'
    have h' : c * ‖R z‖ ≤ ‖z‖ := by simpa only [hz] using h
    exact (le_inv_mul_iff₀ hc).2 h'
  have hCcoer : ∀ z : H, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪C z, z⟫_ℂ := fun z =>
    re_inner_ge_of_inverse_norm_le hc hRC hRsa hRpos hRnorm
      (fun w => ((ContinuousLinearMap.nonneg_iff_isPositive C).mp
        (spectraOperatorAbsoluteValue_nonneg
          (spectraCanonicalIntertwiner U V))).re_inner_nonneg_left w) z
  refine (D - 1).opNorm_le_bound (norm_nonneg (W - 1)) ?_
  intro x
  have hDdisp := norm_sub_one_apply_sq_of_mem_unitary D hDunit x
  have hDform := re_inner_spectraDirectRotation_eq_absoluteValue U V hacute x
  have hcoer := hCcoer x
  rw [RCLike.re_eq_complex_re] at hDdisp hDform hcoer
  have hsq : ‖(D - 1) x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    calc
      ‖(D - 1) x‖ ^ 2 =
          2 * ‖x‖ ^ 2 - 2 * (⟪D x, x⟫_ℂ).re := hDdisp
      _ = 2 * ‖x‖ ^ 2 - 2 * (⟪C x, x⟫_ℂ).re := by rw [hDform]
      _ ≤ r ^ 2 * ‖x‖ ^ 2 := by
        dsimp [c] at hcoer
        nlinarith only [hcoer]
      _ = (r * ‖x‖) ^ 2 := by ring
  have hle : ‖(D - 1) x‖ ≤ r * ‖x‖ :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hr0 (norm_nonneg x))).mp hsq
  simpa only [r] using hle

end Experimental
end DavisKahan
end TauCeti