/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section8RieszCircle
import DavisKahan.Experimental.Frontier.CircleContour
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.All
import ForMathlib.Analysis.InnerProductSpace.SpectralOrder.Complex
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSharpDiagonalResolvents
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSharpSchurComplement
import DavisKahan.Experimental.InfiniteDimensional.Riccati.ContinuationWitnessOrientedBlocks

/-!
# Section 8 frontier: branch selection and spectral repulsion

This module states the missing bridges from circle spectral projections to the
existing continuation witnesses, then states the source-level conclusions of
Theorems 8.1 and 8.2.  The declarations are intentionally separate so progress
can be measured at the analytic, geometric, and source-wrapper layers.
-/

open scoped InnerProductSpace
open Set Filter

namespace TauCeti

open ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open RieszCircle

universe u v

section ContinuationBridge

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Every point of the affine self-adjoint path is self-adjoint: the real
parameter is conjugation-fixed. -/
theorem operatorPath_isSelfAdjointOperator
    {A E : H →L[ℂ] H} (hA : IsSelfAdjointOperator A)
    (hE : IsSelfAdjointOperator E) (t : ℝ) :
    IsSelfAdjointOperator (operatorPath A E t) :=
  hA.add (hE.smul (Complex.conj_ofReal t))

/-- Circle data sufficient to construct the continuation witness used by the
existing Section 8 development.  The pencil inverse is taken through the total
`Ring.inverse`, matching the RieszCircle surface. -/
structure CircleContinuationData
    (A E : H →L[ℂ] H) (s : Set ℝ) where
  hA : IsSelfAdjointOperator A
  hE : IsSelfAdjointOperator E
  hs : MeasurableSet s
  center : ℝ
  radius : ℝ
  margin : ℝ
  margin_pos : 0 < margin
  separates : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
    CircleSeparatesRealSpectrum (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator hA hE t) s center radius
  inverse_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - operatorPath A E t)‖ ≤ margin⁻¹

/-- Every circle point lies on the sphere of the circle contour. -/
theorem circleContour_path_norm_sub_center
    (D : CircleContinuationData A E s) (x : unitInterval) :
    ‖(CircleContour.circleContour (D.center : ℂ) D.radius).path x -
        (D.center : ℂ)‖ = D.radius := by
  show ‖circleMap (D.center : ℂ) D.radius (2 * Real.pi * (x : ℝ)) -
      (D.center : ℂ)‖ = D.radius
  simpa [mem_sphere_iff_norm] using
    circleMap_mem_sphere (D.center : ℂ)
      (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
      (2 * Real.pi * (x : ℝ))

/-- A common separating circle constructs the canonical spectral continuation
witness consumed by the Section 8 branch-selection stack.  The pathwise
separating contours are the circle contours of `CircleContour`, and the
uniform margin comes from the common resolvent bound through the
Neumann-series estimate. -/
noncomputable def spectralContinuationWitness_of_circle
    (D : CircleContinuationData A E s) :
    SpectralContinuationWitness A E s where
  contour := CircleContour.circleContour (D.center : ℂ) D.radius
  separating := fun t ht =>
    CircleContour.circleSeparatingContour (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator D.hA D.hE t) D.hs
      (D.separates t ht)
  geometric_eq := fun _t _ht => rfl
  margin := D.margin
  margin_pos := D.margin_pos
  spectrum_separated := by
    intro t ht x lam hlam
    have hzc := circleContour_path_norm_sub_center D x
    have hznot : (CircleContour.circleContour (D.center : ℂ) D.radius).path x ∉
        spectrum ℂ (operatorPath A E t) :=
      (D.separates t ht).contour_resolvent _ hzc
    have hb := D.inverse_bound t ht _ hzc
    exact CircleContour.margin_le_norm_sub_of_inverse_bound
      D.margin_pos hznot hb hlam

/-- The source and target selected projections of the witness are the genuine
bounded self-adjoint spectral projections. -/
theorem spectralContinuationWitness_of_circle_endpoints
    (D : CircleContinuationData A E s) :
    (spectralContinuationWitness_of_circle
        D).sourceSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection A D.hA s D.hs ∧
      (spectralContinuationWitness_of_circle
          D).targetSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection (A + E)
          (D.hA.add D.hE) s D.hs := by
  constructor
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      A D.hA s D.hs).symm
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      (A + E) (D.hA.add D.hE) s D.hs).symm

/-- Quantitative projection variation obtained from the common-circle
resolvent bound. -/
theorem selectedBranchProjectionLipschitzConstant_of_circle
    (D : CircleContinuationData A E s) :
    selectedBranchProjectionLipschitzConstant
      (spectralContinuationWitness_of_circle D).contour E D.margin ≤
        D.radius * ‖E‖ / D.margin ^ 2 := by
  have hr : (0 : ℝ) ≤ D.radius :=
    (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
  apply le_of_eq
  unfold selectedBranchProjectionLipschitzConstant
  have hlen : (spectralContinuationWitness_of_circle D).contour.contourLength =
      2 * Real.pi * D.radius :=
    CircleContour.circleContour_contourLength _ hr
  have hnorm : ‖rieszNormalization‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_rieszNormalization, norm_inv]
    have h2pi : ‖((2 : ℂ) * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h2pi]
  rw [hlen, hnorm]
  have hm : (D.margin : ℝ) ≠ 0 := D.margin_pos.ne'
  field_simp


omit [CompleteSpace H] in
/-- Local two-sided resolvent membership excludes a point from the Banach
algebra spectrum. -/
theorem not_mem_spectrum_of_inResolventSet
    (T : H →L[ℂ] H) {z : ℂ} (hz : InResolventSet T z) :
    z ∉ spectrum ℂ T := by
  obtain ⟨R, hRL, hLR⟩ := hz
  let P : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - T
  have hP : P = -(T - z • (1 : H →L[ℂ] H)) := by
    dsimp only [P]
    abel
  have hPR : P * (-R) = 1 := by
    rw [hP, neg_mul_neg]
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
      using hLR
  have hRP : (-R) * P = 1 := by
    rw [hP, neg_mul_neg]
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
      using hRL
  have hunit : IsUnit P := isUnit_iff_exists.mpr ⟨-R, hPR, hRP⟩
  apply spectrum.notMem_iff.mpr
  simpa only [P, Algebra.algebraMap_eq_smul_one] using hunit

omit [CompleteSpace H] in
/-- The total inverse of `zI - T` has the same norm as the local resolvent
operator defined using the opposite pencil `T - zI`. -/
theorem norm_ringInverse_pencil_eq_norm_resolventOperator
    (T : H →L[ℂ] H) {z : ℂ} (hz : InResolventSet T z) :
    ‖Ring.inverse (z • (1 : H →L[ℂ] H) - T)‖ =
      ‖resolventOperator T z‖ := by
  let P : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - T
  let R : H →L[ℂ] H := resolventOperator T z
  have hP : P = -(T - z • (1 : H →L[ℂ] H)) := by
    dsimp only [P]
    abel
  have hRL := resolventOperator_mul_cancel T hz
  have hLR := mul_resolventOperator_cancel T hz
  have hPR : P * (-R) = 1 := by
    rw [hP, neg_mul_neg]
    simpa only [R] using hLR
  have hRP : (-R) * P = 1 := by
    rw [hP, neg_mul_neg]
    simpa only [R] using hRL
  have hunit : IsUnit P := isUnit_iff_exists.mpr ⟨-R, hPR, hRP⟩
  have hinv : Ring.inverse P = -R := by
    calc
      Ring.inverse P = Ring.inverse P * 1 := (mul_one _).symm
      _ = Ring.inverse P * (P * (-R)) := by rw [hPR]
      _ = (Ring.inverse P * P) * (-R) := by rw [mul_assoc]
      _ = -R := by rw [Ring.inverse_mul_cancel P hunit, one_mul]
  rw [show z • (1 : H →L[ℂ] H) - T = P from rfl, hinv, norm_neg]

/-- Every point on the canonical finite-gap circle is at distance at least
`d / 2` from the selected interval. -/
theorem canonicalGapCircle_distance_interval
    {left right d : ℝ} (hlr : left ≤ right) {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ∈ Set.Icc left right) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  have hcenter :
      ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        (right - left) / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hlam.1, hlam.2]
  have hdecomp :
      z - (((left + right) / 2 : ℝ) : ℂ) =
        (z - (lam : ℂ)) +
          ((lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)) := by
    ring
  have htri :
      ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ +
          ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  rw [hz] at htri
  linarith

/-- Every point on the canonical finite-gap circle is at distance at least
`d / 2` from the complementary exterior. -/
theorem canonicalGapCircle_distance_exterior
    {left right d : ℝ} (hlr : left ≤ right) (hd0 : 0 ≤ d) {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ≤ left - d ∨ right + d ≤ lam) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  have hfar :
      (right - left + d) / 2 + d / 2 ≤
        ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rcases hlam with hlam | hlam
    · have hsign : lam - (left + right) / 2 ≤ 0 := by
        linarith
      rw [abs_of_nonpos hsign]
      linarith
    · have hsign : 0 ≤ lam - (left + right) / 2 := by
        linarith
      rw [abs_of_nonneg hsign]
      linarith
  have hdecomp :
      (lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ) =
        ((lam : ℂ) - z) +
          (z - (((left + right) / 2 : ℝ) : ℂ)) := by
    ring
  have htri :
      ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        ‖(lam : ℂ) - z‖ +
          ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  rw [hz] at htri
  have hdist : d / 2 ≤ ‖(lam : ℂ) - z‖ := by
    linarith
  simpa only [norm_sub_rev] using hdist

/-- The real points strictly inside the canonical finite-gap circle are
exactly the interval enlarged by `d / 2` on both sides. -/
theorem canonicalGapCircle_inside_iff
    {left right d x : ℝ} :
    ‖(x : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ <
        (right - left + d) / 2 ↔
      x ∈ Set.Ioo (left - d / 2) (right + d / 2) := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

/-- The Schur criterion excludes any real point that remains closer than the
chosen margin to the canonical finite-gap circle. -/
theorem canonicalGapCircle_margin_le_realSpectrum
    (hA : IsSelfAdjointOperator A) (hE : IsSelfAdjointOperator E)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U E)
    {d left right : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hdiag : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ hpath : IsSelfAdjointOperator (operatorPath A E t),
      ∀ z : ℂ, ∀ delta0 delta1 : ℝ,
        0 < delta0 → 0 < delta1 →
        (∀ lam ∈ Set.Icc left right,
          delta0 ≤ ‖z - (lam : ℂ)‖) →
        (∀ lam ∈ {x : ℝ | x ≤ left - d ∨ right + d ≤ x},
          delta1 ≤ ‖z - (lam : ℂ)‖) →
        let Ht := subspaceBlockOperatorData (operatorPath A E t) U hpath
        InResolventSet Ht.A0 z ∧
        ‖resolventOperator Ht.A0 z‖ ≤ delta0⁻¹ ∧
        InResolventSet Ht.A1 z ∧
        ‖resolventOperator Ht.A1 z‖ ≤ delta1⁻¹ ∧
        ‖Ht.B01‖ ≤ t * ‖E‖ ∧
        ‖Ht.B10‖ ≤ t * ‖E‖)
    (hsmall : ‖E‖ < d / 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ∈ realSpectrum (operatorPath A E t)) :
    (d / 2 - ‖E‖) / 2 ≤ ‖z - (lam : ℂ)‖ := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let margin : ℝ := (d / 2 - ‖E‖) / 2
  let delta : ℝ := d / 2 - margin
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  have hdelta : 0 < delta := by
    dsimp only [delta, margin]
    linarith [norm_nonneg E]
  have htd : t * ‖E‖ < delta := by
    have htE : t * ‖E‖ ≤ ‖E‖ := by
      nlinarith [ht.1, ht.2, norm_nonneg E]
    dsimp only [delta, margin]
    linarith
  by_contra hnot
  rw [not_le] at hnot
  have hsep0 : ∀ mu ∈ Set.Icc left right,
      delta ≤ ‖(lam : ℂ) - (mu : ℂ)‖ := by
    intro mu hmu
    have hcircle := canonicalGapCircle_distance_interval hlr hz hmu
    have htri : ‖z - (mu : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ + ‖(lam : ℂ) - (mu : ℂ)‖ := by
      calc
        ‖z - (mu : ℂ)‖ =
            ‖(z - (lam : ℂ)) + ((lam : ℂ) - (mu : ℂ))‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    dsimp only [delta, margin]
    linarith
  have hsep1 : ∀ mu ∈ {x : ℝ | x ≤ left - d ∨ right + d ≤ x},
      delta ≤ ‖(lam : ℂ) - (mu : ℂ)‖ := by
    intro mu hmu
    have hcircle := canonicalGapCircle_distance_exterior hlr hd.le hz hmu
    have htri : ‖z - (mu : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ + ‖(lam : ℂ) - (mu : ℂ)‖ := by
      calc
        ‖z - (mu : ℂ)‖ =
            ‖(z - (lam : ℂ)) + ((lam : ℂ) - (mu : ℂ))‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    dsimp only [delta, margin]
    linarith
  let hpath := operatorPath_isSelfAdjointOperator hA hE t
  let Ht := subspaceBlockOperatorData (operatorPath A E t) U hpath
  obtain ⟨h0, hR0, h1, hR1, hB01, hB10⟩ :=
    hdiag t ht hpath (lam : ℂ) delta delta hdelta hdelta hsep0 hsep1
  have hq0 : 0 ≤ t * ‖E‖ := mul_nonneg ht.1 (norm_nonneg E)
  have hratio0 : 0 ≤ delta⁻¹ * (t * ‖E‖) :=
    mul_nonneg (inv_nonneg.mpr hdelta.le) hq0
  have hratio1 : delta⁻¹ * (t * ‖E‖) < 1 := by
    rw [inv_mul_eq_div]
    exact (div_lt_one hdelta).2 htd
  let R0 : U →L[ℂ] U := resolventOperator Ht.A0 (lam : ℂ)
  let R1 : Uᗮ →L[ℂ] Uᗮ := resolventOperator Ht.A1 (lam : ℂ)
  have hR0' : ‖R0‖ ≤ delta⁻¹ := by
    simpa only [R0] using hR0
  have hR1' : ‖R1‖ ≤ delta⁻¹ := by
    simpa only [R1] using hR1
  have hdeltaInv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hprod :
      ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ < 1 := by
    have hcomp1 :
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ ≤
          ‖((R1 ∘L Ht.B10) ∘L R0)‖ * ‖Ht.B01‖ :=
      ContinuousLinearMap.opNorm_comp_le
        ((R1 ∘L Ht.B10) ∘L R0) Ht.B01
    have hcomp2 :
        ‖((R1 ∘L Ht.B10) ∘L R0)‖ ≤
          ‖R1 ∘L Ht.B10‖ * ‖R0‖ :=
      ContinuousLinearMap.opNorm_comp_le (R1 ∘L Ht.B10) R0
    have hcomp3 :
        ‖R1 ∘L Ht.B10‖ ≤ ‖R1‖ * ‖Ht.B10‖ :=
      ContinuousLinearMap.opNorm_comp_le R1 Ht.B10
    have hpair :
        ‖R1‖ * ‖Ht.B10‖ ≤ delta⁻¹ * (t * ‖E‖) :=
      mul_le_mul hR1' hB10 (norm_nonneg Ht.B10) hdeltaInv
    have htriple :
        (‖R1‖ * ‖Ht.B10‖) * ‖R0‖ ≤
          (delta⁻¹ * (t * ‖E‖)) * delta⁻¹ :=
      mul_le_mul hpair hR0' (norm_nonneg R0) hratio0
    have hfour :
        ((‖R1‖ * ‖Ht.B10‖) * ‖R0‖) * ‖Ht.B01‖ ≤
          ((delta⁻¹ * (t * ‖E‖)) * delta⁻¹) * (t * ‖E‖) :=
      mul_le_mul htriple hB01 (norm_nonneg Ht.B01)
        (mul_nonneg hratio0 hdeltaInv)
    have hnorm :
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ ≤
          delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := by
      calc
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖
            ≤ ‖((R1 ∘L Ht.B10) ∘L R0)‖ * ‖Ht.B01‖ := hcomp1
        _ ≤ (‖R1 ∘L Ht.B10‖ * ‖R0‖) * ‖Ht.B01‖ :=
          mul_le_mul_of_nonneg_right hcomp2 (norm_nonneg Ht.B01)
        _ ≤ ((‖R1‖ * ‖Ht.B10‖) * ‖R0‖) * ‖Ht.B01‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcomp3 (norm_nonneg R0))
            (norm_nonneg Ht.B01)
        _ ≤ delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := hfour
    calc
      ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖
          ≤ delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := hnorm
      _ = (delta⁻¹ * (t * ‖E‖)) ^ 2 := by ring
      _ < 1 := by nlinarith
  have hblock : InResolventSet (blockOperator Ht) (lam : ℂ) := by
    simpa only [R0, R1, ContinuousLinearMap.comp_assoc] using
      blockOperator_inResolventSet_of_schur_norm_lt_one
        Ht (lam : ℂ) h0 h1 hprod
  have hnotBlock : (lam : ℂ) ∉ spectrum ℂ (blockOperator Ht) :=
    not_mem_spectrum_of_inResolventSet (blockOperator Ht) hblock
  have hspec := spectrum_subspaceBlockOperatorData
    (operatorPath A E t) U hpath
  have hnotAmbient : (lam : ℂ) ∉ spectrum ℂ (operatorPath A E t) := by
    rw [hspec]
    exact hnotBlock
  exact hnotAmbient hlam

/-- The printed perturbation half-gap condition produces a single common
circle, a uniform spectral margin, and hence the continuation datum used by
Section 8. -/
theorem exists_circleContinuationData_of_offDiagonal_halfGap
    (hA : IsSelfAdjointOperator A) (hE : IsSelfAdjointOperator E)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U E)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖E‖ < d / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      Nonempty (CircleContinuationData A E
        (Set.Ioo (left - d / 2) (right + d / 2))) := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  obtain ⟨left, right, hlr, hdiag⟩ :=
    hfinite.exists_operatorPath_diagonalResolventData A E U hU hoff
  let center : ℝ := (left + right) / 2
  let radius : ℝ := (right - left + d) / 2
  let margin : ℝ := (d / 2 - ‖E‖) / 2
  have hradius : 0 < radius := by
    dsimp only [radius]
    linarith
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  have huniform : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ∀ lam ∈ realSpectrum (operatorPath A E t),
        margin ≤ ‖z - (lam : ℂ)‖ := by
    intro t ht z hz lam hlam
    exact canonicalGapCircle_margin_le_realSpectrum hA hE hU hoff hd hlr
      hdiag hsmall ht (by simpa only [center, radius] using hz) hlam
  refine ⟨left, right, hlr, ⟨?_⟩⟩
  refine
    { hA := hA
      hE := hE
      hs := measurableSet_Ioo
      center := center
      radius := radius
      margin := margin
      margin_pos := hmargin
      separates := ?_
      inverse_bound := ?_ }
  · intro t ht
    have hpath := operatorPath_isSelfAdjointOperator hA hE t
    refine
      { radius_pos := hradius
        contour_resolvent := ?_
        inside_iff_mem := ?_ }
    · intro z hz
      have hsep : ∀ lam ∈ realSpectrum (operatorPath A E t),
          margin ≤ ‖z - (lam : ℂ)‖ :=
        huniform t ht z hz
      have hres := complex_inResolventSet_of_distance
        (operatorPath A E t) hpath z margin hmargin hsep
      exact not_mem_spectrum_of_inResolventSet (operatorPath A E t) hres
    · intro x _hx
      simpa only [center, radius] using
        (canonicalGapCircle_inside_iff (left := left) (right := right)
          (d := d) (x := x))
  · intro t ht z hz
    have hpath := operatorPath_isSelfAdjointOperator hA hE t
    have hsep : ∀ lam ∈ realSpectrum (operatorPath A E t),
        margin ≤ ‖z - (lam : ℂ)‖ :=
      huniform t ht z hz
    have hres := complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A E t) hpath z margin hmargin hsep
    rw [norm_ringInverse_pencil_eq_norm_resolventOperator
      (operatorPath A E t) hres.1]
    exact hres.2

/-- Source-facing continuation witness obtained directly from the finite-gap,
off-diagonal, and perturbation half-gap hypotheses. -/
theorem exists_spectralContinuationWitness_of_offDiagonal_halfGap
    (hA : IsSelfAdjointOperator A) (hE : IsSelfAdjointOperator E)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U E)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖E‖ < d / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      Nonempty (SpectralContinuationWitness A E
        (Set.Ioo (left - d / 2) (right + d / 2))) := by
  obtain ⟨left, right, hlr, ⟨D⟩⟩ :=
    exists_circleContinuationData_of_offDiagonal_halfGap
      hA hE hU hoff hd hfinite hsmall
  exact ⟨left, right, hlr, ⟨spectralContinuationWitness_of_circle D⟩⟩

end ContinuationBridge

section TargetSplittingCompression

/-! The scaffolded statements of this section claimed the compression
inequalities of Theorem 8.1(i) with placeholder identity blocks; as
transcribed they were false (the Pythagorean field demanded
`2 ‖x‖ ^ 2 = ‖x‖ ^ 2`, and the inequalities reduced to a sign condition on
the perturbation).  At the quadratic-form level the paper's cosine-block
inequality needs no direct rotation: the orthogonal splitting through the new
spectral branch supplies the certificate, because the branch reduces the
perturbed operator, so the cross terms of the splitting vanish. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- A `SpectrumIn` upper half-line for a symmetric operator gives the
quadratic-form upper bound on the branch, through the restriction-spectrum
spectral-order bridge. -/
theorem re_inner_le_of_spectrumIn_Iic
    {T : H →L[ℂ] H} (hT : T.IsSymmetric) {W : Submodule ℂ H}
    [W.HasOrthogonalProjection] {a : ℝ}
    (h : SpectrumIn T W (Set.Iic a)) {y : H} (hy : y ∈ W) :
    RCLike.re ⟪y, T y⟫_ℂ ≤ a * ‖y‖ ^ 2 := by
  have hσ : spectrum ℝ (T.restrict h.invariant) ⊆ Set.Iic a := by
    intro r hr
    exact h.subset
      ⟨h.invariant, by simpa using (spectrum.algebraMap_mem_iff (S := ℂ)).mpr hr⟩
  have hb :=
    SpectralOrder.Complex.upperFormBoundOn_of_restriction_spectrum_subset_Iic
      hT h.invariant hσ y hy
  calc RCLike.re ⟪y, T y⟫_ℂ = RCLike.re ⟪T y, y⟫_ℂ :=
      (congrArg RCLike.re (hT y y)).symm
    _ ≤ a * ‖y‖ ^ 2 := hb

/-- A `SpectrumIn` lower half-line for a symmetric operator gives the
quadratic-form lower bound on the branch. -/
theorem le_re_inner_of_spectrumIn_Ici
    {T : H →L[ℂ] H} (hT : T.IsSymmetric) {W : Submodule ℂ H}
    [W.HasOrthogonalProjection] {b : ℝ}
    (h : SpectrumIn T W (Set.Ici b)) {y : H} (hy : y ∈ W) :
    b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_ℂ := by
  have hσ : spectrum ℝ (T.restrict h.invariant) ⊆ Set.Ici b := by
    intro r hr
    exact h.subset
      ⟨h.invariant, by simpa using (spectrum.algebraMap_mem_iff (S := ℂ)).mpr hr⟩
  have hb :=
    SpectralOrder.Complex.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
      hT h.invariant hσ y hy
  calc b * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := hb
    _ = RCLike.re ⟪y, T y⟫_ℂ := congrArg RCLike.re (hT y y)

/-- The quadratic form of an operator splits exactly through a reducing
subspace: the cross terms vanish. -/
theorem re_inner_splitting_of_invariant
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (x : H) :
    RCLike.re ⟪x, T x⟫_ℂ =
      RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ +
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ := by
  set p := W.starProjection x with hp
  set q := Wᗮ.starProjection x with hq
  have hx : p + q = x := W.starProjection_add_starProjection_orthogonal x
  have hpq : ⟪p, T q⟫_ℂ = 0 := by
    have hTq : T q ∈ Wᗮ := hW' q (Wᗮ.starProjection_apply_mem x)
    exact (Submodule.mem_orthogonal W (T q)).mp hTq p (W.starProjection_apply_mem x)
  have hqp : ⟪q, T p⟫_ℂ = 0 := by
    have hTp : T p ∈ W := hW p (W.starProjection_apply_mem x)
    exact (Submodule.mem_orthogonal' W q).mp (Wᗮ.starProjection_apply_mem x)
      (T p) hTp
  have hinner : ⟪x, T x⟫_ℂ = ⟪p, T p⟫_ℂ + ⟪q, T q⟫_ℂ := by
    conv_lhs => rw [← hx]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hpq, hqp]
    ring
  rw [hinner, map_add]

/-- The orthogonal splitting through the new spectral branch supplies the
upper compression certificate of Theorem 8.1(i).  The kernel-side form is
shifted by the cut so that its global bound is exactly the branch form
bound. -/
theorem upperCompressionRepulsionData_of_targetSplitting
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (a : ℝ) :
    DavisKahan1970.Section8.UpperCompressionRepulsionData
      (fun x : H => RCLike.re ⟪x, T x⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ +
          (a * ‖x‖ ^ 2 - a * ‖W.starProjection x‖ ^ 2))
      (fun x : H =>
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ)
      W.starProjection Wᗮ.starProjection := by
  have hidem : ∀ x : H, W.starProjection (W.starProjection x) =
      W.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hidem' : ∀ x : H, Wᗮ.starProjection (Wᗮ.starProjection x) =
      Wᗮ.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)
  constructor
  · intro x
    rw [hidem x, hidem' x, re_inner_splitting_of_invariant hW hW' x]
    ring
  · intro x
    exact (W.norm_sq_eq_add_norm_sq_starProjection x).symm

/-- The orthogonal splitting through the new spectral branch supplies the
lower compression certificate of Theorem 8.1(i). -/
theorem lowerCompressionRepulsionData_of_targetSplitting
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (b : ℝ) :
    DavisKahan1970.Section8.LowerCompressionRepulsionData
      (fun x : H => RCLike.re ⟪x, T x⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ +
          (b * ‖x‖ ^ 2 - b * ‖Wᗮ.starProjection x‖ ^ 2))
      W.starProjection Wᗮ.starProjection := by
  have hidem : ∀ x : H, W.starProjection (W.starProjection x) =
      W.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hidem' : ∀ x : H, Wᗮ.starProjection (Wᗮ.starProjection x) =
      Wᗮ.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)
  constructor
  · intro x
    rw [hidem x, hidem' x, re_inner_splitting_of_invariant hW hW' x]
    ring
  · intro x
    exact (W.norm_sq_eq_add_norm_sq_starProjection x).symm

/-- Davis--Kahan 1970, Theorem 8.1(i), upper compression inequality, restated
faithfully: the displacement of the perturbed form on the old complement is
controlled by its displacement after the cosine block into the new
complement.  The former placeholder statement compared the unperturbed and
perturbed forms with cancelling cut terms and was false as transcribed. -/
theorem theorem8_1_upperCompressionRepulsion_of_targetSplitting
    (C : SpectralContinuationWitness A E s) {a : ℝ}
    (hsym : IsSelfAdjointOperator (A + E))
    (h0 : SpectrumIn (A + E) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1inv : InvariantFor (A + E) C.targetSelectedSpectralSubspaceᗮ) :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ - a * ‖(x : H)‖ ^ 2 ≤
        RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection
              (x : H))⟫_ℂ -
          a * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)‖ ^ 2 := by
  intro x
  have hdata := upperCompressionRepulsionData_of_targetSplitting
    (T := A + E) (W := C.targetSelectedSpectralSubspace) h0.invariant h1inv a
  have hL0 : ∀ y : H,
      RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection y,
          (A + E) (C.targetSelectedSpectralSubspace.starProjection y)⟫_ℂ +
        (a * ‖y‖ ^ 2 -
          a * ‖C.targetSelectedSpectralSubspace.starProjection y‖ ^ 2) ≤
      a * ‖y‖ ^ 2 := by
    intro y
    have hform := re_inner_le_of_spectrumIn_Iic hsym h0
      (C.targetSelectedSpectralSubspace.starProjection_apply_mem y)
    linarith
  have hres :=
    DavisKahan1970.Section8.upperCompressionRepulsion_of_data hdata hL0 (x : H)
  have hidem : C.targetSelectedSpectralSubspaceᗮ.starProjection
      (C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)) =
      C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H) :=
    Submodule.starProjection_eq_self_iff.mpr
      (C.targetSelectedSpectralSubspaceᗮ.starProjection_apply_mem (x : H))
  simp only [hidem] at hres
  exact hres

/-- Davis--Kahan 1970, Theorem 8.1(i), lower compression companion, restated
faithfully over the old selected subspace. -/
theorem theorem8_1_lowerCompressionRepulsion_of_targetSplitting
    (C : SpectralContinuationWitness A E s) {b : ℝ}
    (hsym : IsSelfAdjointOperator (A + E))
    (h0inv : InvariantFor (A + E) C.targetSelectedSpectralSubspace)
    (h1 : SpectrumIn (A + E) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    ∀ x : C.sourceSelectedSpectralSubspace,
      b * ‖(x : H)‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ ≤
        b * ‖C.targetSelectedSpectralSubspace.starProjection (x : H)‖ ^ 2 -
          RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspace.starProjection
              (x : H))⟫_ℂ := by
  intro x
  have hdata := lowerCompressionRepulsionData_of_targetSplitting
    (T := A + E) (W := C.targetSelectedSpectralSubspace) h0inv h1.invariant b
  have hL1 : ∀ y : H,
      b * ‖y‖ ^ 2 ≤
      RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection y,
          (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection y)⟫_ℂ +
        (b * ‖y‖ ^ 2 -
          b * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection y‖ ^ 2) := by
    intro y
    have hform := le_re_inner_of_spectrumIn_Ici hsym h1
      (C.targetSelectedSpectralSubspaceᗮ.starProjection_apply_mem y)
    linarith
  have hres :=
    DavisKahan1970.Section8.lowerCompressionRepulsion_of_data hdata hL1 (x : H)
  have hidem : C.targetSelectedSpectralSubspace.starProjection
      (C.targetSelectedSpectralSubspace.starProjection (x : H)) =
      C.targetSelectedSpectralSubspace.starProjection (x : H) :=
    Submodule.starProjection_eq_self_iff.mpr
      (C.targetSelectedSpectralSubspace.starProjection_apply_mem (x : H))
  simp only [hidem] at hres
  exact hres

end TargetSplittingCompression

section SourceTheorems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Full source-level conclusion currently expected from Davis--Kahan Theorem
8.1.  The compression inequalities are kept explicit rather than hidden behind
an unconstrained certificate.

Restated against the scaffold: the former compression fields compared the
unperturbed and perturbed forms with cancelling cut terms, which is not the
source inequality and is false in general.  The faithful quadratic-form
content of Theorem 8.1(i) compares the perturbed form on the old branch with
its cosine-block compression into the corresponding new branch. -/
structure Theorem81SourceConclusion
    (C : SpectralContinuationWitness A E s) (a b delta : ℝ) : Prop where
  core : DavisKahan1970.Section8.Theorem81CoreConclusion C a b delta
  upper_compression :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ - a * ‖(x : H)‖ ^ 2 ≤
        RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection
              (x : H))⟫_ℂ -
          a * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)‖ ^ 2
  lower_compression :
    ∀ x : C.sourceSelectedSpectralSubspace,
      b * ‖(x : H)‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ ≤
        b * ‖C.targetSelectedSpectralSubspace.starProjection (x : H)‖ ^ 2 -
          RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspace.starProjection
              (x : H))⟫_ℂ

/-- Davis--Kahan 1970, Theorem 8.1 assembled from a common-circle
continuation, oriented spectral placement, and the target-splitting
compression algebra. -/
theorem theorem8_1_selectedBranch_and_spectralRepulsion
    (D : CircleContinuationData A E s) {a b delta : ℝ}
    (hsmall : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2)
    (hgap : a + delta ≤ b)
    (h0 : SpectrumIn (A + E)
      (spectralContinuationWitness_of_circle D).targetSelectedSpectralSubspace
      (Set.Iic a))
    (h1 : SpectrumIn (A + E)
      (spectralContinuationWitness_of_circle D).targetSelectedSpectralSubspaceᗮ
      (Set.Ici b)) :
    Theorem81SourceConclusion
      (spectralContinuationWitness_of_circle D) a b delta := by
  have hsym : IsSelfAdjointOperator (A + E) := D.hA.add D.hE
  have hsmallC : selectedBranchProjectionLipschitzConstant
      (spectralContinuationWitness_of_circle D).contour E D.margin <
        Real.sqrt 2 / 2 :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hsmall
  exact
    { core := DavisKahan1970.Section8.theorem81CoreConclusion _
        hsmallC hgap h0 h1
      upper_compression :=
        theorem8_1_upperCompressionRepulsion_of_targetSplitting _
          hsym h0 h1.invariant
      lower_compression :=
        theorem8_1_lowerCompressionRepulsion_of_targetSplitting _
          hsym h0.invariant h1 }

/-- Construct the perturbation half-gap bridge required by Theorem 8.2
from a circle datum and an endpoint-size estimate.

The common circle and its uniform spectral margin are now constructed directly
from the finite-gap, off-diagonal, and perturbation half-gap hypotheses by
`exists_circleContinuationData_of_offDiagonal_halfGap`.  The additional bound
below is a sufficient one-step estimate for locating the endpoint below the
quarter-turn threshold; replacing it by the source continuation/no-crossing
argument is a separate branch-selection step. -/
theorem perturbationHalfGapBridge_of_sourceHypotheses
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.PerturbationHalfGapBridge
      (spectralContinuationWitness_of_circle D) delta where
  delta_pos := hdelta
  perturbation_small := hsmall
  contour_selects_quarter_branch :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hquant

/-- Construct the residual half-gap bridge.  The same amendment applies; in
the source the quantitative circle input for the residual alternative is
produced by the Krein replacement argument, which remains the open analytic
step. -/
theorem residualHalfGapBridge_of_sourceHypotheses
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.ResidualHalfGapBridge
      (spectralContinuationWitness_of_circle D) R delta where
  delta_pos := hdelta
  residual_small := hsmall
  contour_selects_quarter_branch :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hquant

/-- Davis--Kahan 1970, Theorem 8.2, perturbation-smallness alternative, from
the quantitative circle datum. -/
theorem theorem8_2_perturbationHalfGap_selectedBranch
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitness_of_circle D) :=
  DavisKahan1970.Section8.theorem82_branch_of_perturbationHalfGapBridge _
    (perturbationHalfGapBridge_of_sourceHypotheses D hdelta hsmall hquant)

/-- Davis--Kahan 1970, Theorem 8.2, residual-smallness alternative, from the
quantitative circle datum. -/
theorem theorem8_2_residualHalfGap_selectedBranch
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitness_of_circle D) :=
  DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge _ R
    (residualHalfGapBridge_of_sourceHypotheses D R hdelta hsmall hquant)

end SourceTheorems

end Section8
end Frontier
end Experimental
end DavisKahan
end TauCeti