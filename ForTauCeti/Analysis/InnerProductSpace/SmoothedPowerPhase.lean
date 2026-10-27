/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerSpectralTrace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Phase curvature of the common smoothed-power penalty

One differentiation gives the phase gradient for every exponent; a second
gives its quadratic sign polynomial. This is scalar calculus, not a claim
that scalar minima already solve the unrestricted transport problem.

The computations derive the family proposed in
`dev/spectral-transport-publication-core.md`. The calculus ingredients are
classical; historical priority of the resulting transport transition is
unresolved.
-/

public section

noncomputable section

namespace TauCeti

/-- The scalar penalty along a unitary eigenphase. -/
@[expose] def smoothedPowerPhaseCost (p tau t : ℝ) : ℝ :=
  (tau ^ 2 + 2 - 2 * Real.cos t) ^ (p / 2) - tau ^ p

/-- The phase gradient of the smoothed-power penalty. -/
@[expose] def smoothedPowerPhaseSlope (p tau t : ℝ) : ℝ :=
  p * Real.sin t * (tau ^ 2 + 2 - 2 * Real.cos t) ^ ((p - 2) / 2)

/-- The phase curvature, factored into a positive radial term and a
quadratic polynomial in the cosine. -/
@[expose] def smoothedPowerPhaseCurvature (p tau t : ℝ) : ℝ :=
  p * (tau ^ 2 + 2 - 2 * Real.cos t) ^ (p / 2 - 2) *
    (p - 2 + (tau ^ 2 + 2) * Real.cos t - p * Real.cos t ^ 2)

theorem smoothedPowerPhase_radicand_pos (tau t : ℝ) (htau : 0 < tau) :
    0 < tau ^ 2 + 2 - 2 * Real.cos t := by
  nlinarith [Real.cos_le_one t, sq_pos_of_pos htau]

/-- Actual first derivative, uniformly in the exponent. -/
theorem hasDerivAt_smoothedPowerPhaseCost (p tau t : ℝ) (htau : 0 < tau) :
    HasDerivAt (smoothedPowerPhaseCost p tau) (smoothedPowerPhaseSlope p tau t) t := by
  have hr : HasDerivAt (fun x => tau ^ 2 + 2 - 2 * Real.cos x) (2 * Real.sin t) t := by
    convert (hasDerivAt_const t (tau ^ 2 + 2)).sub ((Real.hasDerivAt_cos t).const_mul 2) using 1
    ring
  have hd := (hr.rpow_const (p := p / 2)
    (Or.inl (smoothedPowerPhase_radicand_pos tau t htau).ne')).sub_const (tau ^ p)
  apply hd.congr_deriv
  dsimp only [smoothedPowerPhaseSlope]
  rw [show (p - 2) / 2 = p / 2 - 1 by ring]
  ring

/-- Actual second derivative. The same formula controls both the strict
Schatten and Charbonnier phase symbols when their parameters specialize. -/
theorem hasDerivAt_smoothedPowerPhaseSlope (p tau t : ℝ) (htau : 0 < tau) :
    HasDerivAt (smoothedPowerPhaseSlope p tau) (smoothedPowerPhaseCurvature p tau t) t := by
  let R := tau ^ 2 + 2 - 2 * Real.cos t
  have hR : 0 < R := smoothedPowerPhase_radicand_pos tau t htau
  have hr : HasDerivAt (fun x => tau ^ 2 + 2 - 2 * Real.cos x) (2 * Real.sin t) t := by
    convert (hasDerivAt_const t (tau ^ 2 + 2)).sub ((Real.hasDerivAt_cos t).const_mul 2) using 1
    ring
  have hd := ((Real.hasDerivAt_sin t).const_mul p).mul
    (hr.rpow_const (p := (p - 2) / 2) (Or.inl hR.ne'))
  apply hd.congr_deriv
  have heq : R ^ ((p - 2) / 2) = R ^ (p / 2 - 2) * R := by
    calc
      _ = R ^ ((p / 2 - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hR, Real.rpow_one]
  change p * Real.cos t * R ^ ((p - 2) / 2) +
    p * Real.sin t * (2 * Real.sin t * ((p - 2) / 2) * R ^ ((p - 2) / 2 - 1)) = _
  rw [heq, show (p - 2) / 2 - 1 = p / 2 - 2 by ring]
  dsimp only [smoothedPowerPhaseCurvature]
  change _ = p * R ^ (p / 2 - 2) * _
  have hpoly : Real.cos t * R + (p - 2) * Real.sin t ^ 2 =
      p - 2 + (tau ^ 2 + 2) * Real.cos t - p * Real.cos t ^ 2 := by
    dsimp only [R]
    nlinarith [Real.sin_sq_add_cos_sq t,
      congrArg (fun r : ℝ => p * r) (Real.sin_sq_add_cos_sq t)]
  calc
    _ = p * R ^ (p / 2 - 2) * (Real.cos t * R + (p - 2) * Real.sin t ^ 2) := by ring
    _ = _ := by rw [hpoly]

/-- Curvature has exactly the sign of its quadratic cosine polynomial. -/
theorem smoothedPowerPhaseCurvature_neg_iff
    (p tau t : ℝ) (hp : 0 < p) (htau : 0 < tau) :
    smoothedPowerPhaseCurvature p tau t < 0 ↔
      p - 2 + (tau ^ 2 + 2) * Real.cos t - p * Real.cos t ^ 2 < 0 := by
  unfold smoothedPowerPhaseCurvature
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀
      (mul_pos hp (Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau t htau) _))
      (b := p - 2 + (tau ^ 2 + 2) * Real.cos t - p * Real.cos t ^ 2) (c := 0))

/-- The smaller curvature root. Its role as the global scalar minimizer
transition requires a separate phase-selection argument. -/
@[expose] def smoothedPowerCriticalCosine (p tau : ℝ) : ℝ :=
  (tau ^ 2 + 2 - Real.sqrt ((tau ^ 2 + 2) ^ 2 - 4 * p * (2 - p))) / (2 * p)

private theorem smoothedPower_root_data (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    let B := tau ^ 2 + 2
    let D := B ^ 2 - 4 * p * (2 - p)
    0 < D ∧
      0 ≤ (B - Real.sqrt D) / (2 * p) ∧
      (B - Real.sqrt D) / (2 * p) < 1 ∧
      1 < (B + Real.sqrt D) / (2 * p) := by
  dsimp only
  let B := tau ^ 2 + 2
  let D := B ^ 2 - 4 * p * (2 - p)
  change 0 < D ∧ 0 ≤ (B - Real.sqrt D) / (2 * p) ∧
    (B - Real.sqrt D) / (2 * p) < 1 ∧ 1 < (B + Real.sqrt D) / (2 * p)
  have hB : 2 < B := by dsimp only [B]; nlinarith [sq_pos_of_pos htau]
  have hp0 : 0 < p := by linarith
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [sq_nonneg (p - 1)]
  have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hs0 := Real.sqrt_nonneg D
  have hle : Real.sqrt D ≤ B := by
    have hprod : 0 ≤ p * (2 - p) := mul_nonneg hp0.le (by linarith)
    dsimp only [D] at hs
    nlinarith
  have hgap : |B - 2 * p| < Real.sqrt D := by
    apply (sq_lt_sq₀ (abs_nonneg _) hs0).mp
    rw [sq_abs, hs]
    dsimp only [D]
    nlinarith
  refine ⟨hD, div_nonneg (sub_nonneg.mpr hle) (by positivity), ?_, ?_⟩
  · apply (div_lt_one (by positivity : 0 < 2 * p)).mpr
    have hg := lt_of_le_of_lt (le_abs_self (B - 2 * p)) hgap
    linarith
  · apply (one_lt_div₀ (by positivity : 0 < 2 * p)).mpr
    have hg := lt_of_le_of_lt (neg_le_abs (B - 2 * p)) hgap
    linarith

/-- The candidate critical cosine is a genuine interior-to-identity
curvature threshold, including the quadratic value zero. -/
theorem smoothedPowerCriticalCosine_mem (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    smoothedPowerCriticalCosine p tau ∈ Set.Ico 0 1 := by
  have h := smoothedPower_root_data p tau hp hp2 htau
  exact ⟨h.2.1, h.2.2.1⟩

private theorem smoothedPowerPhaseCurvature_pos_factor
    (p tau t : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    ∃ k > 0, smoothedPowerPhaseCurvature p tau t =
      k * (Real.cos t - smoothedPowerCriticalCosine p tau) := by
  let B := tau ^ 2 + 2
  let D := B ^ 2 - 4 * p * (2 - p)
  let C := (B - Real.sqrt D) / (2 * p)
  let L := (B + Real.sqrt D) / (2 * p)
  have hdata := smoothedPower_root_data p tau hp hp2 htau
  have hD : 0 < D := hdata.1
  have hL : 1 < L := hdata.2.2.2
  have hp0 : 0 < p := by linarith
  have hfactor : p - 2 + B * Real.cos t - p * Real.cos t ^ 2 =
      p * (L - Real.cos t) * (Real.cos t - C) := by
    dsimp only [L, C]
    field_simp
    nlinarith [Real.sq_sqrt hD.le]
  refine ⟨p * (tau ^ 2 + 2 - 2 * Real.cos t) ^ (p / 2 - 2) *
    (p * (L - Real.cos t)), ?_, ?_⟩
  · exact mul_pos (mul_pos hp0
      (Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau t htau) _))
        (mul_pos hp0 (by linarith [Real.cos_le_one t]))
  · unfold smoothedPowerPhaseCurvature
    change p * (tau ^ 2 + 2 - 2 * Real.cos t) ^ (p / 2 - 2) *
      (p - 2 + B * Real.cos t - p * Real.cos t ^ 2) = _
    change _ = _ * (Real.cos t - C)
    rw [hfactor]
    ring

/-- The proposed critical surface is exactly the change of sign of the
actual phase curvature. This alone does not assert planar or ambient global
optimality. -/
theorem smoothedPowerPhaseCurvature_neg_iff_cos_lt_critical
    (p tau t : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    smoothedPowerPhaseCurvature p tau t < 0 ↔
      Real.cos t < smoothedPowerCriticalCosine p tau := by
  obtain ⟨k, hk, heq⟩ := smoothedPowerPhaseCurvature_pos_factor p tau t hp hp2 htau
  rw [heq]
  simpa only [mul_zero, sub_neg] using
    (mul_lt_mul_iff_right₀ hk (b := Real.cos t - smoothedPowerCriticalCosine p tau) (c := 0))

/-- The increasing branch is exactly the region above the critical
cosine. -/
theorem smoothedPowerPhaseCurvature_pos_iff_critical_lt_cos
    (p tau t : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    0 < smoothedPowerPhaseCurvature p tau t ↔
      smoothedPowerCriticalCosine p tau < Real.cos t := by
  obtain ⟨k, hk, heq⟩ := smoothedPowerPhaseCurvature_pos_factor p tau t hp hp2 htau
  rw [heq, mul_pos_iff_of_pos_left hk, sub_pos]

/-- The phase slope has exactly one peak: its increasing branch is
uniform throughout the family. -/
theorem smoothedPowerPhaseSlope_strictMonoOn
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    StrictMonoOn (smoothedPowerPhaseSlope p tau)
      (Set.Icc 0 (Real.arccos (smoothedPowerCriticalCosine p tau))) := by
  have hc := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (hasDerivAt_smoothedPowerPhaseSlope p tau t htau).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_smoothedPowerPhaseSlope p tau t htau).deriv,
    smoothedPowerPhaseCurvature_pos_iff_critical_lt_cos p tau t hp hp2 htau]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le
    (Real.arccos_le_pi _) ht.2
  rwa [Real.cos_arccos
    (by linarith [hc.1] : -1 ≤ smoothedPowerCriticalCosine p tau) hc.2.le] at hcos

/-- The same phase slope strictly decreases beyond its critical angle.
Together with the increasing branch, this verifies the single-peak shape
hypothesis of the proposed decoupling theorem for positive smoothing. -/
theorem smoothedPowerPhaseSlope_strictAntiOn
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    StrictAntiOn (smoothedPowerPhaseSlope p tau)
      (Set.Icc (Real.arccos (smoothedPowerCriticalCosine p tau)) Real.pi) := by
  have hc := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun t _ => (hasDerivAt_smoothedPowerPhaseSlope p tau t htau).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_smoothedPowerPhaseSlope p tau t htau).deriv,
    smoothedPowerPhaseCurvature_neg_iff_cos_lt_critical p tau t hp hp2 htau]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) ht.2.le ht.1
  rwa [Real.cos_arccos
    (by linarith [hc.1] : -1 ≤ smoothedPowerCriticalCosine p tau) hc.2.le] at hcos

/-- The zero-smoothing critical surface reduces to the strict-Schatten
cosine `(2-p)/p`, including its two endpoint values. -/
theorem smoothedPowerCriticalCosine_zero (p : ℝ) (hp : 1 ≤ p) :
    smoothedPowerCriticalCosine p 0 = (2 - p) / p := by
  unfold smoothedPowerCriticalCosine
  norm_num only [zero_pow, zero_add]
  rw [show (4 : ℝ) - 4 * p * (2 - p) = (2 * p - 2) ^ 2 by ring,
    Real.sqrt_sq (by linarith : 0 ≤ 2 * p - 2)]
  field_simp
  ring

/-- Quadratic phase curvature changes sign at cosine zero, independently
of smoothing. This does not imply a nonzero optimal planar phase. -/
theorem smoothedPowerCriticalCosine_two (tau : ℝ) :
    smoothedPowerCriticalCosine 2 tau = 0 := by
  unfold smoothedPowerCriticalCosine
  norm_num only [sub_self, mul_zero, sub_zero]
  rw [Real.sqrt_sq (by positivity : 0 ≤ tau ^ 2 + 2)]
  simp

/-- Phase curvature is unchanged when the phase is reversed. -/
theorem smoothedPowerPhaseCurvature_neg (p tau t : ℝ) :
    smoothedPowerPhaseCurvature p tau (-t) = smoothedPowerPhaseCurvature p tau t := by
  simp only [smoothedPowerPhaseCurvature, Real.cos_neg]

end TauCeti
