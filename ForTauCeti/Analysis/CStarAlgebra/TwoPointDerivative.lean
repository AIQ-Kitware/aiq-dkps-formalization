/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum
public import ForTauCeti.Analysis.Calculus.TwoPointFactorization
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Functional-calculus derivatives at two-point normal spectra

When a scalar symbol has the same value at two spectral points, its
quadratic factor gives a direct derivative of its normal functional
calculus. The factor itself need only be continuous: its derivative is
multiplied by the zero quadratic polynomial at the base operator.

These are classical divided-difference formulas. They are developed here
for the Schatten second variation on constant-gradient spectral blocks.
-/

public section

open scoped Topology

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

private theorem hasDerivAt_mul_of_zero_of_continuousAt
    (f g : ℝ → A) (x : ℝ) (f' : A)
    (hf : HasDerivAt f f' x) (hf0 : f x = 0) (hg : ContinuousAt g x) :
    HasDerivAt (fun t => f t * g t) (f' * g x) x := by
  apply hasDerivAt_iff_tendsto_slope.2
  have h := hf.tendsto_slope.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  ext t
  simp only [slope_def_module, hf0, zero_mul, sub_zero, smul_mul_assoc]

/-- Differentiate a normal functional calculus using a quadratic factor
whose value vanishes at the base operator. No derivative of the remaining
continuous factor is required. -/
theorem hasDerivAt_cfc_of_two_point_factor
    (f k : ℂ → ℂ) (a b c : ℂ) (s : Set ℂ) (hs : IsCompact s)
    (hk : ContinuousOn k s)
    (hfactor : ∀ z ∈ s, f z = c + (z - a) * (z - b) * k z)
    (U : ℝ → A) (x : ℝ) (U' : A) (hU : HasDerivAt U U' x)
    (hnormal : ∀ t, IsStarNormal (U t)) (hspectrum : ∀ t, spectrum ℂ (U t) ⊆ s)
    (hzero : (U x - a • (1 : A)) * (U x - b • (1 : A)) = 0) :
    HasDerivAt (fun t => cfc f (U t))
      ((U' * (U x - b • (1 : A)) + (U x - a • (1 : A)) * U') * cfc k (U x)) x := by
  let q : ℂ → ℂ := fun z => (z - a) * (z - b)
  have hq : Continuous q := (continuous_id.sub continuous_const).mul
    (continuous_id.sub continuous_const)
  have heq (t : ℝ) : cfc f (U t) = c • (1 : A) +
      ((U t - a • (1 : A)) * (U t - b • (1 : A))) * cfc k (U t) := by
    let := hnormal t
    have hkT := hk.mono (hspectrum t)
    have hlin (r : ℂ) : cfc (fun z : ℂ => z - r) (U t) = U t - r • (1 : A) := by
      rw [cfc_sub (fun z : ℂ => z) (fun _ => r), cfc_id' ℂ (U t),
        cfc_const r (U t), Algebra.algebraMap_eq_smul_one]
    calc
      cfc f (U t) = cfc (fun z => c + q z * k z) (U t) :=
        cfc_congr (fun z hz => hfactor z (hspectrum t hz))
      _ = c • (1 : A) + cfc (fun z => q z * k z) (U t) := by
        rw [cfc_const_add c (fun z => q z * k z) (U t)
          (hq.continuousOn.mul hkT), Algebra.algebraMap_eq_smul_one]
      _ = c • (1 : A) + (cfc q (U t)) * cfc k (U t) := by
        rw [cfc_mul q k (U t) hq.continuousOn hkT]
      _ = c • (1 : A) +
          ((U t - a • (1 : A)) * (U t - b • (1 : A))) * cfc k (U t) := by
        rw [show cfc q (U t) = cfc (fun z : ℂ => z - a) (U t) *
            cfc (fun z : ℂ => z - b) (U t) from cfc_mul _ _ (U t), hlin, hlin]
  have hcont : ContinuousAt (fun t => cfc k (U t)) x := by
    rw [← continuousWithinAt_univ]
    exact (continuousOn_cfc A hs k hk (U x) ⟨hnormal x, hspectrum x⟩).comp
      hU.continuousAt.continuousWithinAt (fun t _ => ⟨hnormal t, hspectrum t⟩)
  have hpoly := (hU.sub_const (a • (1 : A))).mul (hU.sub_const (b • (1 : A)))
  have hd := (hasDerivAt_mul_of_zero_of_continuousAt _ _ x _ hpoly hzero hcont).const_add
    (c • (1 : A))
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)

private theorem two_point_factor_derivative_eq_compressions
    (P D : A) (hP : IsIdempotentElem P) (a b da db : ℂ) (hab : a ≠ b) :
    (D * ((a - b) • (1 - P)) + ((b - a) • P) * D) *
        ((da / (a - b)) • (1 - P) + (db / (b - a)) • P) =
      da • ((1 - P) * D * (1 - P)) + db • (P * D * P) := by
  let R : A := 1 - P
  have hRR : R * R = R := hP.one_sub
  have hRP : R * P = 0 := hP.one_sub_mul_self
  have hc1 : (da / (a - b)) * (a - b) = da := by
    field_simp [sub_ne_zero.2 hab]
  have hc2 : (da / (a - b)) * (b - a) = -da := by
    field_simp [sub_ne_zero.2 hab]
    ring
  have hc3 : (db / (b - a)) * (b - a) = db := by
    field_simp [sub_ne_zero.2 hab.symm]
  change (D * ((a - b) • R) + ((b - a) • P) * D) *
      ((da / (a - b)) • R + (db / (b - a)) • P) =
    da • (R * D * R) + db • (P * D * P)
  calc
    _ = da • (D * R) + (-da) • (P * (D * R)) + db • (P * (D * P)) := by
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
        mul_assoc, hRR, hRP, mul_zero, smul_zero, zero_add, hc1, hc2, hc3]
    _ = da • (R * D * R) + db • (P * D * P) := by
      have heq : R * D * R = D * R - P * (D * R) := by
        dsimp [R]
        noncomm_ring
      rw [heq, smul_sub, neg_smul]
      simp only [mul_assoc]
      abel

/-- At a two-point normal spectrum where a differentiable symbol takes
the same value at both points, only the two diagonal compressions occur
in the functional-calculus derivative. This holds in any complex C⋆-algebra. -/
theorem exists_projection_hasDerivAt_cfc_of_two_point_spectrum
    (f : ℂ → ℂ) (a b c : ℂ) (hab : a ≠ b) (hfa : f a = c) (hfb : f b = c)
    (s : Set ℂ) (hs : IsCompact s) (hf : ContinuousOn f s)
    (hda : DifferentiableAt ℂ f a) (hdb : DifferentiableAt ℂ f b)
    (U : ℝ → A) (x : ℝ) (U' : A) (hU : HasDerivAt U U' x)
    (hnormal : ∀ t, IsStarNormal (U t)) (hspectrum : ∀ t, spectrum ℂ (U t) ⊆ s)
    (hbase : spectrum ℂ (U x) ⊆ {a, b}) :
    ∃ P : A, IsStarProjection P ∧ U x = a • (1 : A) + (b - a) • P ∧
      HasDerivAt (fun t => cfc f (U t))
        (deriv f a • ((1 - P) * U' * (1 - P)) + deriv f b • (P * U' * P)) x := by
  let := hnormal x
  obtain ⟨P, hP, hcfc⟩ :=
    exists_isStarProjection_cfc_eq_affine_of_spectrum_subset_pair (U x) a b hbase
  have hrepr : U x = a • (1 : A) + (b - a) • P := by
    have h := hcfc (fun z => z)
    rw [cfc_id' ℂ (U x)] at h
    exact h
  have hTa : U x - a • (1 : A) = (b - a) • P := by rw [hrepr]; abel
  have hTb : U x - b • (1 : A) = (a - b) • (1 - P) := by
    rw [hrepr]
    simp only [smul_sub, sub_smul]
    abel
  have hzero : (U x - a • (1 : A)) * (U x - b • (1 : A)) = 0 := by
    rw [hTa, hTb, smul_mul_smul, hP.isIdempotentElem.mul_one_sub_self, smul_zero]
  obtain ⟨k, hk, hfactor, hka, hkb⟩ :=
    exists_continuousOn_two_point_factor f s a b c hab hfa hfb hf hda hdb
  have hkbase : cfc k (U x) = (deriv f a / (a - b)) • (1 - P) +
      (deriv f b / (b - a)) • P := by
    rw [hcfc k, hka, hkb]
    simp only [smul_sub, sub_smul]
    abel
  have hd := hasDerivAt_cfc_of_two_point_factor f k a b c s hs hk
    (fun z _ => hfactor z) U x U' hU hnormal hspectrum hzero
  refine ⟨P, hP, hrepr, hd.congr_deriv ?_⟩
  rw [hTa, hTb, hkbase]
  exact two_point_factor_derivative_eq_compressions P U' hP.isIdempotentElem
    a b (deriv f a) (deriv f b) hab

/-- The two diagonal-compression derivative, using a specified star
projection in the base operator's two-point spectral representation. -/
theorem hasDerivAt_cfc_of_affine_projection
    (f : ℂ → ℂ) (a b c : ℂ) (hab : a ≠ b) (hfa : f a = c) (hfb : f b = c)
    (s : Set ℂ) (hs : IsCompact s) (hf : ContinuousOn f s)
    (hda : DifferentiableAt ℂ f a) (hdb : DifferentiableAt ℂ f b)
    (U : ℝ → A) (x : ℝ) (U' : A) (hU : HasDerivAt U U' x)
    (hnormal : ∀ t, IsStarNormal (U t)) (hspectrum : ∀ t, spectrum ℂ (U t) ⊆ s)
    (P : A) (hP : IsStarProjection P)
    (hrepr : U x = a • (1 : A) + (b - a) • P) :
    HasDerivAt (fun t => cfc f (U t))
      (deriv f a • ((1 - P) * U' * (1 - P)) + deriv f b • (P * U' * P)) x := by
  have hbase : spectrum ℂ (U x) ⊆ {a, b} := by
    rw [hrepr]
    exact spectrum_affine_projection_subset_pair P hP a b
  obtain ⟨Q, _, hQ, hd⟩ := exists_projection_hasDerivAt_cfc_of_two_point_spectrum
    f a b c hab hfa hfb s hs hf hda hdb U x U' hU hnormal hspectrum hbase
  have hQP : Q = P := by
    apply smul_right_injective A (sub_ne_zero.2 hab.symm)
    exact add_left_cancel (hQ.symm.trans hrepr)
  rwa [hQP] at hd

end TauCeti
