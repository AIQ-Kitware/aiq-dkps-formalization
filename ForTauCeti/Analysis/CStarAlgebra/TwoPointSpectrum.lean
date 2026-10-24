/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Normal elements with two-point spectrum

A normal element whose spectrum lies in `{a, b}` is `a + (b - a) P` for
a star projection `P`. The result holds in any complex C⋆-algebra and does
not require finite dimension. It is the classical spectral-projection step
used after the two-root Schatten-gradient classification.
-/

public section

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

/-- An affine function of a star projection has spectrum contained in
the two scalar values on its complementary ranges. -/
theorem spectrum_affine_projection_subset_pair
    (P : A) (hP : IsStarProjection P) (a b : ℂ) :
    spectrum ℂ (a • (1 : A) + (b - a) • P) ⊆ {a, b} := by
  let := hP.isStarNormal
  have hspec : spectrum ℂ P ⊆ {0, 1} :=
    (isStarProjection_iff_spectrum_subset_and_isStarNormal.1 hP).1
  have heq : cfc (fun z : ℂ => a + (b - a) * z) P =
      a • (1 : A) + (b - a) • P := by
    rw [cfc_const_add a (fun z : ℂ => (b - a) * z) P,
      cfc_const_mul_id (b - a) P, Algebra.algebraMap_eq_smul_one]
  rw [← heq, cfc_map_spectrum (a := P) (f := fun z : ℂ => a + (b - a) * z)
    hP.isStarNormal (continuous_const.add (continuous_const.mul continuous_id)).continuousOn]
  rintro z ⟨w, hw, rfl⟩
  rcases hspec hw with hzero | hone
  · simp [hzero]
  · simp only [Set.mem_singleton_iff] at hone
    simp [hone]

/-- On a two-point normal spectrum, every scalar functional calculus is
affine in the same star projection. No continuity hypothesis on the scalar
function is needed because the spectrum is finite. -/
theorem exists_isStarProjection_cfc_eq_affine_of_spectrum_subset_pair
    (T : A) [IsStarNormal T] (a b : ℂ)
    (hs : spectrum ℂ T ⊆ {a, b}) :
    ∃ P : A, IsStarProjection P ∧ ∀ h : ℂ → ℂ,
      cfc h T = h a • (1 : A) + (h b - h a) • P := by
  classical
  let f : ℂ → ℂ := fun z => if z = b then 1 else 0
  have hf : ContinuousOn f (spectrum ℂ T) :=
    ((Set.finite_singleton b).insert a).subset hs |>.continuousOn f
  refine ⟨cfc f T, ⟨?_, ?_⟩, ?_⟩
  · change cfc f T * cfc f T = cfc f T
    rw [← cfc_mul f f T hf hf]
    apply cfc_congr
    intro z _
    simp [f]
  · change star (cfc f T) = cfc f T
    rw [← cfc_star]
    apply cfc_congr
    intro z _
    simp [f]
  · intro h
    have heq : cfc h T = cfc (fun z => h a + (h b - h a) * f z) T := by
      apply cfc_congr
      intro z hz
      have hz' := hs hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
      rcases hz' with hza | hzb
      · rw [hza]
        by_cases hab : a = b <;> simp [f, hab]
      · simp [hzb, f]
    calc
      cfc h T = cfc (fun z => h a + (h b - h a) * f z) T := heq
      _ = algebraMap ℂ A (h a) + cfc (fun z => (h b - h a) * f z) T :=
        cfc_const_add (h a) (fun z => (h b - h a) * f z) T (continuousOn_const.mul hf)
      _ = h a • (1 : A) + (h b - h a) • cfc f T := by
        rw [cfc_const_mul (h b - h a) f T hf, Algebra.algebraMap_eq_smul_one]

/-- A normal element with spectrum in two scalar values is affine in a
star projection. The two values need not be distinct. -/
theorem exists_isStarProjection_eq_affine_of_spectrum_subset_pair
    (T : A) [IsStarNormal T] (a b : ℂ)
    (hs : spectrum ℂ T ⊆ {a, b}) :
    ∃ P : A, IsStarProjection P ∧ T = a • (1 : A) + (b - a) • P := by
  obtain ⟨P, hP, hcfc⟩ :=
    exists_isStarProjection_cfc_eq_affine_of_spectrum_subset_pair T a b hs
  refine ⟨P, hP, ?_⟩
  have h := hcfc (fun z => z)
  rw [cfc_id' ℂ T] at h
  exact h

end TauCeti
