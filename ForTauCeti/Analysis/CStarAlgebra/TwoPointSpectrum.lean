/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Algebra.Star.StarProjection

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

/-- A normal element with spectrum in two scalar values is affine in a
star projection. The two values need not be distinct. -/
theorem exists_isStarProjection_eq_affine_of_spectrum_subset_pair
    (T : A) [IsStarNormal T] (a b : ℂ)
    (hs : spectrum ℂ T ⊆ {a, b}) :
    ∃ P : A, IsStarProjection P ∧ T = a • (1 : A) + (b - a) • P := by
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
  · have heq : cfc (fun z : ℂ => z) T =
        cfc (fun z => a + (b - a) * f z) T := by
      apply cfc_congr
      intro z hz
      have hz' := hs hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
      rcases hz' with hza | hzb
      · rw [hza]
        by_cases hab : a = b <;> simp [f, hab]
      · simp [hzb, f]
    rw [cfc_id' ℂ T] at heq
    calc
      T = cfc (fun z => a + (b - a) * f z) T := heq
      _ = algebraMap ℂ A a + cfc (fun z => (b - a) * f z) T :=
        cfc_const_add a (fun z => (b - a) * f z) T (continuousOn_const.mul hf)
      _ = a • (1 : A) + (b - a) • cfc f T := by
        rw [cfc_const_mul (b - a) f T hf, Algebra.algebraMap_eq_smul_one]

end TauCeti
