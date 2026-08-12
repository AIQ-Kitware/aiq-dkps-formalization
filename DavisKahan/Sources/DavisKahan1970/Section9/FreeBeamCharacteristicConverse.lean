/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import Mathlib.Tactic

/-!
# Converse characteristic construction for the free--free beam

The existing characteristic file proves that every nontrivial free mode has
`cos beta * cosh beta = 1`.  For spectral realization one also needs the
converse: every nonzero characteristic root produces a nontrivial coefficient
vector satisfying all four free endpoint equations.

This file supplies the missing two-by-two kernel construction and reconstructs
the four-parameter classical mode with coefficients `(a,b,a,b)`.
-/

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Classical

noncomputable section

open FreeBeam

/-- A singular matrix `[[A,B],[C,A]]` has a nonzero kernel vector. -/
theorem exists_nontrivial_two_by_two_kernel
    {A B C : ℝ} (hdet : A ^ 2 - B * C = 0) :
    ∃ a b : ℝ,
      (a ≠ 0 ∨ b ≠ 0) ∧
      A * a + B * b = 0 ∧
      C * a + A * b = 0 := by
  by_cases hA : A = 0
  · by_cases hB : B = 0
    · refine ⟨0, 1, by norm_num, ?_, ?_⟩
      · simp [hA, hB]
      · simp [hA]
    · refine ⟨B, -A, Or.inl hB, ?_, ?_⟩
      · ring
      · rw [hA] at hdet ⊢
        nlinarith
  · refine ⟨B, -A, ?_, ?_, ?_⟩
    · exact Or.inr (neg_ne_zero.mpr hA)
    · ring
    · nlinarith

/-- The reduced first row is exactly the right endpoint second derivative,
up to the nonzero factor `beta^2`. -/
theorem modeD2_right_eq_reduced
    (beta a b : ℝ) :
    FreeBeam.modeD2 beta a b a b 1 =
      beta ^ 2 *
        (FreeBeam.boundaryA beta * a +
          FreeBeam.boundaryB beta * b) := by
  simp only [FreeBeam.modeD2,
    FreeBeam.boundaryA,
    FreeBeam.boundaryB, mul_one]
  ring

/-- The reduced second row is exactly the right endpoint third derivative,
up to the nonzero factor `beta^3`. -/
theorem modeD3_right_eq_reduced
    (beta a b : ℝ) :
    FreeBeam.modeD3 beta a b a b 1 =
      beta ^ 3 *
        (FreeBeam.boundaryC beta * a +
          FreeBeam.boundaryA beta * b) := by
  simp only [FreeBeam.modeD3,
    FreeBeam.boundaryA,
    FreeBeam.boundaryC, mul_one]
  ring

/-- The coefficients `(a,b,a,b)` automatically satisfy both left endpoint
conditions. -/
theorem left_free_boundary_identified_coefficients
    (beta a b : ℝ) :
    FreeBeam.modeD2 beta a b a b 0 = 0 ∧
    FreeBeam.modeD3 beta a b a b 0 = 0 := by
  constructor <;>
    simp [FreeBeam.modeD2,
      FreeBeam.modeD3]

/-- A reduced kernel vector gives the two right free endpoint conditions. -/
theorem right_free_boundary_of_reduced_kernel
    {beta a b : ℝ}
    (h1 : FreeBeam.boundaryA beta * a +
      FreeBeam.boundaryB beta * b = 0)
    (h2 : FreeBeam.boundaryC beta * a +
      FreeBeam.boundaryA beta * b = 0) :
    FreeBeam.modeD2 beta a b a b 1 = 0 ∧
    FreeBeam.modeD3 beta a b a b 1 = 0 := by
  constructor
  · rw [modeD2_right_eq_reduced, h1, mul_zero]
  · rw [modeD3_right_eq_reduced, h2, mul_zero]

/-- The characteristic equation is equivalent to vanishing of the reduced
boundary determinant. -/
theorem boundaryDet_eq_zero_of_characteristic_eq_zero
    {beta : ℝ}
    (hroot : FreeBeam.characteristic beta = 0) :
    FreeBeam.boundaryDet beta = 0 := by
  rw [FreeBeam.boundaryDet_eq]
  unfold FreeBeam.characteristic at hroot
  nlinarith

/-- Every characteristic root produces nontrivial reduced coefficients. -/
theorem exists_reduced_coefficients_of_characteristic
    {beta : ℝ}
    (hroot : FreeBeam.characteristic beta = 0) :
    ∃ a b : ℝ,
      (a ≠ 0 ∨ b ≠ 0) ∧
      FreeBeam.boundaryA beta * a +
        FreeBeam.boundaryB beta * b = 0 ∧
      FreeBeam.boundaryC beta * a +
        FreeBeam.boundaryA beta * b = 0 := by
  apply exists_nontrivial_two_by_two_kernel
  exact boundaryDet_eq_zero_of_characteristic_eq_zero hroot

/-- Every nonzero characteristic root produces a nontrivial classical
free--free mode. -/
theorem exists_nontrivial_freeBoundary_of_characteristic
    {beta : ℝ} (_hbeta : beta ≠ 0)
    (hroot : FreeBeam.characteristic beta = 0) :
    ∃ a b : ℝ,
      (a ≠ 0 ∨ b ≠ 0) ∧
      FreeBeam.FreeBoundary beta a b a b := by
  obtain ⟨a, b, hab, h1, h2⟩ :=
    exists_reduced_coefficients_of_characteristic hroot
  obtain ⟨h20, h30⟩ := left_free_boundary_identified_coefficients beta a b
  obtain ⟨h21, h31⟩ := right_free_boundary_of_reduced_kernel h1 h2
  exact ⟨a, b, hab, h20, h30, h21, h31⟩

/-- At nonzero frequency, the classical characteristic equation is equivalent
to existence of a nontrivial free mode. -/
theorem characteristic_iff_exists_nontrivial_freeBoundary
    {beta : ℝ} (hbeta : beta ≠ 0) :
    FreeBeam.characteristic beta = 0 ↔
      ∃ a b c d : ℝ,
        (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
        FreeBeam.FreeBoundary beta a b c d := by
  constructor
  · intro hroot
    obtain ⟨a, b, hab, hfree⟩ :=
      exists_nontrivial_freeBoundary_of_characteristic hbeta hroot
    refine ⟨a, b, a, b, ?_, hfree⟩
    tauto
  · rintro ⟨a, b, c, d, hnonzero, hfree⟩
    exact FreeBeam.characteristic_eq_zero_of_freeBoundary
      hbeta hfree hnonzero

end

end Classical
end FreeBeam
end DavisKahan
end TauCeti