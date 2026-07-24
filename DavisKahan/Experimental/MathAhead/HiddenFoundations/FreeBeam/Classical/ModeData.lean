/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.CharacteristicConverse
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.SmoothGreenIdentity
import Mathlib.Tactic

/-!
# Classical characteristic modes as fourth-order derivative data

This file connects the closed-form mode calculations to the smooth Green and
kernel infrastructure.  A characteristic root now produces a concrete
`FourthOrderData` object satisfying the free conditions and the fourth-order
eigen-equation.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Classical

noncomputable section

open MathAhead.HiddenFoundations.FreeBeam

/-- The real closed-form beam mode bundled with all four derivative
relations. -/
noncomputable def modeData (beta a b c d : ℝ) : FourthOrderData where
  f0 := MathAhead.HiddenFoundations.FreeBeam.mode beta a b c d
  f1 := MathAhead.HiddenFoundations.FreeBeam.modeD1 beta a b c d
  f2 := MathAhead.HiddenFoundations.FreeBeam.modeD2 beta a b c d
  f3 := MathAhead.HiddenFoundations.FreeBeam.modeD3 beta a b c d
  f4 := MathAhead.HiddenFoundations.FreeBeam.modeD4 beta a b c d
  continuous0 := continuous_iff_continuousAt.mpr fun x =>
    (MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_mode beta a b c d x).continuousAt
  continuous1 := continuous_iff_continuousAt.mpr fun x =>
    (MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD1 beta a b c d x).continuousAt
  continuous2 := continuous_iff_continuousAt.mpr fun x =>
    (MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD2 beta a b c d x).continuousAt
  continuous3 := continuous_iff_continuousAt.mpr fun x =>
    (MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD3 beta a b c d x).continuousAt
  continuous4 := by
    unfold MathAhead.HiddenFoundations.FreeBeam.modeD4
    exact continuous_const.mul
      (continuous_iff_continuousAt.mpr fun x =>
        (MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_mode beta a b c d x).continuousAt)
  deriv0 := MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_mode beta a b c d
  deriv1 := MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD1 beta a b c d
  deriv2 := MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD2 beta a b c d
  deriv3 := MathAhead.HiddenFoundations.FreeBeam.hasDerivAt_modeD3 beta a b c d

@[simp] theorem modeData_f0 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f0 x =
      MathAhead.HiddenFoundations.FreeBeam.mode beta a b c d x := rfl

@[simp] theorem modeData_f1 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f1 x =
      MathAhead.HiddenFoundations.FreeBeam.modeD1 beta a b c d x := rfl

@[simp] theorem modeData_f2 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f2 x =
      MathAhead.HiddenFoundations.FreeBeam.modeD2 beta a b c d x := rfl

@[simp] theorem modeData_f3 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f3 x =
      MathAhead.HiddenFoundations.FreeBeam.modeD3 beta a b c d x := rfl

@[simp] theorem modeData_f4 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f4 x =
      MathAhead.HiddenFoundations.FreeBeam.modeD4 beta a b c d x := rfl

/-- The bundled and unbundled free boundary predicates agree exactly. -/
theorem modeData_freeBoundary_iff (beta a b c d : ℝ) :
    (modeData beta a b c d).FreeBoundary ↔
      MathAhead.HiddenFoundations.FreeBeam.FreeBoundary beta a b c d := by
  rfl

/-- Every bundled mode satisfies the fourth-order eigen-equation. -/
theorem modeData_eigen_equation (beta a b c d x : ℝ) :
    (modeData beta a b c d).f4 x =
      beta ^ 4 * (modeData beta a b c d).f0 x := by
  rfl

/-- Initial value of the identified-coefficient mode. -/
theorem mode_identified_value_zero (beta a b : ℝ) :
    MathAhead.HiddenFoundations.FreeBeam.mode beta a b a b 0 = 2 * a := by
  simp [MathAhead.HiddenFoundations.FreeBeam.mode]
  ring

/-- Initial derivative of the identified-coefficient mode. -/
theorem modeD1_identified_value_zero (beta a b : ℝ) :
    MathAhead.HiddenFoundations.FreeBeam.modeD1 beta a b a b 0 =
      2 * beta * b := by
  simp [MathAhead.HiddenFoundations.FreeBeam.modeD1]
  ring

/-- A nonzero reduced coefficient vector at nonzero frequency has a nonzero
initial position-or-velocity jet. -/
theorem mode_identified_nontrivial_jet
    {beta a b : ℝ} (hbeta : beta ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    (modeData beta a b a b).f0 0 ≠ 0 ∨
      (modeData beta a b a b).f1 0 ≠ 0 := by
  rcases hab with ha | hb
  · left
    rw [modeData_f0, mode_identified_value_zero]
    exact mul_ne_zero (by norm_num) ha
  · right
    rw [modeData_f1, modeD1_identified_value_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hbeta) hb

/-- A characteristic root produces a concrete free fourth-order datum with a
nonzero initial jet. -/
theorem exists_free_modeData_of_characteristic
    {beta : ℝ} (hbeta : beta ≠ 0)
    (hroot : MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0) :
    ∃ u : FourthOrderData,
      u.FreeBoundary ∧
      (∀ x, u.f4 x = beta ^ 4 * u.f0 x) ∧
      (u.f0 0 ≠ 0 ∨ u.f1 0 ≠ 0) := by
  obtain ⟨a, b, hab, hfree⟩ :=
    exists_nontrivial_freeBoundary_of_characteristic hbeta hroot
  refine ⟨modeData beta a b a b, ?_, ?_, ?_⟩
  · exact (modeData_freeBoundary_iff beta a b a b).mpr hfree
  · exact modeData_eigen_equation beta a b a b
  · exact mode_identified_nontrivial_jet hbeta hab

/-- Positive characteristic roots produce nonzero smooth eigenvalues above
`500` once the scalar localization interface is supplied. -/
theorem free_modeData_eigenvalue_gt_five_hundred
    (L : MathAhead.HiddenFoundations.FreeBeam.PositiveRootLocalization)
    {beta : ℝ} (hbeta : 0 < beta)
    (hroot : MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0) :
    ∃ u : FourthOrderData,
      u.FreeBoundary ∧
      (∀ x, u.f4 x = beta ^ 4 * u.f0 x) ∧
      (u.f0 0 ≠ 0 ∨ u.f1 0 ≠ 0) ∧
      500 < beta ^ 4 := by
  obtain ⟨u, hu, heig, hnonzero⟩ :=
    exists_free_modeData_of_characteristic hbeta.ne' hroot
  exact ⟨u, hu, heig, hnonzero,
    MathAhead.HiddenFoundations.FreeBeam.positive_root_fourth_power_gt_five_hundred
      L hbeta hroot⟩

end

end Classical
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti