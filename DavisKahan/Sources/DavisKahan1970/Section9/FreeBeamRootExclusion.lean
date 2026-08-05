/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The free-beam characteristic function has no root below `3π/2`

Davis--Kahan 1970 Section 9 needs the third eigenvalue of the free beam to
exceed `500`.  Everything downstream of that is already proved in this
directory: the eigenvalue is `β⁴` for `β` a positive root of

`characteristic β = cos β · cosh β − 1`,

and `positive_root_fourth_power_gt_five_hundred` turns `4.73 < β` into
`500 < β⁴`.  What is missing is the localization of the first positive root
itself, which is `FirstPositiveRootCertificate` — a structure the repository
never constructs.

This module supplies the part of that localization which needs no decimal
arithmetic: **`cos β · cosh β < 1` for every `β ∈ (0, 3π/2]`**, so the
characteristic function has no root there.  Since `3π/2 ≈ 4.712` and the first
root is `≈ 4.7300407`, what remains after this is only the thin interval
`(3π/2, 4.73]`, where the bound is genuinely numerical: `cos` and `cosh` are
both increasing there, so it comes down to `cos 4.73 · cosh 4.73 < 1`, whose
true value is `≈ 0.9977`.

## The argument

On `(0, π/2]` it is calculus.  Write `f = cos · cosh`.  Then `f 0 = 1`,
`f' = −sin·cosh + cos·sinh` vanishes at `0`, and `f'' = −2 sin·sinh < 0` on
`(0, π/2)`.  So `f'` is strictly decreasing from `0`, hence negative, hence `f`
is strictly decreasing from `1`.

On `[π/2, 3π/2]` there is nothing to do: `cos β ≤ 0` and `cosh β > 0`, so the
product is `≤ 0`.

## Main results

* `TauCeti.DavisKahan1970.Section9.cos_mul_cosh_lt_one_of_le_pi_div_two`
* `TauCeti.DavisKahan1970.Section9.cos_mul_cosh_lt_one_of_le_three_pi_div_two`
-/

open Real

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-! ## The first two derivatives of `cos · cosh` -/

private theorem hasDerivAt_cosMulCosh (b : ℝ) :
    HasDerivAt (fun x => Real.cos x * Real.cosh x)
      (-Real.sin b * Real.cosh b + Real.cos b * Real.sinh b) b :=
  (Real.hasDerivAt_cos b).mul (Real.hasDerivAt_cosh b)

private theorem hasDerivAt_cosMulCosh_deriv (b : ℝ) :
    HasDerivAt (fun x => -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x)
      (-(2 * (Real.sin b * Real.sinh b))) b := by
  have h1 : HasDerivAt (fun x => -Real.sin x * Real.cosh x)
      (-Real.cos b * Real.cosh b + -Real.sin b * Real.sinh b) b :=
    ((Real.hasDerivAt_sin b).neg).mul (Real.hasDerivAt_cosh b)
  have h2 : HasDerivAt (fun x => Real.cos x * Real.sinh x)
      (-Real.sin b * Real.sinh b + Real.cos b * Real.cosh b) b :=
    (Real.hasDerivAt_cos b).mul (Real.hasDerivAt_sinh b)
  have h := h1.add h2
  have heq : (-Real.cos b * Real.cosh b + -Real.sin b * Real.sinh b) +
      (-Real.sin b * Real.sinh b + Real.cos b * Real.cosh b) =
      -(2 * (Real.sin b * Real.sinh b)) := by ring
  rw [heq] at h
  exact h

/-! ## The derivative is negative, hence the function drops below `1` -/

/-- `f' = −sin·cosh + cos·sinh` is negative on `(0, π/2]`: it vanishes at `0`
and its own derivative `−2 sin·sinh` is negative throughout. -/
private theorem cosMulCosh_deriv_neg {b : ℝ} (hb : 0 < b) (hle : b ≤ π / 2) :
    -Real.sin b * Real.cosh b + Real.cos b * Real.sinh b < 0 := by
  have hanti : StrictAntiOn
      (fun x => -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x)
      (Set.Icc 0 (π / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosMulCosh_deriv x).deriv]
    have hs : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos, hx.2])
    have hh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx.1
    nlinarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_refl _, by positivity⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hb.le, hle⟩
  have h := hanti h0 hbmem hb
  simpa using h

/-- **`cos β · cosh β < 1` on `(0, π/2]`.** -/
theorem cos_mul_cosh_lt_one_of_le_pi_div_two {b : ℝ} (hb : 0 < b)
    (hle : b ≤ π / 2) : Real.cos b * Real.cosh b < 1 := by
  have hanti : StrictAntiOn (fun x => Real.cos x * Real.cosh x)
      (Set.Icc 0 (π / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosMulCosh x).deriv]
    exact cosMulCosh_deriv_neg hx.1 hx.2.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_refl _, by positivity⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hb.le, hle⟩
  have h := hanti h0 hbmem hb
  simpa using h

/-- **`cos β · cosh β < 1` on all of `(0, 3π/2]`.**

Past `π/2` the cosine is nonpositive, so the product is nonpositive and there is
nothing to prove; the content is entirely in the first quarter period. -/
theorem cos_mul_cosh_lt_one_of_le_three_pi_div_two {b : ℝ} (hb : 0 < b)
    (hle : b ≤ 3 * π / 2) : Real.cos b * Real.cosh b < 1 := by
  rcases le_or_gt b (π / 2) with h | h
  · exact cos_mul_cosh_lt_one_of_le_pi_div_two hb h
  · have hcos : Real.cos b ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h.le (by linarith)
    have hcosh : 0 < Real.cosh b := Real.cosh_pos b
    nlinarith

end Section9
end DavisKahan1970
end TauCeti
