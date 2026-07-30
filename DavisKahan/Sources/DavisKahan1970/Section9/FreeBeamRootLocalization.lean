/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import Mathlib.Tactic

/-!
# Reduction of free-beam root localization to scalar certificates

The operator campaign only needs a reusable certificate that the first positive
root of `cos beta * cosh beta = 1` lies above `4.73`.  This file isolates the
remaining scalar analysis into small sign and exclusion obligations.

It deliberately does not claim a numerical transcendental estimate that has
not yet been proved.  Instead it supplies exact constructors showing which
finite set of scalar facts is sufficient for `PositiveRootLocalization`.
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

/-- Continuity of the characteristic function. -/
theorem continuous_characteristic :
    Continuous MathAhead.HiddenFoundations.FreeBeam.characteristic := by
  unfold MathAhead.HiddenFoundations.FreeBeam.characteristic
  exact (Real.continuous_cos.mul Real.continuous_cosh).sub continuous_const

/-- The characteristic equation in its usual multiplicative form. -/
theorem characteristic_eq_zero_iff (beta : ℝ) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0 ↔
      Real.cos beta * Real.cosh beta = 1 := by
  unfold MathAhead.HiddenFoundations.FreeBeam.characteristic
  exact sub_eq_zero

/-- No root can occur where cosine is nonpositive. -/
theorem characteristic_lt_zero_of_cos_nonpos
    {beta : ℝ} (hcos : Real.cos beta ≤ 0) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic beta < 0 := by
  unfold MathAhead.HiddenFoundations.FreeBeam.characteristic
  have hcosh : 0 < Real.cosh beta := Real.cosh_pos beta
  have hprod : Real.cos beta * Real.cosh beta ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcos hcosh.le
  linarith

/-- Sign exclusion version of the preceding result. -/
theorem characteristic_ne_zero_of_cos_nonpos
    {beta : ℝ} (hcos : Real.cos beta ≤ 0) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0 :=
  ne_of_lt (characteristic_lt_zero_of_cos_nonpos hcos)

/-- A strict upper bound on `cos beta * cosh beta` excludes a root. -/
theorem characteristic_ne_zero_of_product_lt_one
    {beta : ℝ} (h : Real.cos beta * Real.cosh beta < 1) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0 := by
  unfold MathAhead.HiddenFoundations.FreeBeam.characteristic
  linarith

/-- A strict lower bound on `cos beta * cosh beta` excludes a root. -/
theorem characteristic_ne_zero_of_one_lt_product
    {beta : ℝ} (h : 1 < Real.cos beta * Real.cosh beta) :
    MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0 := by
  unfold MathAhead.HiddenFoundations.FreeBeam.characteristic
  linarith

/-- Exact certificate that a displayed root is the first positive root. -/
structure FirstPositiveRootCertificate where
  root : ℝ
  root_pos : 0 < root
  root_equation :
    MathAhead.HiddenFoundations.FreeBeam.characteristic root = 0
  no_smaller_positive_root : ∀ beta : ℝ,
    0 < beta → beta < root →
      MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0
  lower_bound : (473 : ℝ) / 100 < root

/-- The scalar first-root certificate supplies the interface consumed by the
operator-theoretic development. -/
noncomputable def FirstPositiveRootCertificate.toPositiveRootLocalization
    (C : FirstPositiveRootCertificate) :
    MathAhead.HiddenFoundations.FreeBeam.PositiveRootLocalization where
  firstPositiveRoot := C.root
  firstPositiveRoot_pos := C.root_pos
  firstPositiveRoot_characteristic := C.root_equation
  minimal := by
    intro beta hbeta hroot
    by_contra hle
    have hlt : beta < C.root := lt_of_not_ge hle
    exact C.no_smaller_positive_root beta hbeta hlt hroot
  lower_bound := C.lower_bound

/-- It is enough to exclude roots on `(0, lower]`, then on `(lower, root)`. -/
noncomputable def firstPositiveRootCertificate_of_split_exclusion
    {root lower : ℝ}
    (hroot_pos : 0 < root)
    (hroot : MathAhead.HiddenFoundations.FreeBeam.characteristic root = 0)
    (hsmall : ∀ beta : ℝ, 0 < beta → beta ≤ lower →
      MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0)
    (hmiddle : ∀ beta : ℝ, lower < beta → beta < root →
      MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0)
    (h473 : (473 : ℝ) / 100 < root) :
    FirstPositiveRootCertificate where
  root := root
  root_pos := hroot_pos
  root_equation := hroot
  no_smaller_positive_root := by
    intro beta hbeta hbeta_root
    by_cases hle : beta ≤ lower
    · exact hsmall beta hbeta hle
    · exact hmiddle beta (lt_of_not_ge hle) hbeta_root
  lower_bound := h473

/-- A sign partition can discharge a root-exclusion interval pointwise. -/
theorem root_exclusion_of_pointwise_sign
    {S : Set ℝ}
    (hsign : ∀ beta ∈ S,
      Real.cos beta ≤ 0 ∨
      Real.cos beta * Real.cosh beta < 1 ∨
      1 < Real.cos beta * Real.cosh beta) :
    ∀ beta ∈ S,
      MathAhead.HiddenFoundations.FreeBeam.characteristic beta ≠ 0 := by
  intro beta hbeta
  rcases hsign beta hbeta with hcos | hlt | hgt
  · exact characteristic_ne_zero_of_cos_nonpos hcos
  · exact characteristic_ne_zero_of_product_lt_one hlt
  · exact characteristic_ne_zero_of_one_lt_product hgt

/-- Any completed first-root certificate gives the numerical eigenvalue bound
used by the free-beam application. -/
theorem positive_root_pow_four_gt_five_hundred_of_certificate
    (C : FirstPositiveRootCertificate)
    {beta : ℝ} (hbeta : 0 < beta)
    (hroot : MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0) :
    500 < beta ^ 4 :=
  MathAhead.HiddenFoundations.FreeBeam.positive_root_fourth_power_gt_five_hundred
    C.toPositiveRootLocalization hbeta hroot

end

end Classical
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti