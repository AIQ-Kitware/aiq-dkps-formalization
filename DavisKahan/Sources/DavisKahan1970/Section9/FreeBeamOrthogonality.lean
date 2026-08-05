/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import ForTauCeti.Analysis.Calculus.FourthOrderGreensIdentity

/-!
# Free-beam eigenmodes at distinct frequencies are `L²`-orthogonal

Davis--Kahan 1970 Section 9's numerical example is stated against a self-adjoint
fourth-derivative operator on `L²(0,1)` with free-end boundary conditions.  The
classical side of that operator is already here — `FreeBeamCharacteristic.lean`
builds the four-parameter mode `u'''' = β⁴ u`, its derivative chain, and the
free-end conditions — and `ForTauCeti`'s
`integral_fourthDeriv_mul_eq_mul_fourthDeriv` supplies the symmetry of `d⁴/dx⁴`
under those conditions.

This module joins the two and gets the first genuinely *spectral* consequence:
modes at frequencies with `β⁴ ≠ γ⁴` are orthogonal in `L²(0,1)`.  That is the
statement an eigenbasis is built from, and it is what makes the operator's
spectral decomposition — and hence Section 9's angle quantities — meaningful
rather than nominal.

The argument is the classical one, in one line once the symmetry is available:
Green's identity turns `∫ v u''''` into `∫ u v''''`, the eigenvalue equation
turns those into `β⁴ ∫ v u` and `γ⁴ ∫ u v`, and `β⁴ ≠ γ⁴` forces the common
integral to vanish.

## What this does *not* yet do

It does not build the operator.  Remaining for that: completeness of the mode
family in `L²(0,1)`, and the passage from the classical modes to a densely
defined self-adjoint operator.  Both are open; this is the brick they rest on.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam

noncomputable section

/-! ### Continuity of the mode and its derivative chain -/

/-- The classical mode is continuous. -/
theorem continuous_mode (beta a b c d : ℝ) : Continuous (mode beta a b c d) := by
  unfold mode; fun_prop

/-- The first derivative is continuous. -/
theorem continuous_modeD1 (beta a b c d : ℝ) : Continuous (modeD1 beta a b c d) := by
  unfold modeD1; fun_prop

/-- The second derivative is continuous. -/
theorem continuous_modeD2 (beta a b c d : ℝ) : Continuous (modeD2 beta a b c d) := by
  unfold modeD2; fun_prop

/-- The third derivative is continuous. -/
theorem continuous_modeD3 (beta a b c d : ℝ) : Continuous (modeD3 beta a b c d) := by
  unfold modeD3; fun_prop

/-- The fourth derivative is continuous. -/
theorem continuous_modeD4 (beta a b c d : ℝ) : Continuous (modeD4 beta a b c d) := by
  unfold modeD4
  exact continuous_const.mul (continuous_mode beta a b c d)

/-! ### Orthogonality -/

/-- **Free-beam modes at distinct frequencies are `L²(0,1)`-orthogonal.**

Green's identity moves the fourth derivative across the pairing; the eigenvalue
equation `u'''' = β⁴ u` turns both sides into multiples of the same integral;
and `β⁴ ≠ γ⁴` forces it to vanish.

This is the first spectral fact about the free-beam operator that does not
depend on constructing the operator itself. -/
theorem integral_mode_mul_eq_zero_of_ne
    {beta a b c d gamma a' b' c' d' : ℝ}
    (hu : FreeBoundary beta a b c d) (hv : FreeBoundary gamma a' b' c' d')
    (hne : beta ^ 4 ≠ gamma ^ 4) :
    ∫ x in (0 : ℝ)..1, mode beta a b c d x * mode gamma a' b' c' d' x = 0 := by
  set u := mode beta a b c d with hudef
  set v := mode gamma a' b' c' d' with hvdef
  obtain ⟨hu2zero, hu3zero, hu2one, hu3one⟩ := hu
  obtain ⟨hv2zero, hv3zero, hv2one, hv3one⟩ := hv
  -- Green's identity for the two modes.
  have hgreen := TauCeti.integral_fourthDeriv_mul_eq_mul_fourthDeriv
    (u := u) (u1 := modeD1 beta a b c d) (u2 := modeD2 beta a b c d)
    (u3 := modeD3 beta a b c d) (u4 := modeD4 beta a b c d)
    (v := v) (v1 := modeD1 gamma a' b' c' d') (v2 := modeD2 gamma a' b' c' d')
    (v3 := modeD3 gamma a' b' c' d') (v4 := modeD4 gamma a' b' c' d')
    (continuous_mode _ _ _ _ _) (continuous_modeD1 _ _ _ _ _)
    (continuous_modeD2 _ _ _ _ _) (continuous_modeD3 _ _ _ _ _)
    (continuous_modeD4 _ _ _ _ _)
    (continuous_mode _ _ _ _ _) (continuous_modeD1 _ _ _ _ _)
    (continuous_modeD2 _ _ _ _ _) (continuous_modeD3 _ _ _ _ _)
    (continuous_modeD4 _ _ _ _ _)
    (hasDerivAt_mode beta a b c d) (hasDerivAt_modeD1 beta a b c d)
    (hasDerivAt_modeD2 beta a b c d) (hasDerivAt_modeD3 beta a b c d)
    (hasDerivAt_mode gamma a' b' c' d') (hasDerivAt_modeD1 gamma a' b' c' d')
    (hasDerivAt_modeD2 gamma a' b' c' d') (hasDerivAt_modeD3 gamma a' b' c' d')
    hu2zero hu2one hu3zero hu3one hv2zero hv2one hv3zero hv3one
  -- Replace the fourth derivatives by their eigenvalue multiples.
  have hu4 : ∀ x, modeD4 beta a b c d x = beta ^ 4 * u x := fun x => rfl
  have hv4 : ∀ x, modeD4 gamma a' b' c' d' x = gamma ^ 4 * v x := fun x => rfl
  simp only [hu4, hv4] at hgreen
  -- Both sides are scalar multiples of `∫ u v`.
  have hleft : ∫ x in (0 : ℝ)..1, v x * (beta ^ 4 * u x) =
      beta ^ 4 * ∫ x in (0 : ℝ)..1, u x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring
  have hright : ∫ x in (0 : ℝ)..1, u x * (gamma ^ 4 * v x) =
      gamma ^ 4 * ∫ x in (0 : ℝ)..1, u x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    ring
  rw [hleft, hright] at hgreen
  have hfactor : (beta ^ 4 - gamma ^ 4) * ∫ x in (0 : ℝ)..1, u x * v x = 0 := by
    linarith [hgreen]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

end

end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
