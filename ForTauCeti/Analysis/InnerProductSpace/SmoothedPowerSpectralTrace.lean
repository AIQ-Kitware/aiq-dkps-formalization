/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralVariation
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# A common supporting field for smoothed displacement powers

The penalty `(tau² + |z - 1|²)^(p/2) - tau^p` is the restriction of the
convex Hilbert norm power to an affine plane. Positive smoothing makes its
supporting field continuous even at exponent one. The resulting trace
variation includes spectral collisions and identity eigenvalues.

## Provenance

The scalar family is the generalized Charbonnier penalty of Sun–Roth–Black
(2010), §4, with exponent `p/2` and its value at zero subtracted; see also
Barron (2019), equation (4), and the primary-source links in the unification
note. The penalty itself is prior art.

Convex norm powers, their tangent support, and normal spectral-trace
variation are classical ingredients, consumed through Mathlib and
`SpectralTrace`. This module specializes those ingredients to the common
smoothed-power family; it does not claim their historical novelty or an
unrestricted global transport theorem.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate InnerProductSpace

/-- The common displacement penalty, with its literal normalization. -/
@[expose] def smoothedPowerDisplacementSymbol (p tau : ℝ) (z : ℂ) : ℝ :=
  (tau ^ 2 + ‖z - 1‖ ^ 2) ^ (p / 2) - tau ^ p

/-- The real Euclidean supporting gradient. -/
@[expose] def smoothedPowerDisplacementGradient (p tau : ℝ) (z : ℂ) : ℂ :=
  ((p * (tau ^ 2 + ‖z - 1‖ ^ 2) ^ ((p - 2) / 2) : ℝ) : ℂ) * (z - 1)

/-- Positive smoothing keeps the radial power away from its singularity. -/
theorem smoothedPower_radicand_pos (tau : ℝ) (htau : 0 < tau) (z : ℂ) :
    0 < tau ^ 2 + ‖z - 1‖ ^ 2 := by positivity

/-- Global scalar tangent support for every convex smoothed norm power,
including exponent one. No restriction to the unit circle is needed. -/
theorem smoothedPowerDisplacement_support
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau) (z w : ℂ) :
    smoothedPowerDisplacementSymbol p tau z +
        (conj (smoothedPowerDisplacementGradient p tau z) * (w - z)).re ≤
      smoothedPowerDisplacementSymbol p tau w := by
  let x : WithLp 2 (ℝ × ℂ) := WithLp.toLp 2 (tau, z - 1)
  let y : WithLp 2 (ℝ × ℂ) := WithLp.toLp 2 (tau, w - 1)
  have hx : x ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : WithLp 2 (ℝ × ℂ) => v.fst) h
    exact htau.ne' hzero
  have hnorm (v : ℂ) (r : ℝ) :
      ‖WithLp.toLp 2 (tau, v - 1)‖ ^ r = (tau ^ 2 + ‖v - 1‖ ^ 2) ^ (r / 2) := by
    have hs : ‖WithLp.toLp 2 (tau, v - 1)‖ ^ 2 = tau ^ 2 + ‖v - 1‖ ^ 2 := by
      have hs := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (tau, v - 1))
      change ‖WithLp.toLp 2 (tau, v - 1)‖ ^ 2 = ‖tau‖ ^ 2 + ‖v - 1‖ ^ 2 at hs
      simpa only [Real.norm_eq_abs, sq_abs] using hs
    calc
      _ = (‖WithLp.toLp 2 (tau, v - 1)‖ ^ (2 : ℕ)) ^ (r / 2) := by
        rw [← Real.rpow_natCast_mul (norm_nonneg _)]
        congr 1
        ring
      _ = _ := congrArg (fun a : ℝ => a ^ (r / 2)) hs
  have hi : ⟪x, y - x⟫_ℝ = (conj (z - 1) * (w - z)).re := by
    change ⟪tau, tau - tau⟫_ℝ + ⟪z - 1, (w - 1) - (z - 1)⟫_ℝ = _
    rw [sub_self, inner_zero_right, zero_add,
      show (w - 1) - (z - 1) = w - z by ring, real_inner_eq_re_inner ℂ,
      RCLike.inner_apply']
    rfl
  have h := norm_rpow_support_of_ne_zero p hp x y hx
  rw [hnorm z p, hnorm z (p - 2), hnorm w p, hi] at h
  have hg : (conj (smoothedPowerDisplacementGradient p tau z) * (w - z)).re =
      p * (tau ^ 2 + ‖z - 1‖ ^ 2) ^ ((p - 2) / 2) *
        (conj (z - 1) * (w - z)).re := by
    simp only [smoothedPowerDisplacementGradient, map_mul, Complex.conj_ofReal,
      mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hg]
  dsimp only [smoothedPowerDisplacementSymbol]
  linarith

/-- The supporting field is continuous for every exponent under positive
smoothing. Convexity is needed for support, not for this regularity fact. -/
theorem continuous_smoothedPowerDisplacementGradient (p tau : ℝ) (htau : 0 < tau) :
    Continuous (smoothedPowerDisplacementGradient p tau) := by
  have hr : Continuous (fun z : ℂ => tau ^ 2 + ‖z - 1‖ ^ 2) := by fun_prop
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (hr.rpow_const fun z =>
      Or.inl (smoothedPower_radicand_pos tau htau z).ne'))).mul
        (continuous_id.sub continuous_const)

/-- At zero smoothing the literal family is exactly the powered
Schatten scalar penalty, for every positive exponent. -/
theorem smoothedPowerDisplacementSymbol_zero (p : ℝ) (hp : 0 < p) (z : ℂ) :
    smoothedPowerDisplacementSymbol p 0 z = ‖z - 1‖ ^ p := by
  unfold smoothedPowerDisplacementSymbol
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.zero_rpow hp.ne', sub_zero,
    ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  ring

/-- At the quadratic endpoint smoothing cancels exactly. -/
theorem smoothedPowerDisplacementSymbol_two (tau : ℝ) (z : ℂ) :
    smoothedPowerDisplacementSymbol 2 tau z = ‖z - 1‖ ^ 2 := by
  unfold smoothedPowerDisplacementSymbol
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, Real.rpow_two]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- First variation of the actual finite spectral trace throughout the
smoothed-power family. This derives from one scalar support argument,
without invoking either existing penalty-specific optimization theorem. -/
theorem hasDerivAt_smoothedPower_unitary_right_variation_at
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (LinearMap.trace ℂ E
        (cfc (fun z => (smoothedPowerDisplacementSymbol p tau z : ℂ))
          ((U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H)))).toLinearMap).re)
      (LinearMap.trace ℂ E
        (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau)
          ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t :=
  hasDerivAt_unitary_spectral_right_variation_at _ _
    (continuous_smoothedPowerDisplacementGradient p tau htau).continuousOn
    (fun z _ w _ => smoothedPowerDisplacement_support p tau hp htau z w) U H hH t

end TauCeti
