/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace

/-!
# Supporting fields and first variations of Charbonnier spectral traces

The scalar supporting inequality holds on the entire complex plane when
the smoothing parameter is positive. It gives the first variation along
normal operator curves without differentiating eigenvalues or assuming
simple spectra. The displacement may vanish.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate

/-- The literal scalar Charbonnier displacement penalty. -/
@[expose] def charbonnierDisplacementSymbol (tau : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) - tau

/-- Its complex gradient for the real Euclidean inner product. -/
@[expose] def charbonnierDisplacementGradient (tau : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2))⁻¹ : ℝ) * (z - 1)

/-- Positive smoothing keeps the scalar denominator away from zero. -/
theorem charbonnier_radius_pos (tau : ℝ) (htau : 0 < tau) (z : ℂ) :
    0 < Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) := by
  apply Real.sqrt_pos.mpr
  positivity

private theorem augmented_cauchy (tau : ℝ) (z w : ℂ) :
    tau ^ 2 + (conj (z - 1) * (w - 1)).re ≤
      Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) *
        Real.sqrt (tau ^ 2 + ‖w - 1‖ ^ 2) := by
  have hr := Complex.re_le_norm (conj (z - 1) * (w - 1))
  rw [norm_mul, Complex.norm_conj] at hr
  apply le_trans (add_le_add le_rfl hr)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith only [mul_nonneg (sq_nonneg tau) (sq_nonneg (‖z - 1‖ - ‖w - 1‖))]

/-- Global scalar tangent support for the Charbonnier displacement,
including the identity where displacement is zero. -/
theorem charbonnierDisplacement_support (tau : ℝ) (htau : 0 < tau) (z w : ℂ) :
    charbonnierDisplacementSymbol tau z +
        (conj (charbonnierDisplacementGradient tau z) * (w - z)).re ≤
      charbonnierDisplacementSymbol tau w := by
  let r := Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2)
  let q := Real.sqrt (tau ^ 2 + ‖w - 1‖ ^ 2)
  have hr : 0 < r := charbonnier_radius_pos tau htau z
  have hrsq : r ^ 2 = tau ^ 2 + ‖z - 1‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hdiff : (conj (z - 1) * (w - z)).re =
      (conj (z - 1) * (w - 1)).re - ‖z - 1‖ ^ 2 := by
    rw [show w - z = (w - 1) - (z - 1) by ring, mul_sub, Complex.sub_re,
      RCLike.conj_mul]
    norm_cast
  have hgrad : (conj (charbonnierDisplacementGradient tau z) * (w - z)).re =
      ((conj (z - 1) * (w - 1)).re - ‖z - 1‖ ^ 2) / r := by
    calc
      _ = r⁻¹ * (conj (z - 1) * (w - z)).re := by
        simp only [charbonnierDisplacementGradient, map_mul, Complex.conj_ofReal,
          mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rfl
      _ = _ := by rw [hdiff, div_eq_mul_inv]; ring
  have hbound : ((conj (z - 1) * (w - 1)).re - ‖z - 1‖ ^ 2) / r ≤ q - r := by
    apply (div_le_iff₀ hr).mpr
    have hcs := augmented_cauchy tau z w
    change tau ^ 2 + (conj (z - 1) * (w - 1)).re ≤ r * q at hcs
    nlinarith
  change r - tau + _ ≤ q - tau
  rw [hgrad]
  linarith

/-- The global supporting field is continuous for positive smoothing. -/
theorem continuous_charbonnierDisplacementGradient (tau : ℝ) (htau : 0 < tau) :
    Continuous (charbonnierDisplacementGradient tau) := by
  have hr : Continuous (fun z : ℂ => Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2)) := by fun_prop
  exact (Complex.continuous_ofReal.comp
    (hr.inv₀ fun z => (charbonnier_radius_pos tau htau z).ne')).mul
      (continuous_id.sub continuous_const)

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- First variation of the actual normal Charbonnier spectral trace.
Spectral collisions and zero displacement require no exceptions. -/
theorem hasDerivAt_re_trace_cfc_charbonnier
    (tau : ℝ) (htau : 0 < tau) (s : Set ℂ) (hs : IsCompact s)
    (a : ℝ → E →L[ℂ] E) (x : ℝ) (a' : E →L[ℂ] E)
    (ha : HasDerivAt a a' x) (hnormal : ∀ t, IsStarNormal (a t))
    (hspectrum : ∀ t, spectrum ℂ (a t) ⊆ s) :
    HasDerivAt
      (fun t => (LinearMap.trace ℂ E
        (cfc (fun z => (charbonnierDisplacementSymbol tau z : ℂ)) (a t)).toLinearMap).re)
      (LinearMap.trace ℂ E
        ((cfc (charbonnierDisplacementGradient tau) (a x)).adjoint * a').toLinearMap).re x :=
  hasDerivAt_re_trace_cfc (charbonnierDisplacementSymbol tau)
    (charbonnierDisplacementGradient tau) s hs
    (continuous_charbonnierDisplacementGradient tau htau).continuousOn
    (fun z _ w _ => charbonnierDisplacement_support tau htau z w)
    a x a' ha hnormal hspectrum

end ContinuousLinearMap

end TauCeti
