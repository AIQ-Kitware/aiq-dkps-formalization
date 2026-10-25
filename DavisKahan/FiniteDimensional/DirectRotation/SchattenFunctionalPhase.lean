/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimalPhase
public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
# The intrinsic optimal Schatten phase factor

Finite functional calculus defines the positive scalar phase as a function
of the actual principal cosine operator. The symbol has unit modulus on
the entire complex plane; hence its finite normal functional calculus is
unitary. No continuity or infinite-dimensional ideal assertion is needed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The positive attaining scalar phase as a function of a cosine. -/
def schattenPhaseSymbol (p : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((optimalPhase p (Real.arccos z.re) : ℂ) * Complex.I)

/-- The positive spectral phase factor, defined without choosing a frame. -/
@[expose]
def schattenPhaseFactor (p : ℝ) (C : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (schattenPhaseSymbol p) C

/-- The factor is unitary for every finite normal operator, including
spectra outside the principal-cosine interval. -/
theorem schattenPhaseFactor_mem_unitary (p : ℝ) (C : E →L[ℂ] E) (hC : IsStarNormal C) :
    schattenPhaseFactor p C ∈ unitary (E →L[ℂ] E) := by
  apply (cfc_unitary_iff (schattenPhaseSymbol p) C hC
    ((C.finite_spectrum ℂ).continuousOn _)).mpr
  intro z _
  change conj (Complex.exp _) * Complex.exp _ = 1
  rw [RCLike.conj_mul, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- The factor has the named optimal phase on each physical cosine
eigenvector, including the zero and right-angle endpoints. -/
theorem schattenPhaseFactor_apply_cos (p theta : ℝ)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E)
    (hθ : theta ∈ Set.Icc 0 Real.pi)
    (hx : C x = (Real.cos theta : ℂ) • x) :
    schattenPhaseFactor p C x =
      Complex.exp ((optimalPhase p theta : ℂ) * Complex.I) • x := by
  rw [schattenPhaseFactor,
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal (schattenPhaseSymbol p) hx]
  simp only [schattenPhaseSymbol, Complex.ofReal_re, Real.arccos_cos hθ.1 hθ.2]

/-- The adjoint has the opposite scalar phase on the same cosine space. -/
theorem schattenPhaseFactor_star_apply_cos (p theta : ℝ)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E)
    (hθ : theta ∈ Set.Icc 0 Real.pi)
    (hx : C x = (Real.cos theta : ℂ) • x) :
    star (schattenPhaseFactor p C) x =
      Complex.exp (((-optimalPhase p theta : ℝ) : ℂ) * Complex.I) • x := by
  have h := unitary_star_apply_of_apply_eq_smul
    (⟨schattenPhaseFactor p C, schattenPhaseFactor_mem_unitary p C inferInstance⟩ :
      unitary (E →L[ℂ] E)) _ (Complex.norm_exp_ofReal_mul_I (optimalPhase p theta)) x
    (schattenPhaseFactor_apply_cos p theta C x hθ hx)
  have hs : star (Complex.exp ((optimalPhase p theta : ℂ) * Complex.I)) =
      Complex.exp (((-optimalPhase p theta : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    simp
  simpa only [hs] using h

/-- Cosine-one vectors are fixed, for every scalar exponent at least one. -/
theorem schattenPhaseFactor_apply_one (p : ℝ) (hp : 1 ≤ p)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hx : C x = x) :
    schattenPhaseFactor p C x = x := by
  have h := schattenPhaseFactor_apply_cos p 0 C x
    ⟨le_rfl, Real.pi_pos.le⟩ (by simpa only [Real.cos_zero, Complex.ofReal_one, one_smul] using hx)
  simpa only [optimalPhase_zero p hp, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] using h

/-- At a right angle the positive spectral factor acts by `i`. This
phase does not constrain the independent reflecting defect parameter. -/
theorem schattenPhaseFactor_apply_zero (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hx : C x = 0) :
    schattenPhaseFactor p C x = Complex.I • x := by
  have h := schattenPhaseFactor_apply_cos p (Real.pi / 2) C x
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    (by simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul] using hx)
  simpa only [optimalPhase_right_angle p hp1 hp2, Complex.exp_ofReal_mul_I,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one,
    one_mul, zero_add] using h

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
