/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Continuous factorization at two equal function values

If a scalar function has equal values at two distinct points and is
differentiable there, subtracting that value factors as the product of the
two linear factors and a continuous divided difference. Only continuity is
required at the other points of the specified set.

The construction uses two applications of Mathlib's `dslope`. It provides
the removable factor used to differentiate the continuous functional
calculus at a normal element with two-point spectrum.
-/

public section

open scoped Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A function with equal values at two distinct differentiability points
has a continuous quadratic factor, with the expected removable values. -/
theorem exists_continuousOn_two_point_factor
    (f : 𝕜 → 𝕜) (s : Set 𝕜) (a b c : 𝕜) (hab : a ≠ b)
    (hfa : f a = c) (hfb : f b = c) (hf : ContinuousOn f s)
    (hda : DifferentiableAt 𝕜 f a) (hdb : DifferentiableAt 𝕜 f b) :
    ∃ k : 𝕜 → 𝕜, ContinuousOn k s ∧
      (∀ z, f z = c + (z - a) * (z - b) * k z) ∧
      k a = deriv f a / (a - b) ∧ k b = deriv f b / (b - a) := by
  let g := dslope f a
  let k := dslope g b
  have hgb : g b = 0 := by
    rw [show g b = dslope f a b from rfl, dslope_of_ne f hab.symm, slope_def_field,
      hfa, hfb, sub_self, zero_div]
  have hg : ContinuousOn g s := by
    intro z hz
    by_cases hza : z = a
    · subst z
      exact (continuousAt_dslope_same.2 hda).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne hza).2 (hf z hz)
  have hdgb : DifferentiableAt 𝕜 g b := (differentiableAt_dslope_of_ne hab.symm).2 hdb
  have hk : ContinuousOn k s := by
    intro z hz
    by_cases hzb : z = b
    · subst z
      exact (continuousAt_dslope_same.2 hdgb).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne hzb).2 (hg z hz)
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · intro z
    have hgfac : (z - a) * g z = f z - c := by
      simpa only [smul_eq_mul, hfa] using sub_smul_dslope f a z
    have hkfac : (z - b) * k z = g z := by
      simpa only [smul_eq_mul, hgb, sub_zero] using sub_smul_dslope g b z
    calc
      f z = c + (z - a) * g z := by rw [hgfac]; ring
      _ = c + (z - a) * (z - b) * k z := by rw [← hkfac]; ring
  · change dslope g b a = deriv f a / (a - b)
    rw [dslope_of_ne g hab, slope_def_field, hgb, sub_zero]
    change dslope f a a / (a - b) = deriv f a / (a - b)
    rw [dslope_same]
  · change dslope g b b = deriv f b / (b - a)
    rw [dslope_same]
    have hd := (hdb.hasDerivAt.sub_const (f a)).div
      ((hasDerivAt_id b).sub_const a) (sub_ne_zero.2 hab.symm)
    have hcoeff : (deriv f b * (b - a) - (f b - f a) * 1) / (b - a) ^ 2 =
        deriv f b / (b - a) := by
      rw [hfa, hfb, sub_self, zero_mul, sub_zero]
      field_simp
    have hevent : g =ᶠ[𝓝 b] (fun z => (f z - f a) / (z - a)) :=
      (dslope_eventuallyEq_slope_of_ne f hab.symm).mono (fun z hz => by
        simpa only [slope_def_field] using hz)
    exact ((hd.congr_deriv hcoeff).congr_of_eventuallyEq hevent).deriv

end TauCeti
