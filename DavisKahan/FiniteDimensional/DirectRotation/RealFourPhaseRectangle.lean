/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Order.Compact

/-!
# The monotone phase-rectangle reduction for real two-angle transport

Every point of the orthogonal positive-determinant phase rectangle is
dominated by a point on the single edge `(h,delta)`, `d ≤ delta ≤ h`.
The construction uses `delta = max d (h - |x-y|)` after reflecting both
coordinates when their sum exceeds `π`. Thus the proof works for any
nondecreasing phase penalty, including flat penalties and endpoint angles.

This is the scalar optimization step of the unrestricted four-dimensional
formula. It does not assume convexity or differentiability of a penalty.
-/

public section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

private theorem exists_edge_dominating_of_sum_le_pi
    (phi : ℝ → ℝ) (hphi : MonotoneOn phi (Set.Icc 0 Real.pi))
    (h d x y : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hh : h ≤ Real.pi / 2)
    (hx : h ≤ x) (hy : d ≤ y) (hxy : x + y ≤ Real.pi) :
    ∃ delta ∈ Set.Icc d h,
      phi (h + delta) + phi (h - delta) ≤ phi (x + y) + phi |x - y| := by
  let delta := max d (h - |x - y|)
  have hh0 : 0 ≤ h := hd.trans hdh
  have hx0 : 0 ≤ x := hh0.trans hx
  have hy0 : 0 ≤ y := hd.trans hy
  have hdelta₁ : d ≤ delta := le_max_left _ _
  have hdelta₂ : delta ≤ h := max_le hdh (sub_le_self _ (abs_nonneg _))
  have hsum : h + delta ≤ x + y := by
    have habs : h - |x - y| ≤ x + y - h := by
      rcases le_total x y with hle | hle
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        linarith
    have : delta ≤ x + y - h := max_le (by linarith) habs
    linarith
  have hdiff : h - delta ≤ |x - y| := by
    have := le_max_right d (h - |x - y|)
    change h - |x - y| ≤ delta at this
    linarith
  have habs : |x - y| ≤ x + y := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨delta, ⟨hdelta₁, hdelta₂⟩, add_le_add ?_ ?_⟩
  · exact hphi ⟨by linarith, by linarith⟩ ⟨by linarith, hxy⟩ hsum
  · exact hphi ⟨by linarith, by linarith⟩
      ⟨abs_nonneg _, habs.trans hxy⟩ hdiff

/-- Every folded phase-rectangle cost is bounded below by an edge cost.
This is a pointwise domination statement for arbitrary nondecreasing
penalties, stronger than an equality of infima. -/
theorem exists_edge_dominating_phase_rectangle
    (phi : ℝ → ℝ) (hphi : MonotoneOn phi (Set.Icc 0 Real.pi))
    (h d x y : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hh : h ≤ Real.pi / 2)
    (hx : x ∈ Set.Icc h (Real.pi - h))
    (hy : y ∈ Set.Icc d (Real.pi - d)) :
    ∃ delta ∈ Set.Icc d h,
      phi (h + delta) + phi (h - delta) ≤
        phi (min (x + y) (2 * Real.pi - x - y)) + phi |x - y| := by
  by_cases hxy : x + y ≤ Real.pi
  · rw [min_eq_left (by linarith : x + y ≤ 2 * Real.pi - x - y)]
    exact exists_edge_dominating_of_sum_le_pi phi hphi h d x y hd hdh hh hx.1 hy.1 hxy
  · obtain ⟨delta, hdelta, hcost⟩ := exists_edge_dominating_of_sum_le_pi
      phi hphi h d (Real.pi - x) (Real.pi - y) hd hdh hh
      (by linarith [hx.2]) (by linarith [hy.2]) (by linarith)
    refine ⟨delta, hdelta, ?_⟩
    rw [min_eq_right (by linarith : 2 * Real.pi - x - y ≤ x + y)]
    have hsum : (Real.pi - x) + (Real.pi - y) = 2 * Real.pi - x - y := by ring
    have hdiff : |(Real.pi - x) - (Real.pi - y)| = |x - y| := by
      rw [show (Real.pi - x) - (Real.pi - y) = y - x by ring, abs_sub_comm]
    simpa only [hsum, hdiff] using hcost

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
