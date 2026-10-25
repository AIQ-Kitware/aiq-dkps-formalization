/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SharpDisplacement

/-!
# Limiting sharpness of the uniform acute-pair displacement constant

The sharp bound `sqrt 2` is not attained at an acute angle, but no smaller
constant is valid on *all* acute pairs.  The quantitative four-dimensional
family supplies a witness at each angle, and a one-sided limit at `π/2`
identifies the limiting coefficient.  This theorem is stated in terms of the
witness's actual canonical rotation and globally optimal competitor; therefore
it implies the optimality of the uniform constant for arbitrary UI norms.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SmallAngleCounterexample

open scoped InnerProductSpace

/-- Any coefficient controlling the canonical trace displacement of the real
four-dimensional witness for *every* positive acute angle is at least `sqrt 2`.
Together with `uiNorm_directRotation_le_sqrt_two_mul_displacement`, this makes
`sqrt 2` the least common displacement factor on acute pairs. -/
theorem sqrt_two_common_factor_necessary (c : ℝ)
    (hbound : ∀ (theta : ℝ) (h0 : 0 < theta) (h1 : theta < Real.pi / 2),
      kyFanSum 4 (LinearMap.id -
        (directRotation ShortRotationCounterexample.U4 (V4 theta)
          (acute theta (cos_pos theta h0 h1))).toLinearMap) ≤
        c * kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap)) :
    Real.sqrt 2 ≤ c := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have hcont : Continuous (fun theta : ℝ => c * Real.cos (theta / 2)) := by
    fun_prop
  have hlim : Filter.Tendsto (fun theta : ℝ => c * Real.cos (theta / 2))
      (nhdsWithin (Real.pi / 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (nhds (c * Real.cos ((Real.pi / 2) / 2))) :=
    (hcont.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (Real.pi / 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo hpi.ne]
    exact ⟨hpi.le, le_refl _⟩
  have hwithin : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    self_mem_nhdsWithin
  have hevent : ∀ᶠ theta : ℝ in
      nhdsWithin (Real.pi / 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      (1 : ℝ) ≤ c * Real.cos (theta / 2) := by
    filter_upwards [hwithin] with theta htheta
    exact factor_necessary_at_fixedAngle theta c htheta.1 htheta.2
      (hbound theta htheta.1 htheta.2)
  have hlimBound : 1 ≤ c * Real.cos ((Real.pi / 2) / 2) :=
    ge_of_tendsto hlim hevent
  have hangle : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
  rw [hangle, Real.cos_pi_div_four] at hlimBound
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  by_contra hc
  have hlt : c < Real.sqrt 2 := lt_of_not_ge hc
  have hmul : c * Real.sqrt 2 < Real.sqrt 2 * Real.sqrt 2 :=
    mul_lt_mul_of_pos_right hlt hpos
  nlinarith [hs]

end SmallAngleCounterexample
end DavisKahan.FiniteDimensional
end TauCeti
