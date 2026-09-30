/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI GPT-5.6 Sol, Jon Crall
-/
import DavisKahan.Sources.DavisKahan1970.Section4Examples
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Instances

/-!
# Low-dimensional Section 4 surface facts

This module records the part of the low-dimensional analysis that is already
forced by the explicit Section 4.1 plane model.

In real two-space, once the source and target subspaces are distinct lines, the
only orthogonal competitors are the canonical direct rotation and the line-
exchanging reflection.  The direct rotation displacement has singular values
`(2 sin (θ/2), 2 sin (θ/2))`, while the reflection displacement has singular
values `(2, 0)`.  Therefore, on the short-angle range `θ ≤ π/3`, the direct
rotation is weakly majorized by the reflection and hence is no larger in every
unitarily invariant seminorm.

This formalizes the "no two-dimensional counterexample" part of the
low-dimensional discussion around Proposition 4.4.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section4LowDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)
open Section4Examples

noncomputable section

/-- The Ky Fan one-sum of Example 4.1's direct rotation is its common chord
singular value `2 sin (θ/2)`. -/
theorem example4_1_directRotation_kyFan_one
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    TauCeti.kyFanSum 1 (LinearMap.id - example41DirectRotation theta) =
      2 * Real.sin (theta / 2) := by
  rw [TauCeti.kyFanSum_eq_sum_fin, Fin.sum_univ_one,
    example4_1_directRotation_singularValues h0 hpi]
  simp

/-- The Ky Fan one-sum of Example 4.1's reflection is `2`. -/
theorem example4_1_reflection_kyFan_one (theta : ℝ) :
    TauCeti.kyFanSum 1 (LinearMap.id - example41Reflection theta) = 2 := by
  rw [TauCeti.kyFanSum_eq_sum_fin, Fin.sum_univ_one,
    example4_1_reflection_singularValues]
  simp

private theorem sin_half_le_one_half_of_le_pi_div_three
    {theta : ℝ} (h0 : 0 ≤ theta) (hθ : theta ≤ Real.pi / 3) :
    Real.sin (theta / 2) ≤ 1 / 2 := by
  have hsin : Real.sin (theta / 2) ≤ Real.sin (Real.pi / 6) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
    · linarith
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  rw [Real.sin_pi_div_six] at hsin
  simpa using hsin

/-- On the short-angle range `θ ≤ π/3`, the direct-rotation displacement of
Example 4.1 is weakly majorized by the reflecting competitor and therefore is
smaller in every square unitarily invariant seminorm. -/
theorem example4_1_directRotation_uiNorm_le_reflection_of_le_pi_div_three
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2)
    (hθ : theta ≤ Real.pi / 3)
    (N : UnitarilyInvariantSeminorm ℝ RealPlane RealPlane) :
    N (LinearMap.id - example41DirectRotation theta) ≤
      N (LinearMap.id - example41Reflection theta) := by
  have hfinrank : finrank ℝ RealPlane = 2 := by
    simp [RealPlane]
  have hky :
      ∀ k,
        TauCeti.kyFanSum k (LinearMap.id - example41DirectRotation theta) ≤
          TauCeti.kyFanSum k (LinearMap.id - example41Reflection theta) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      simp [TauCeti.kyFanSum_eq_sum_fin]
    by_cases hk1 : k = 1
    · subst hk1
      rw [example4_1_directRotation_kyFan_one h0 hpi,
        example4_1_reflection_kyFan_one]
      have hhalf : Real.sin (theta / 2) ≤ 1 / 2 :=
        sin_half_le_one_half_of_le_pi_div_three h0 hθ
      nlinarith
    · have hk2 : 2 ≤ k := by omega
      have hfin : finrank ℝ RealPlane ≤ k := by simpa [hfinrank] using hk2
      rw [TauCeti.kyFanSum_eq_of_finrank_le hfin,
        TauCeti.kyFanSum_eq_of_finrank_le hfin, hfinrank]
      rw [example4_1_directRotation_kyFan_two h0 hpi,
        example4_1_reflection_kyFan_two]
      have hhalf : Real.sin (theta / 2) ≤ 1 / 2 :=
        sin_half_le_one_half_of_le_pi_div_three h0 hθ
      nlinarith
  exact (TauCeti.UnitarilyInvariantSeminorm.kyFanSum_le_iff_forall_seminorm).1 hky N

/-- Package the two plane competitors in Example 4.1.  `false` is the direct
rotation and `true` is the reflecting competitor. -/
def example4_1_competitor (theta : ℝ) (flip : Bool) : RealPlane →ₗ[ℝ] RealPlane :=
  cond flip (example41Reflection theta) (example41DirectRotation theta)

/-- **No two-dimensional real counterexample in the Example 4.1 model.**
Up to the two orthogonal plane competitors (direct rotation or reflection), the
canonical direct rotation is minimal for every square unitarily invariant
seminorm throughout the source-valid range `θ ≤ π/3`. -/
theorem example4_1_directRotation_uiNorm_minimal_of_le_pi_div_three
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2)
    (hθ : theta ≤ Real.pi / 3)
    (flip : Bool)
    (N : UnitarilyInvariantSeminorm ℝ RealPlane RealPlane) :
    N (LinearMap.id - example41DirectRotation theta) ≤
      N (LinearMap.id - example4_1_competitor theta flip) := by
  cases flip
  · change N (LinearMap.id - example41DirectRotation theta) ≤
      N (LinearMap.id - example41DirectRotation theta)
    exact le_rfl
  · change N (LinearMap.id - example41DirectRotation theta) ≤
      N (LinearMap.id - example41Reflection theta)
    exact example4_1_directRotation_uiNorm_le_reflection_of_le_pi_div_three
      h0 hpi hθ N

end
end Section4LowDimensional
end DavisKahan1970
end TauCeti
