/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourPrincipalAngles

/-!
# The sharp real nuclear canonical region in dimension four

Coupling improves the canonical nuclear cost whenever both principal
angles are positive. When only one is positive, the exact remaining
canonical/reflection threshold is pi/3. Both endpoints are included.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

/-- The canonical nuclear phase is the left endpoint of `[d,h]`. It is
minimizing exactly when the interval degenerates. -/
theorem four_nuclear_edge_left_isMinOn_iff
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    IsMinOn (fourEdgeCost id h) (Set.Icc d h) d ↔ d = h := by
  constructor
  · intro hmin
    by_contra hne
    have hlt : d < h := lt_of_le_of_ne hdh hne
    have hs : 0 < Real.sin (h/2) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by linarith [Real.pi_pos])
    have hc : Real.cos (h/2) < Real.cos (d/2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
        (by linarith)
    have hcost := hmin ⟨hdh, le_rfl⟩
    change fourEdgeCost id h d ≤ fourEdgeCost id h h at hcost
    rw [four_nuclear_edgeCost h d (by linarith) ⟨hd, hdh⟩,
      four_nuclear_edgeCost h h (by linarith) ⟨by linarith, le_rfl⟩] at hcost
    exact (not_lt_of_ge hcost) (mul_lt_mul_of_pos_left hc (by positivity))
  · intro heq
    subst d
    intro delta hdelta
    have heq : delta = h := le_antisymm hdelta.2 hdelta.1
    change fourEdgeCost id h h ≤ fourEdgeCost id h delta
    rw [heq]

/-- Exact all-ambient real nuclear canonical criterion. At most one angle
may be positive, and its value must not exceed `pi/3`. -/
theorem fourCSRotation_nuclear_isMinOn_iff
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    IsMinOn (fourDisplacementCost id)
      {X | X.transpose * X = 1 ∧
        X * fourSourceProjection * X.transpose =
          fourCSRotation ![h+d, h-d] * fourSourceProjection *
            (fourCSRotation ![h+d, h-d]).transpose}
      (fourCSRotation ![h+d, h-d]) ↔
      h-d = 0 ∧ h+d ≤ Real.pi / 3 := by
  rw [fourCSRotation_isMinOn_iff h d hd hdh hhd id
    (fun _ _ _ _ hxy => hxy) continuous_id.continuousOn rfl,
    four_nuclear_edge_left_isMinOn_iff h d hd hdh hhd]
  have hphase : fourPhasePenalty id (h+d) = 2*Real.sin ((h+d)/2) := by
    exact sqrt_displacement_chord_eq_two_sin_half _
      ⟨by linarith, by linarith [Real.pi_pos]⟩
  rw [hphase]
  simp only [id_eq]
  have hsin : Real.sin ((h+d)/2) ≤ (1 : ℝ)/2 ↔ (h+d)/2 ≤ Real.pi/6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  constructor
  · rintro ⟨heq, hcost⟩
    exact ⟨by linarith, by have := hsin.mp (by linarith); linarith⟩
  · rintro ⟨heq, hbound⟩
    exact ⟨by linarith, by have := hsin.mpr (by linarith); linarith⟩

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
