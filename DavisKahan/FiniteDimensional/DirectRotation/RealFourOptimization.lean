/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourPositive

/-!
# Exact optimization in the real four-dimensional cosine--sine model

The full positive fiber is dominated by the scalar edge, and every edge
point is attained by a common real source/complement rotation. Compactness
of that interval gives an attaining positive-class minimum. Combining it
with the exact negative class gives the unrestricted ambient minimum.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix

/-- A spectral penalty evaluated on the displacement chord. -/
@[expose] def fourPhasePenalty (rho : ℝ → ℝ) (t : ℝ) : ℝ :=
  rho (Real.sqrt (2 - 2 * Real.cos t))

/-- The paired edge cost; its admissible parameter interval is `[d,h]`. -/
@[expose] def fourEdgeCost (rho : ℝ → ℝ) (h delta : ℝ) : ℝ :=
  2 * (fourPhasePenalty rho (h+delta) + fourPhasePenalty rho (h-delta))

theorem sqrt_displacement_chord_mem (t : ℝ) :
    Real.sqrt (2 - 2 * Real.cos t) ∈ Set.Icc 0 2 := by
  have hrad : 0 ≤ 2 - 2 * Real.cos t := by linarith [Real.cos_le_one t]
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (2 - 2 * Real.cos t), Real.neg_one_le_cos t]

/-- The chord expression agrees with the half-angle convention used for
principal angles. -/
theorem sqrt_displacement_chord_eq_two_sin_half (t : ℝ) (ht : t ∈ Set.Icc 0 Real.pi) :
    Real.sqrt (2 - 2 * Real.cos t) = 2 * Real.sin (t/2) := by
  have hs : 0 ≤ Real.sin (t/2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hcos : Real.cos t = 1 - 2*Real.sin (t/2)^2 := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      Real.cos_two_mul_eq_one_sub (t/2)
  rw [hcos, show 2-2*(1-2*Real.sin (t/2)^2) = (2*Real.sin (t/2))^2 by ring,
    Real.sqrt_sq (by positivity)]

theorem fourPhasePenalty_monotoneOn (rho : ℝ → ℝ)
    (hrho : MonotoneOn rho (Set.Icc 0 2)) :
    MonotoneOn (fourPhasePenalty rho) (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  exact hrho (sqrt_displacement_chord_mem x) (sqrt_displacement_chord_mem y)
    (Real.sqrt_le_sqrt (by
      linarith [Real.cos_le_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy]))

private theorem phase_rectangle_cost_dominated_by_edge
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2))
    (h d x y : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hh : h ≤ Real.pi / 2)
    (hx : x ∈ Set.Icc h (Real.pi-h)) (hy : y ∈ Set.Icc d (Real.pi-d)) :
    ∃ delta ∈ Set.Icc d h, fourEdgeCost rho h delta ≤
      2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
        2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  obtain ⟨delta, hdelta, hcost⟩ := exists_edge_dominating_phase_rectangle
    (fourPhasePenalty rho) (fourPhasePenalty_monotoneOn rho hrho) h d x y hd hdh hh hx hy
  have hfold : fourPhasePenalty rho (min (x+y) (2*Real.pi-x-y)) =
      fourPhasePenalty rho (x+y) := by
    by_cases hxy : x+y ≤ Real.pi
    · rw [min_eq_left (by linarith : x+y ≤ 2*Real.pi-x-y)]
    · rw [min_eq_right (by linarith : 2*Real.pi-x-y ≤ x+y)]
      simp only [fourPhasePenalty, show 2*Real.pi-x-y = 2*Real.pi-(x+y) by ring,
        Real.cos_two_pi_sub]
  have habs : fourPhasePenalty rho |x-y| = fourPhasePenalty rho (x-y) := by
    simp only [fourPhasePenalty, Real.cos_abs]
  rw [hfold, habs] at hcost
  refine ⟨delta, hdelta, ?_⟩
  change 2*(fourPhasePenalty rho (h+delta)+fourPhasePenalty rho (h-delta)) ≤
    2*fourPhasePenalty rho (x+y)+2*fourPhasePenalty rho (x-y)
  linarith

/-- Every ambient positive-determinant transporter is dominated by an
actual scalar edge cost. This covers both positive source/complement
components, without assuming independent principal-plane optimization. -/
theorem four_positive_transport_dominated_by_edge
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2))
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1) (hdet : W.det = 1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation ![h+d, h-d] * fourSourceProjection *
        (fourCSRotation ![h+d, h-d]).transpose) :
    ∃ delta ∈ Set.Icc d h, fourEdgeCost rho h delta ≤ fourDisplacementCost rho W := by
  obtain ⟨a, b, e, f, he, hf, hform⟩ := exists_fourTransport_of_mem_fiber ![h+d, h-d] W hW htrans
  have hef : e*f = 1 := by simpa only [hform, det_fourTransport] using hdet
  have hf' : f = e := by rcases he with rfl | rfl <;> linarith
  subst f
  let r := (a+b)/2
  let s := (a-b)/2
  have ha : r+s = a := by dsimp [r, s]; ring
  have hb : r-s = b := by dsimp [r, s]; ring
  have hform' : W = fourTransport ![h+d, h-d] (r+s) (r-s) e e := by
    rw [ha, hb]
    exact hform
  have hphase : ∃ x ∈ Set.Icc h (Real.pi-h), ∃ y ∈ Set.Icc d (Real.pi-d),
      fourDisplacementCost rho W = 2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
        2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
    rcases he with rfl | rfl
    · obtain ⟨x, hx, y, hy, _, _, hcost⟩ := exists_fourTransport_rotations_phase_rectangle
        h d r s hd hdh (by linarith) rho
      exact ⟨x, hx, y, hy, by rw [hform']; exact hcost⟩
    · obtain ⟨x, hx, y, hy, _, _, hcost⟩ := exists_fourTransport_reflections_phase_rectangle
        h d r s hd hdh hhd rho
      exact ⟨x, hx, y, hy, by rw [hform']; exact hcost⟩
  obtain ⟨x, hx, y, hy, hcost⟩ := hphase
  rw [hcost]
  exact phase_rectangle_cost_dominated_by_edge rho hrho h d x y hd hdh (by linarith) hx hy

/-- Every edge cost is attained by a common rotation within source and
complement. The angle uses `acos(cos(delta)/cos(d))`; `cos(d)>0` follows
from the ordered principal-angle constraints, including the right endpoint. -/
theorem exists_four_positive_transport_attaining_edge
    (h d delta : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2)
    (hdelta : delta ∈ Set.Icc d h) (rho : ℝ → ℝ) :
    ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
      W.transpose * W = 1 ∧ W.det = 1 ∧
      W * fourSourceProjection * W.transpose =
        fourCSRotation ![h+d, h-d] * fourSourceProjection *
          (fourCSRotation ![h+d, h-d]).transpose ∧
      fourDisplacementCost rho W = fourEdgeCost rho h delta := by
  have hdpi : d < Real.pi/2 := by linarith [Real.pi_pos]
  have hden : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hdpi⟩
  have hdc : Real.cos delta ≤ Real.cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hd (by linarith [Real.pi_pos, hdelta.2]) hdelta.1
  have hdelc : 0 ≤ Real.cos delta := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, hdelta.1], by linarith [hdelta.2]⟩
  let gamma := Real.arccos (Real.cos delta / Real.cos d)
  have hgamma : Real.cos gamma = Real.cos delta / Real.cos d :=
    Real.cos_arccos (by have := div_nonneg hdelc hden.le; linarith)
      ((div_le_one hden).mpr hdc)
  have hphase : Real.cos delta = Real.cos d * Real.cos gamma := by
    rw [hgamma]
    field_simp
  let W := fourTransport ![h+d, h-d] gamma gamma 1 1
  have hmem := fourTransport_mem_fiber ![h+d, h-d] gamma gamma 1 1 (by norm_num) (by norm_num)
  refine ⟨W, hmem.1, by simp [W], hmem.2, ?_⟩
  have hcost := fourTransport_rotations_cost_of_phase_cosines h d gamma 0 h delta
    (by simp) hphase rho
  simp only [add_zero, sub_zero] at hcost
  rw [show fourDisplacementCost rho W = _ from hcost]
  simp only [fourEdgeCost, fourPhasePenalty]
  ring

/-- The scalar edge minimum is attained and equals the minimum over the
entire positive-determinant fiber. The penalty needs only continuity and
monotonicity on its actual singular-value interval `[0,2]`. -/
theorem exists_minimizing_four_positive_transport
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2))
    (hcont : ContinuousOn rho (Set.Icc 0 2)) :
    ∃ delta ∈ Set.Icc d h, IsMinOn (fourEdgeCost rho h) (Set.Icc d h) delta ∧
      ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
        W.transpose * W = 1 ∧ W.det = 1 ∧
        W * fourSourceProjection * W.transpose =
          fourCSRotation ![h+d, h-d] * fourSourceProjection *
            (fourCSRotation ![h+d, h-d]).transpose ∧
        fourDisplacementCost rho W = fourEdgeCost rho h delta ∧
        IsMinOn (fourDisplacementCost rho)
          {X | X.transpose * X = 1 ∧ X.det = 1 ∧
            X * fourSourceProjection * X.transpose =
              fourCSRotation ![h+d, h-d] * fourSourceProjection *
                (fourCSRotation ![h+d, h-d]).transpose} W := by
  have hphi : Continuous (fourPhasePenalty rho) := by
    apply continuousOn_univ.mp
    exact hcont.comp
      (Real.continuous_sqrt.comp (continuous_const.sub
        (continuous_const.mul Real.continuous_cos))).continuousOn
      (fun t _ => sqrt_displacement_chord_mem t)
  have hedge : Continuous (fourEdgeCost rho h) :=
    continuous_const.mul ((hphi.comp (continuous_const.add continuous_id)).add
      (hphi.comp (continuous_const.sub continuous_id)))
  obtain ⟨delta, hdelta, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc d h)).exists_isMinOn
    ⟨d, ⟨le_rfl, hdh⟩⟩ hedge.continuousOn
  obtain ⟨W, hW, hdet, htrans, hcost⟩ :=
    exists_four_positive_transport_attaining_edge h d delta hd hdh hhd hdelta rho
  refine ⟨delta, hdelta, hmin, W, hW, hdet, htrans, hcost, ?_⟩
  intro X hX
  obtain ⟨eta, heta, hbound⟩ := four_positive_transport_dominated_by_edge
    h d hd hdh hhd rho hrho X hX.1 hX.2.1 hX.2.2
  rw [hcost]
  exact (hmin heta).trans hbound

/-- The unrestricted real four-dimensional transport minimum. The scalar
edge minimizer is supplied with its exact interval and minimality proof;
the ambient attaining matrix and comparison include both determinant
classes and all mixing competitors. Zero, equal and right angles are
included. Only continuity and monotonicity on `[0,2]` are required. -/
theorem exists_minimizing_four_transport
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2))
    (hcont : ContinuousOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    ∃ delta ∈ Set.Icc d h, IsMinOn (fourEdgeCost rho h) (Set.Icc d h) delta ∧
      ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
        W.transpose * W = 1 ∧
        W * fourSourceProjection * W.transpose =
          fourCSRotation ![h+d, h-d] * fourSourceProjection *
            (fourCSRotation ![h+d, h-d]).transpose ∧
        fourDisplacementCost rho W = min (fourEdgeCost rho h delta)
          (rho 2 + 2*fourPhasePenalty rho (h-d)) ∧
        IsMinOn (fourDisplacementCost rho)
          {X | X.transpose * X = 1 ∧
            X * fourSourceProjection * X.transpose =
              fourCSRotation ![h+d, h-d] * fourSourceProjection *
                (fourCSRotation ![h+d, h-d]).transpose} W := by
  obtain ⟨delta, hdelta, hscalar, Wp, hWp, hdetp, htransp, hcostp, hminp⟩ :=
    exists_minimizing_four_positive_transport h d hd hdh hhd rho hrho hcont
  obtain ⟨Wn, hWn, hdetn, htransn, hcostn, hminn⟩ :=
    exists_minimizing_four_negative_transport (h+d) (h-d)
      (by linarith) (by linarith) hhd rho hrho hzero
  let posval := fourEdgeCost rho h delta
  let negval := rho 2 + 2*fourPhasePenalty rho (h-d)
  have hpval : fourDisplacementCost rho Wp = posval := hcostp
  have hnval : fourDisplacementCost rho Wn = negval := hcostn
  have hlower (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
      (hX : X.transpose * X = 1 ∧
        X * fourSourceProjection * X.transpose =
          fourCSRotation ![h+d, h-d] * fourSourceProjection *
            (fourCSRotation ![h+d, h-d]).transpose) :
      min posval negval ≤ fourDisplacementCost rho X := by
    have hsq : X.det ^ 2 = 1 := by
      have hdet := congrArg Matrix.det hX.1
      simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using hdet
    rcases mul_eq_zero.mp (show (X.det-1)*(X.det+1)=0 by nlinarith [hsq]) with hp | hn
    · have hXdet : X.det = 1 := by linarith
      have hbound := hminp ⟨hX.1, hXdet, hX.2⟩
      rw [hpval] at hbound
      exact (min_le_left _ _).trans hbound
    · have hXdet : X.det = -1 := by linarith
      have hbound := hminn ⟨hX.1, hXdet, hX.2⟩
      rw [hnval] at hbound
      exact (min_le_right _ _).trans hbound
  by_cases hp : posval ≤ negval
  · have hvalue : fourDisplacementCost rho Wp = min posval negval :=
      hpval.trans (min_eq_left hp).symm
    refine ⟨delta, hdelta, hscalar, Wp, hWp, htransp, hvalue, ?_⟩
    intro X hX
    rw [hvalue]
    exact hlower X hX
  · have hvalue : fourDisplacementCost rho Wn = min posval negval :=
      hnval.trans (min_eq_right (le_of_not_ge hp)).symm
    refine ⟨delta, hdelta, hscalar, Wn, hWn, htransn, hvalue, ?_⟩
    intro X hX
    rw [hvalue]
    exact hlower X hX

/-- The nuclear edge minimum is at the endpoint `delta=h`, including
zero and right angles. -/
theorem four_nuclear_edge_minimum
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    fourEdgeCost id h h = 4*Real.sin h ∧
      IsMinOn (fourEdgeCost id h) (Set.Icc d h) h := by
  have hformula (delta : ℝ) (hdelta : delta ∈ Set.Icc d h) :
      fourEdgeCost id h delta = 8*Real.sin (h/2)*Real.cos (delta/2) := by
    rw [fourEdgeCost, fourPhasePenalty, fourPhasePenalty, id_eq, id_eq,
      sqrt_displacement_chord_eq_two_sin_half _ ⟨by linarith [hdelta.1], by linarith [hdelta.2]⟩,
      sqrt_displacement_chord_eq_two_sin_half _ ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩]
    rw [show (h+delta)/2 = h/2+delta/2 by ring,
      show (h-delta)/2 = h/2-delta/2 by ring, Real.sin_add, Real.sin_sub]
    ring
  have hvalue : fourEdgeCost id h h = 4*Real.sin h := by
    rw [hformula h ⟨hdh, le_rfl⟩]
    have hh : Real.sin h = 2*Real.sin (h/2)*Real.cos (h/2) := by
      simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using Real.sin_two_mul (h/2)
    rw [hh]
    ring
  refine ⟨hvalue, ?_⟩
  intro delta hdelta
  change fourEdgeCost id h h ≤ fourEdgeCost id h delta
  rw [hformula h ⟨hdh, le_rfl⟩, hformula delta hdelta]
  apply mul_le_mul_of_nonneg_left
    (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hdelta.1]) (by linarith [Real.pi_pos])
      (by linarith [hdelta.2]))
  exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_pos]))

/-- Closed nuclear-cost formula for all ambient orthogonal transports in
the two-angle model. Unlike the repeated-angle witness, this includes
unequal principal-angle parameters and both determinant classes. -/
theorem exists_minimizing_four_nuclear_transport
    (h d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
      W.transpose * W = 1 ∧
      W * fourSourceProjection * W.transpose =
        fourCSRotation ![h+d, h-d] * fourSourceProjection *
          (fourCSRotation ![h+d, h-d]).transpose ∧
      fourDisplacementCost id W = min (4*Real.sin h) (2+4*Real.sin ((h-d)/2)) ∧
      IsMinOn (fourDisplacementCost id)
        {X | X.transpose * X = 1 ∧
          X * fourSourceProjection * X.transpose =
            fourCSRotation ![h+d, h-d] * fourSourceProjection *
              (fourCSRotation ![h+d, h-d]).transpose} W := by
  obtain ⟨delta, hdelta, hscalar, W, hW, htrans, hcost, hmin⟩ :=
    exists_minimizing_four_transport h d hd hdh hhd id (fun _ _ _ _ hxy => hxy)
      continuous_id.continuousOn rfl
  obtain ⟨hvalue, hedge⟩ := four_nuclear_edge_minimum h d hd hdh hhd
  have hscalarval : fourEdgeCost id h delta = 4*Real.sin h := by
    apply le_antisymm
    · rw [← hvalue]
      exact hscalar ⟨hdh, le_rfl⟩
    · rw [← hvalue]
      exact hedge hdelta
  refine ⟨W, hW, htrans, ?_, hmin⟩
  rw [hcost, hscalarval, fourPhasePenalty, id_eq,
    sqrt_displacement_chord_eq_two_sin_half _ ⟨by linarith, by linarith [Real.pi_pos]⟩]
  simp only [id_eq]
  congr 1
  ring

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
